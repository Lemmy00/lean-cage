(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual scalar reader checks width before requesting
   stream bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess ReceiverAllocation CallAccess Readers.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayImport GatewaySource GatewayMachine GatewayContexts GatewayPure GatewayReturns
  GatewayCallPath GatewayFrames GatewayFunctionEntry GatewayWordData GatewayWordsMemory GatewayWordsMath GatewayReads GatewayWordReceipt GatewayStreamInterface GatewayReturnTypes GatewayReadonly GatewayReadonlyRuntime GatewayOperations.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Record gateway_word_arguments := {
  word_stream:Values.val;
  word_width:int;
  word_output:Values.val
}.
Definition gateway_word_values arguments :=
  [word_stream arguments;Vint(word_width arguments);word_output arguments].
Definition gateway_word_parameters arguments :=
  PTree.set _value(word_output arguments)(PTree.set _width(Vint(word_width arguments))
    (PTree.set _stream(word_stream arguments)(create_undef_temps(fn_temps f_host_word)))).
Definition gateway_word_environment buffer :=PTree.set _bytes(buffer,tarray tuchar 8)empty_env.

Definition gateway_word_read :=
  match fn_body f_host_word with
  |Ssequence(Ssequence(Sifthenelse _ _(Ssequence call _))_)_=>call
  |_=>Sskip end.
Definition gateway_word_read_bool :=Sset _t'1(Ecast(Etempvar _t'2 tint)tbool).
Definition gateway_word_failure :=
  Sreturn(Some(Eunop Oneg(Econst_int(Int.repr 1)tint)tint)).
Definition gateway_word_test :=Sifthenelse(Etempvar _t'1 tint)gateway_word_failure Sskip.
Definition gateway_word_after :=match fn_body f_host_word with Ssequence _ after=>after|_=>Sskip end.
Definition gateway_word_guard :=
  Ebinop Ogt(Etempvar _width tuint)(Esizeof(tarray tuchar 8)tulong)tint.
Definition gateway_word_check :=
  Sifthenelse gateway_word_guard(Sset _t'1(Econst_int(Int.repr 1)tint))
    (Ssequence gateway_word_read gateway_word_read_bool).

Lemma gateway_word_body_structure :fn_body f_host_word=
  Ssequence(Ssequence gateway_word_check gateway_word_test)gateway_word_after.
Proof. reflexivity. Qed.

Lemma gateway_word_function_entry ge before allocated buffer arguments :
  Mem.alloc before 0 8=(allocated,buffer) ->
  function_entry2 ge f_host_word(gateway_word_values arguments)before
    (gateway_word_environment buffer)(gateway_word_parameters arguments)allocated.
Proof.
  intro ALLOC;constructor.
  - repeat(apply list_norepet_cons;[cbn;intuition discriminate|]);apply list_norepet_nil.
  - repeat(apply list_norepet_cons;[cbn;intuition discriminate|]);apply list_norepet_nil.
  - unfold list_disjoint,var_names;cbn;intros first second LEFT RIGHT.
    repeat destruct LEFT as[LEFT|LEFT];try contradiction;subst first;
      repeat destruct RIGHT as[RIGHT|RIGHT];try contradiction;subst second;discriminate.
  - cbn[fn_vars];econstructor;[exact ALLOC|constructor].
  - reflexivity.
Qed.

Lemma gateway_actual_word_entry ge before arguments environment temporaries allocated :
  function_entry2 ge f_host_word(gateway_word_values arguments)before environment temporaries allocated ->
  exists buffer,environment=gateway_word_environment buffer /\
    temporaries=gateway_word_parameters arguments /\Mem.alloc before 0 8=(allocated,buffer) /\
    Mem.unchanged_on(fun _ _=>Logic.True)before allocated /\~Mem.valid_block before buffer /\
    Mem.range_perm allocated buffer 0 8 Cur Freeable.
Proof.
  intro ENTRY;destruct(Mem.alloc before 0 8)as[canonical buffer]eqn:ALLOC.
  destruct(function_entry_unique _ _ _ _ _ _ _ _ _ _
    (gateway_word_function_entry ge before canonical buffer arguments ALLOC)ENTRY)as[ENV[TEMPS MEMORY]].
  subst environment temporaries allocated.
  exists buffer;split;[reflexivity|]. split;[reflexivity|]. split;[reflexivity|].
  split;[eapply Mem.alloc_unchanged_on;exact ALLOC|].
  split;[eapply Mem.fresh_block_alloc;exact ALLOC|].
  intros position RANGE;eapply Mem.perm_alloc_2;eauto.
Qed.

Lemma gateway_word_guard_value ge environment temporaries memory width :
  temporaries!_width=Some(Vint width) ->
  expression_value ge environment temporaries memory gateway_word_guard
    (Vint(if zlt 8(Int.unsigned width)then Int.one else Int.zero)).
Proof.
  intro WIDTH;eapply binary_expression_value.
  - apply old_expression_value,value_temp;exact WIDTH.
  - split;[apply eval_Esizeof|].
    intros other EVALUATION;inversion EVALUATION;subst;try reflexivity.
    match goal with LOCATION:eval_lvalue _ _ _ _ (Esizeof _ _) _ _ _|-_=>inversion LOCATION end.
  - change (Some(Val.of_bool(Int64.ltu(Int64.repr 8)(Int64.repr(Int.unsigned width))))=
      Some(Vint(if zlt 8(Int.unsigned width)then Int.one else Int.zero))).
    unfold Int64.ltu.
    rewrite(Int64.unsigned_repr 8)by(change(0<=8<=18446744073709551615);lia).
    rewrite(Int64.unsigned_repr(Int.unsigned width))by
      (pose proof(Int.unsigned_range width);change Int.modulus with 4294967296 in *;
       change Int64.max_unsigned with 18446744073709551615;lia).
    destruct(zlt 8(Int.unsigned width));reflexivity.
Qed.

Lemma gateway_word_large_fails ge buffer arguments memory :
  8<Int.unsigned(word_width arguments) ->
  gateway_constant_path ge(Vint(Int.neg Int.one))
    (State f_host_word(fn_body f_host_word)Kstop(gateway_word_environment buffer)
      (gateway_word_parameters arguments)memory).
Proof.
  intro LARGE;rewrite gateway_word_body_structure.
  eapply gateway_constant_next with(next:=State f_host_word
    (Ssequence gateway_word_check gateway_word_test)(Kseq gateway_word_after Kstop)
    (gateway_word_environment buffer)(gateway_word_parameters arguments)memory).
  - cbn;tauto.
  - intro another;apply unchanged_store_edge,edge_seq.
  - eapply gateway_constant_next with(next:=State f_host_word gateway_word_check
      (Kseq gateway_word_test(Kseq gateway_word_after Kstop))
      (gateway_word_environment buffer)(gateway_word_parameters arguments)memory).
    + cbn;tauto.
    + intro another;apply unchanged_store_edge,edge_seq.
    + eapply gateway_constant_next with(next:=State f_host_word(Sset _t'1(Econst_int(Int.repr 1)tint))
        (Kseq gateway_word_test(Kseq gateway_word_after Kstop))
        (gateway_word_environment buffer)(gateway_word_parameters arguments)memory).
      * cbn;tauto.
      * intro another;eapply certified_if_edge with(b:=true).
        -- pose proof(gateway_word_guard_value ge(gateway_word_environment buffer)
             (gateway_word_parameters arguments)another(word_width arguments)ltac:(reflexivity))as VALUE.
           rewrite zlt_true in VALUE by exact LARGE;exact VALUE.
        -- reflexivity.
      * eapply gateway_constant_next with(next:=State f_host_word Sskip
          (Kseq gateway_word_test(Kseq gateway_word_after Kstop))
          (gateway_word_environment buffer)(PTree.set _t'1(Vint Int.one)(gateway_word_parameters arguments))memory).
        -- cbn;tauto.
        -- intro another;apply unchanged_store_edge;apply edge_set;constructor.
        -- eapply gateway_constant_next with(next:=State f_host_word gateway_word_test
            (Kseq gateway_word_after Kstop)(gateway_word_environment buffer)
            (PTree.set _t'1(Vint Int.one)(gateway_word_parameters arguments))memory).
           ++ cbn;tauto.
           ++ intro another;apply unchanged_store_edge,edge_skip_seq.
           ++ eapply gateway_constant_next with(next:=State f_host_word gateway_word_failure
                (Kseq gateway_word_after Kstop)(gateway_word_environment buffer)
                (PTree.set _t'1(Vint Int.one)(gateway_word_parameters arguments))memory).
              ** cbn;tauto.
              ** intro another;apply unchanged_store_edge;eapply edge_if with(b:=true).
                 --- apply value_temp;apply PTree.gss.
                 --- reflexivity.
              ** eapply gateway_constant_at_return with(value:=Vint(Int.neg Int.one)).
                 --- reflexivity.
                 --- intro another;apply old_expression_value;eapply value_unary;[constructor|reflexivity].
                 --- intro another;reflexivity.
Qed.

Theorem gateway_actual_word_width_bounded {World Event}(backend:gateway_backend World Event)ge
    arguments before world events after next :
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_word)(gateway_word_values arguments)Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  Int.unsigned(word_width arguments)<=8.
Proof.
  intro RUN;destruct(Z_le_gt_dec(Int.unsigned(word_width arguments))8)as[BOUND|LARGE];[exact BOUND|].
  destruct(actual_gateway_function_entry backend ge f_host_word(gateway_word_values arguments)Kstop
    before world events(Vint Int.zero)Kstop after next RUN)
    as[prefix[suffix[entry_memory[entry_world[environment[temporaries[allocated
      [EVENTS[PREFIX[ENTRY BODY]]]]]]]]]].
  destruct(gateway_actual_word_entry ge entry_memory arguments environment temporaries allocated ENTRY)
    as[buffer[ENV[TEMPS[ALLOC[FRAME[FRESH OWN]]]]]];subst environment temporaries.
  pose proof(gateway_constant_path_actual backend ge _ _ entry_world suffix(Vint Int.zero)after next
    (gateway_word_large_fails ge buffer arguments allocated ltac:(lia))BODY)as BAD;discriminate.
Qed.

Definition gateway_word_read_arguments buffer arguments :=
  [word_stream arguments;Vptr buffer Ptrofs.zero;Vlong(Int64.repr(Int.unsigned(word_width arguments)))].
Definition gateway_word_read_cont buffer arguments continuation :=
  Kcall(Some _t'2)f_host_word(gateway_word_environment buffer)(gateway_word_parameters arguments)
    (Kseq gateway_word_read_bool(Kseq gateway_word_test(Kseq gateway_word_after continuation))).

Lemma gateway_word_array_pointer ge buffer temporaries memory :
  expression_value ge(gateway_word_environment buffer)temporaries memory
    (Evar _bytes(tarray tuchar 8))(Vptr buffer Ptrofs.zero).
Proof.
  eapply location_read_value;[apply local_location_value;reflexivity|].
  apply deref_loc_reference;reflexivity.
Qed.

Lemma gateway_word_read_call (ge:Clight.genv) buffer arguments memory continuation symbol block offset :
  word_stream arguments=Vptr block offset ->
  Genv.find_symbol ge _host_read=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some(Internal f_host_read) ->
  store_edge ge
    (State f_host_word gateway_word_read
      (Kseq gateway_word_read_bool(Kseq gateway_word_test(Kseq gateway_word_after continuation)))
      (gateway_word_environment buffer)(gateway_word_parameters arguments)memory)
    (Callstate(Internal f_host_read)(gateway_word_read_arguments buffer arguments)
      (gateway_word_read_cont buffer arguments continuation)memory).
Proof.
  intros STREAM SYMBOL FUNCTION;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=word_stream arguments).
    + apply old_expression_value,value_temp;reflexivity.
    + rewrite STREAM;reflexivity.
    + eapply cons_argument_values with(v:=Vptr buffer Ptrofs.zero).
      * apply gateway_word_array_pointer.
      * reflexivity.
      * eapply cons_argument_values with(v:=Vint(word_width arguments)).
        -- apply old_expression_value,value_temp;reflexivity.
        -- reflexivity.
        -- apply no_argument_values.
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Lemma gateway_word_body_read_path_retained (ge:Clight.genv) buffer arguments memory continuation symbol block offset :
  Int.unsigned(word_width arguments)<=8 ->word_stream arguments=Vptr block offset ->
  Genv.find_symbol ge _host_read=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some(Internal f_host_read) ->
  gateway_retained_call_path ge(Internal f_host_read)(gateway_word_read_arguments buffer arguments)
    (gateway_word_read_cont buffer arguments continuation)
    (State f_host_word(fn_body f_host_word)continuation(gateway_word_environment buffer)
      (gateway_word_parameters arguments)memory).
Proof.
  intros BOUND STREAM SYMBOL FUNCTION;rewrite gateway_word_body_structure.
  eapply gateway_retained_next with(next:=State f_host_word
    (Ssequence gateway_word_check gateway_word_test)(Kseq gateway_word_after continuation)
    (gateway_word_environment buffer)(gateway_word_parameters arguments)memory).
  - cbn;tauto.
  - intro another;apply unchanged_store_edge,edge_seq.
  - eapply gateway_retained_next with(next:=State f_host_word gateway_word_check
      (Kseq gateway_word_test(Kseq gateway_word_after continuation))
      (gateway_word_environment buffer)(gateway_word_parameters arguments)memory).
    + cbn;tauto.
    + intro another;apply unchanged_store_edge,edge_seq.
    + eapply gateway_retained_next with(next:=State f_host_word
        (Ssequence gateway_word_read gateway_word_read_bool)
        (Kseq gateway_word_test(Kseq gateway_word_after continuation))
        (gateway_word_environment buffer)(gateway_word_parameters arguments)memory).
      * cbn;tauto.
      * intro another;eapply certified_if_edge with(b:=false).
        -- pose proof(gateway_word_guard_value ge(gateway_word_environment buffer)
             (gateway_word_parameters arguments)another(word_width arguments)ltac:(reflexivity))as VALUE.
           rewrite zlt_false in VALUE by lia;exact VALUE.
        -- reflexivity.
      * eapply gateway_retained_next with(next:=State f_host_word gateway_word_read
          (Kseq gateway_word_read_bool(Kseq gateway_word_test(Kseq gateway_word_after continuation)))
          (gateway_word_environment buffer)(gateway_word_parameters arguments)memory).
        -- cbn;tauto.
        -- intro another;apply unchanged_store_edge,edge_seq.
        -- eapply gateway_retained_next with(next:=Callstate(Internal f_host_read)
             (gateway_word_read_arguments buffer arguments)
             (gateway_word_read_cont buffer arguments continuation)memory).
           ++ cbn;tauto.
           ++ intro another;eapply gateway_word_read_call;eassumption.
           ++ constructor.
Qed.

Lemma gateway_word_body_read_path (ge:Clight.genv) buffer arguments memory continuation symbol block offset :
  Int.unsigned(word_width arguments)<=8 ->word_stream arguments=Vptr block offset ->
  Genv.find_symbol ge _host_read=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some(Internal f_host_read) ->
  gateway_control_call_path ge(Internal f_host_read)(gateway_word_read_arguments buffer arguments)
    (gateway_word_read_cont buffer arguments continuation)
    (State f_host_word(fn_body f_host_word)continuation(gateway_word_environment buffer)
      (gateway_word_parameters arguments)memory).
Proof.
  intros;apply gateway_retained_control;eapply gateway_word_body_read_path_retained;eassumption.
Qed.

Theorem gateway_actual_word_calls_read {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    arguments before world events after next symbol block offset :
  word_stream arguments=Vptr block offset ->
  Genv.find_symbol ge _host_read=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some(Internal f_host_read) ->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_word)(gateway_word_values arguments)Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  exists prefix suffix buffer memory called_world allocation_before allocated,
    events=prefix++suffix /\Mem.alloc allocation_before 0 8=(allocated,buffer) /\
    ~Mem.valid_block allocation_before buffer /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_word)(gateway_word_values arguments)Kstop before)world)prefix
      (gateway_live(Callstate(Internal f_host_read)(gateway_word_read_arguments buffer arguments)
        (gateway_word_read_cont buffer arguments Kstop)memory)called_world) /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_read)(gateway_word_read_arguments buffer arguments)
        (gateway_word_read_cont buffer arguments Kstop)memory)called_world)suffix
      (gateway_live(Returnstate(Vint Int.zero)Kstop after)next).
Proof.
  intros STREAM SYMBOL FUNCTION RUN.
  pose proof(gateway_actual_word_width_bounded backend ge _ _ _ _ _ _ RUN)as BOUND.
  destruct(actual_gateway_function_entry backend ge f_host_word(gateway_word_values arguments)Kstop
    before world events(Vint Int.zero)Kstop after next RUN)
    as[entry_prefix[body_events[allocation_before[allocation_world[environment[temporaries[allocated
      [EVENTS[PREFIX[ENTRY BODY]]]]]]]]]].
  destruct(gateway_actual_word_entry ge allocation_before arguments environment temporaries allocated ENTRY)
    as[buffer[ENV[TEMPS[ALLOC[FRAME[FRESH OWN]]]]]];subst environment temporaries.
  destruct(gateway_control_call_cut backend ge(Internal f_host_read)
    (gateway_word_read_arguments buffer arguments)(gateway_word_read_cont buffer arguments Kstop)
    _ allocation_world body_events(Vint Int.zero)after next
    (gateway_word_body_read_path ge buffer arguments allocated Kstop symbol block offset
      BOUND STREAM SYMBOL FUNCTION)BODY)
    as[body_prefix[suffix[memory[called_world[BODY_EVENTS[CALL REST]]]]]].
  exists(entry_prefix++gateway_source E0::body_prefix),suffix,buffer,memory,called_world,allocation_before,allocated.
  split;[rewrite EVENTS,BODY_EVENTS;rewrite<-app_assoc;reflexivity|].
  split;[exact ALLOC|]. split;[exact FRESH|]. split;[|exact REST].
  eapply gateway_steps_append;[exact PREFIX|].
  econstructor;[apply gateway_internal;[exact I|apply step_internal_function;exact ENTRY]|exact CALL].
Qed.

Lemma gateway_word_failed_read_path ge buffer arguments memory :
  gateway_constant_path ge(Vint(Int.neg Int.one))
    (Returnstate(Vint(Int.neg Int.one))(gateway_word_read_cont buffer arguments Kstop)memory).
Proof.
  eapply gateway_constant_next with(next:=State f_host_word Sskip
    (Kseq gateway_word_read_bool(Kseq gateway_word_test(Kseq gateway_word_after Kstop)))
    (gateway_word_environment buffer)
    (PTree.set _t'2(Vint(Int.neg Int.one))(gateway_word_parameters arguments))memory).
  - cbn;tauto.
  - intro another;apply unchanged_store_edge,edge_returnstate.
  - eapply gateway_constant_next with(next:=State f_host_word gateway_word_read_bool
      (Kseq gateway_word_test(Kseq gateway_word_after Kstop))(gateway_word_environment buffer)
      (PTree.set _t'2(Vint(Int.neg Int.one))(gateway_word_parameters arguments))memory).
    + cbn;tauto.
    + intro another;apply unchanged_store_edge,edge_skip_seq.
    + eapply gateway_constant_next with(next:=State f_host_word Sskip
        (Kseq gateway_word_test(Kseq gateway_word_after Kstop))(gateway_word_environment buffer)
        (PTree.set _t'1(Vint Int.one)(PTree.set _t'2(Vint(Int.neg Int.one))
          (gateway_word_parameters arguments)))memory).
      * cbn;tauto.
      * intro another;apply unchanged_store_edge,edge_set.
        eapply value_cast;[apply value_temp;apply PTree.gss|reflexivity].
      * eapply gateway_constant_next with(next:=State f_host_word gateway_word_test
          (Kseq gateway_word_after Kstop)(gateway_word_environment buffer)
          (PTree.set _t'1(Vint Int.one)(PTree.set _t'2(Vint(Int.neg Int.one))
            (gateway_word_parameters arguments)))memory).
        -- cbn;tauto.
        -- intro another;apply unchanged_store_edge,edge_skip_seq.
        -- eapply gateway_constant_next with(next:=State f_host_word gateway_word_failure
            (Kseq gateway_word_after Kstop)(gateway_word_environment buffer)
            (PTree.set _t'1(Vint Int.one)(PTree.set _t'2(Vint(Int.neg Int.one))
              (gateway_word_parameters arguments)))memory).
           ++ cbn;tauto.
           ++ intro another;apply unchanged_store_edge;eapply edge_if with(b:=true).
              ** apply value_temp;apply PTree.gss.
              ** reflexivity.
           ++ eapply gateway_constant_at_return with(value:=Vint(Int.neg Int.one)).
              ** reflexivity.
              ** intro another;apply old_expression_value;eapply value_unary;[constructor|reflexivity].
              ** intro another;reflexivity.
Qed.

Theorem gateway_word_successful_read_result {World Event}(backend:gateway_backend World Event)ge
    buffer arguments memory world events returned after next :
  (returned=Vint Int.zero \/returned=Vint(Int.neg Int.one)) ->
  gateway_steps backend ge
    (gateway_live(Returnstate returned(gateway_word_read_cont buffer arguments Kstop)memory)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->returned=Vint Int.zero.
Proof.
  intros[ZERO|ERROR] RUN;[exact ZERO|]. subst returned.
  pose proof(gateway_constant_path_actual backend ge _ _ world events(Vint Int.zero)after next
    (gateway_word_failed_read_path ge buffer arguments memory)RUN)as BAD;discriminate.
Qed.

Definition gateway_word_get :=match gateway_word_after with Ssequence(Ssequence call _) _=>call|_=>Sskip end.
Definition gateway_word_assignment :=match gateway_word_after with Ssequence(Ssequence _ store)_=>store|_=>Sskip end.
Definition gateway_word_return :=Sreturn(Some(Econst_int Int.zero tint)).
Definition gateway_word_after_read_parameters arguments :=
  PTree.set _t'1(Vint Int.zero)(PTree.set _t'2(Vint Int.zero)(gateway_word_parameters arguments)).
Definition gateway_word_get_arguments buffer arguments :=[Vptr buffer Ptrofs.zero;Vint(word_width arguments)].
Definition gateway_word_get_cont buffer arguments :=
  Kcall(Some _t'3)f_host_word(gateway_word_environment buffer)(gateway_word_after_read_parameters arguments)
    (Kseq gateway_word_assignment(Kseq gateway_word_return Kstop)).

Lemma gateway_word_get_structure :gateway_word_after=
  Ssequence(Ssequence gateway_word_get gateway_word_assignment)gateway_word_return.
Proof. reflexivity. Qed.

Lemma gateway_word_get_call (ge:Clight.genv) buffer arguments memory symbol :
  Genv.find_symbol ge _host_get64=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some(Internal f_host_get64) ->
  store_edge ge
    (State f_host_word gateway_word_get(Kseq gateway_word_assignment(Kseq gateway_word_return Kstop))
      (gateway_word_environment buffer)(gateway_word_after_read_parameters arguments)memory)
    (Callstate(Internal f_host_get64)(gateway_word_get_arguments buffer arguments)
      (gateway_word_get_cont buffer arguments)memory).
Proof.
  intros SYMBOL FUNCTION;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vptr buffer Ptrofs.zero).
    + apply gateway_word_array_pointer.
    + reflexivity.
    + eapply cons_argument_values with(v:=Vint(word_width arguments)).
      * apply old_expression_value,value_temp;reflexivity.
      * reflexivity.
      * apply no_argument_values.
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Lemma gateway_word_zero_read_get_path_retained (ge:Clight.genv) buffer arguments memory symbol :
  Genv.find_symbol ge _host_get64=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some(Internal f_host_get64) ->
  gateway_retained_call_path ge(Internal f_host_get64)(gateway_word_get_arguments buffer arguments)
    (gateway_word_get_cont buffer arguments)
    (Returnstate(Vint Int.zero)(gateway_word_read_cont buffer arguments Kstop)memory).
Proof.
  intros SYMBOL FUNCTION.
  eapply gateway_retained_next with(next:=State f_host_word Sskip
    (Kseq gateway_word_read_bool(Kseq gateway_word_test(Kseq gateway_word_after Kstop)))
    (gateway_word_environment buffer)(PTree.set _t'2(Vint Int.zero)(gateway_word_parameters arguments))memory).
  - cbn;tauto.
  - intro another;apply unchanged_store_edge,edge_returnstate.
  - eapply gateway_retained_next with(next:=State f_host_word gateway_word_read_bool
      (Kseq gateway_word_test(Kseq gateway_word_after Kstop))(gateway_word_environment buffer)
      (PTree.set _t'2(Vint Int.zero)(gateway_word_parameters arguments))memory).
    + cbn;tauto.
    + intro another;apply unchanged_store_edge,edge_skip_seq.
    + eapply gateway_retained_next with(next:=State f_host_word Sskip
        (Kseq gateway_word_test(Kseq gateway_word_after Kstop))(gateway_word_environment buffer)
        (gateway_word_after_read_parameters arguments)memory).
      * cbn;tauto.
      * intro another;apply unchanged_store_edge,edge_set.
        eapply value_cast;[apply value_temp;apply PTree.gss|reflexivity].
      * eapply gateway_retained_next with(next:=State f_host_word gateway_word_test
          (Kseq gateway_word_after Kstop)(gateway_word_environment buffer)
          (gateway_word_after_read_parameters arguments)memory).
        -- cbn;tauto.
        -- intro another;apply unchanged_store_edge,edge_skip_seq.
        -- eapply gateway_retained_next with(next:=State f_host_word Sskip
            (Kseq gateway_word_after Kstop)(gateway_word_environment buffer)
            (gateway_word_after_read_parameters arguments)memory).
           ++ cbn;tauto.
           ++ intro another;apply unchanged_store_edge;eapply edge_if with(b:=false).
              ** apply value_temp;reflexivity.
              ** reflexivity.
           ++ eapply gateway_retained_next with(next:=State f_host_word gateway_word_after Kstop
                (gateway_word_environment buffer)(gateway_word_after_read_parameters arguments)memory).
              ** cbn;tauto.
              ** intro another;apply unchanged_store_edge,edge_skip_seq.
              ** rewrite gateway_word_get_structure.
                 eapply gateway_retained_next with(next:=State f_host_word
                   (Ssequence gateway_word_get gateway_word_assignment)(Kseq gateway_word_return Kstop)
                   (gateway_word_environment buffer)(gateway_word_after_read_parameters arguments)memory).
                 --- cbn;tauto.
                 --- intro another;apply unchanged_store_edge,edge_seq.
                 --- eapply gateway_retained_next with(next:=State f_host_word gateway_word_get
                       (Kseq gateway_word_assignment(Kseq gateway_word_return Kstop))
                       (gateway_word_environment buffer)(gateway_word_after_read_parameters arguments)memory).
                     +++ cbn;tauto.
                     +++ intro another;apply unchanged_store_edge,edge_seq.
                     +++ eapply gateway_retained_next with(next:=Callstate(Internal f_host_get64)
                           (gateway_word_get_arguments buffer arguments)(gateway_word_get_cont buffer arguments)memory).
                         *** cbn;tauto.
                         *** intro another;eapply gateway_word_get_call;eassumption.
                         *** constructor.
Qed.

Lemma gateway_word_zero_read_get_path (ge:Clight.genv) buffer arguments memory symbol :
  Genv.find_symbol ge _host_get64=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some(Internal f_host_get64) ->
  gateway_control_call_path ge(Internal f_host_get64)(gateway_word_get_arguments buffer arguments)
    (gateway_word_get_cont buffer arguments)
    (Returnstate(Vint Int.zero)(gateway_word_read_cont buffer arguments Kstop)memory).
Proof.
  intros;apply gateway_retained_control;eapply gateway_word_zero_read_get_path_retained;eassumption.
Qed.

(* Undefined native values remain possible in the broad machine. They cannot
   cross the actual C cast in a successful caller execution. *)
Lemma gateway_word_undefined_read_path ge buffer arguments memory :
  gateway_blocked_path ge
    (Returnstate Vundef(gateway_word_read_cont buffer arguments Kstop)memory).
Proof.
  eapply gateway_blocked_next with(next:=State f_host_word Sskip
    (Kseq gateway_word_read_bool(Kseq gateway_word_test(Kseq gateway_word_after Kstop)))
    (gateway_word_environment buffer)(PTree.set _t'2 Vundef(gateway_word_parameters arguments))memory).
  - cbn;tauto.
  - intro another;apply unchanged_store_edge,edge_returnstate.
  - eapply gateway_blocked_next with(next:=State f_host_word gateway_word_read_bool
      (Kseq gateway_word_test(Kseq gateway_word_after Kstop))(gateway_word_environment buffer)
      (PTree.set _t'2 Vundef(gateway_word_parameters arguments))memory).
    + cbn;tauto.
    + intro another;apply unchanged_store_edge,edge_skip_seq.
    + apply gateway_blocked_at.
      * cbn;tauto.
      * intros;discriminate.
      * intros another trace target STEP;inversion STEP;subst;
          try match goal with BAD:_=_\/_=_|-_=>destruct BAD;discriminate end.
        match goal with VALUE:eval_expr _ _ _ _(Ecast _ _) _|-_=>inversion VALUE;subst end.
        -- match goal with VALUE:eval_expr _ _ _ _(Etempvar _t'2 _) _|-_=>
             pose proof(evaluated_unique _ _ _ _ _ _
               (value_temp _ _ _ _ _ tint Vundef ltac:(apply PTree.gss))_ VALUE)as SAME;subst end.
           discriminate.
        -- match goal with LOCATION:eval_lvalue _ _ _ _(Ecast _ _) _ _ _|-_=>inversion LOCATION end.
Qed.

Theorem gateway_word_successful_typed_read_result {World Event}(backend:gateway_backend World Event)ge
    buffer arguments memory world events returned after next :
  (returned=Vundef \/returned=Vint Int.zero \/returned=Vint(Int.neg Int.one)) ->
  gateway_steps backend ge
    (gateway_live(Returnstate returned(gateway_word_read_cont buffer arguments Kstop)memory)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->returned=Vint Int.zero.
Proof.
  intros[UNDEFINED|TYPED] RUN.
  - subst returned;exfalso;eapply gateway_blocked_cannot_return;
      [apply gateway_word_undefined_read_path|exact RUN].
  - eapply gateway_word_successful_read_result;eassumption.
Qed.

Record gateway_word_call_data (World Event:Type) :Type:={
  word_chain_buffer:block;
  word_chain_prefix:list(gateway_event Event);
  word_chain_read:list(gateway_event Event);
  word_chain_middle:list(gateway_event Event);
  word_chain_get:list(gateway_event Event);
  word_chain_suffix:list(gateway_event Event);
  word_chain_read_before:Memory.mem;
  word_chain_read_world:World;
  word_chain_read_after:Memory.mem;
  word_chain_read_next:World;
  word_chain_get_before:Memory.mem;
  word_chain_get_world:World;
  word_chain_get_after:Memory.mem;
  word_chain_get_next:World;
  word_chain_get_value:Values.val;
  word_chain_allocation_before:Memory.mem;
  word_chain_allocated:Memory.mem
}.

Record gateway_word_call_facts {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    arguments before world events after next(data:gateway_word_call_data World Event) :Prop:={
  word_chain_allocation:Mem.alloc(word_chain_allocation_before _ _ data)0 8=
    (word_chain_allocated _ _ data,word_chain_buffer _ _ data);
  word_chain_width:Int.unsigned(word_width arguments)<=8;
  word_chain_order:events=(word_chain_prefix _ _ data)++(word_chain_read _ _ data)++(word_chain_middle _ _ data)++(word_chain_get _ _ data)++(word_chain_suffix _ _ data);
  word_chain_to_read:gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_word)(gateway_word_values arguments)Kstop before)world)
    (word_chain_prefix _ _ data)(gateway_live(Callstate(Internal f_host_read)
      (gateway_word_read_arguments (word_chain_buffer _ _ data) arguments)
      (gateway_word_read_cont (word_chain_buffer _ _ data) arguments Kstop)(word_chain_read_before _ _ data))(word_chain_read_world _ _ data));
  word_chain_read_run:gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_read)(gateway_word_read_arguments (word_chain_buffer _ _ data) arguments)Kstop
      (word_chain_read_before _ _ data))(word_chain_read_world _ _ data))(word_chain_read _ _ data)
    (gateway_live(Returnstate(Vint Int.zero)Kstop (word_chain_read_after _ _ data))(word_chain_read_next _ _ data));
  word_chain_to_get:gateway_steps backend ge
    (gateway_live(Returnstate(Vint Int.zero)(gateway_word_read_cont (word_chain_buffer _ _ data) arguments Kstop)
      (word_chain_read_after _ _ data))(word_chain_read_next _ _ data))(word_chain_middle _ _ data)
    (gateway_live(Callstate(Internal f_host_get64)(gateway_word_get_arguments (word_chain_buffer _ _ data) arguments)
      (gateway_word_get_cont (word_chain_buffer _ _ data) arguments)(word_chain_get_before _ _ data))(word_chain_get_world _ _ data));
  word_chain_get_run:gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_get64)(gateway_word_get_arguments (word_chain_buffer _ _ data) arguments)Kstop
      (word_chain_get_before _ _ data))(word_chain_get_world _ _ data))(word_chain_get _ _ data)
    (gateway_live(Returnstate (word_chain_get_value _ _ data) Kstop (word_chain_get_after _ _ data))(word_chain_get_next _ _ data));
  word_chain_after_get:gateway_steps backend ge
    (gateway_live(Returnstate (word_chain_get_value _ _ data)(gateway_word_get_cont (word_chain_buffer _ _ data) arguments)
      (word_chain_get_after _ _ data))(word_chain_get_next _ _ data))(word_chain_suffix _ _ data)
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next)
}.

Definition gateway_word_call_chain {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    arguments before world events after next :Prop:=
  exists data,gateway_word_call_facts backend ge arguments before world events after next data.

Theorem gateway_actual_word_call_chain {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    arguments before world events after next read_symbol get_symbol stream_block stream_offset :
  word_stream arguments=Vptr stream_block stream_offset ->
  Genv.find_symbol ge _host_read=Some read_symbol ->
  Genv.find_funct_ptr ge read_symbol=Some(Internal f_host_read) ->
  Genv.find_symbol ge _host_get64=Some get_symbol ->
  Genv.find_funct_ptr ge get_symbol=Some(Internal f_host_get64) ->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_word)(gateway_word_values arguments)Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  gateway_word_call_chain backend ge arguments before world events after next.
Proof.
  intros STREAM READ_SYMBOL READ_FUNCTION GET_SYMBOL GET_FUNCTION RUN.
  pose proof(gateway_actual_word_width_bounded backend ge _ _ _ _ _ _ RUN)as WIDTH.
  destruct(gateway_actual_word_calls_read backend ge _ _ _ _ _ _ _ _ _
    STREAM READ_SYMBOL READ_FUNCTION RUN)
    as[prefix[read_tail[buffer[read_before[read_world[allocation_before[allocated
      [EVENTS[ALLOC[FRESH[TO_READ FROM_READ]]]]]]]]]]].
  destruct(gateway_return_cut backend ge(Internal f_host_read)(gateway_word_read_arguments buffer arguments)
    (gateway_word_read_cont buffer arguments Kstop)read_before read_world read_tail
    (Returnstate(Vint Int.zero)Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_READ)
    as[read_events[after_read[read_value[read_after[read_next[READ_EVENTS[READ_RUN READ_REST]]]]]]].
  pose proof(actual_host_read_return_type backend ge _ _ _ _ _ _ _ READ_RUN)as READ_TYPE.
  pose proof(gateway_word_successful_typed_read_result backend ge buffer arguments read_after read_next
    after_read read_value after next READ_TYPE READ_REST)as ZERO;subst read_value.
  destruct(gateway_control_call_cut backend ge(Internal f_host_get64)(gateway_word_get_arguments buffer arguments)
    (gateway_word_get_cont buffer arguments)_ read_next after_read(Vint Int.zero)after next
    (gateway_word_zero_read_get_path ge buffer arguments read_after get_symbol GET_SYMBOL GET_FUNCTION)READ_REST)
    as[middle[get_tail[get_before[get_world[GET_EVENTS[TO_GET FROM_GET]]]]]].
  destruct(gateway_return_cut backend ge(Internal f_host_get64)(gateway_word_get_arguments buffer arguments)
    (gateway_word_get_cont buffer arguments)get_before get_world get_tail
    (Returnstate(Vint Int.zero)Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_GET)
    as[get_events[suffix[get_value[get_after[get_next[LAST_EVENTS[GET_RUN GET_REST]]]]]]].
  exists{|word_chain_buffer:=buffer;word_chain_prefix:=prefix;word_chain_read:=read_events;
    word_chain_middle:=middle;word_chain_get:=get_events;word_chain_suffix:=suffix;
    word_chain_read_before:=read_before;word_chain_read_world:=read_world;
    word_chain_read_after:=read_after;word_chain_read_next:=read_next;
    word_chain_get_before:=get_before;word_chain_get_world:=get_world;
    word_chain_get_after:=get_after;word_chain_get_next:=get_next;word_chain_get_value:=get_value;
    word_chain_allocation_before:=allocation_before;word_chain_allocated:=allocated|}.
  constructor;cbn.
  - exact ALLOC.
  - exact WIDTH.
  - rewrite EVENTS,READ_EVENTS,GET_EVENTS,LAST_EVENTS;repeat rewrite app_assoc;reflexivity.
  - exact TO_READ.
  - exact READ_RUN.
  - exact TO_GET.
  - exact GET_RUN.
  - exact GET_REST.
Qed.

Lemma gateway_native_byte_roundtrip bytes :gateway_native_bytes(map Readers.byte_word bytes)=bytes.
Proof.
  induction bytes as[|byte rest IH];[reflexivity|].
  cbn[gateway_native_bytes map];unfold Readers.byte_word.
  rewrite Int.unsigned_repr by(pose proof(Byte.unsigned_range byte);
    change Byte.modulus with 256 in *;change Int.max_unsigned with 4294967295;lia).
  rewrite Byte.repr_unsigned;f_equal;exact IH.
Qed.

(* §AR-host-boundary.interfaces.gateway: The read result is fed to the actual get64 call
   in order. *)


Definition gateway_word_store_region buffer output offset block position :Prop:=
  gateway_byte_region buffer 0 8 block position \/gateway_byte_region output offset 8 block position.
Definition gateway_word_store_ready buffer output offset memory :Prop:=
  Mem.range_perm memory buffer 0 8 Cur Freeable /\Mem.valid_access memory Mint64 output offset Writable.
Definition gateway_word_stored buffer output offset value memory :Prop:=
  Mem.range_perm memory buffer 0 8 Cur Freeable /\Mem.load Mint64 memory output offset=Some(Vlong value).

Lemma gateway_word_store_ready_closed buffer output offset :
  gateway_region_closed(gateway_word_store_region buffer output offset)(gateway_word_store_ready buffer output offset).
Proof.
  intros before after[BUFFER[OUT ALIGNMENT]]FRAME;split.
  - intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME|left;split;[reflexivity|cbn;lia]|].
    apply BUFFER;exact RANGE.
  - split;[|exact ALIGNMENT]. intros position RANGE;eapply Mem.perm_unchanged_on;
      [exact FRAME|right;split;[reflexivity|exact RANGE]|apply OUT;exact RANGE].
Qed.

Lemma gateway_word_stored_closed buffer output offset value :
  gateway_region_closed(gateway_word_store_region buffer output offset)(gateway_word_stored buffer output offset value).
Proof.
  intros before after[BUFFER LOAD]FRAME;split.
  - intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME|left;split;[reflexivity|cbn;lia]|].
    apply BUFFER;exact RANGE.
  - eapply Mem.load_unchanged_on;[exact FRAME| |exact LOAD].
    intros position RANGE;right;split;[reflexivity|exact RANGE].
Qed.

Lemma gateway_word_output_closed buffer output offset value :
  gateway_region_closed(gateway_word_store_region buffer output offset)
    (fun memory=>Mem.load Mint64 memory output offset=Some(Vlong value)).
Proof.
  intros before after LOAD FRAME;eapply Mem.load_unchanged_on;[exact FRAME| |exact LOAD].
  intros position RANGE;right;split;[reflexivity|exact RANGE].
Qed.

Lemma gateway_word_after_get_store_path (ge:Clight.genv)buffer arguments output ofs value memory :
  word_output arguments=Vptr output ofs ->output<>buffer ->Ptrofs.unsigned ofs+8<=Ptrofs.modulus ->
  gateway_framed_path ge(gateway_word_store_region buffer output(Ptrofs.unsigned ofs))
    (gateway_word_store_ready buffer output(Ptrofs.unsigned ofs))
    (Returnstate(Vlong value)(gateway_word_get_cont buffer arguments)memory)(Vint Int.zero)
    (fun after=>Mem.load Mint64 after output(Ptrofs.unsigned ofs)=Some(Vlong value)).
Proof.
  intros OUTPUT SEPARATE BOUND.
  eapply gateway_framed_same with(next:=State f_host_word Sskip
    (Kseq gateway_word_assignment(Kseq gateway_word_return Kstop))(gateway_word_environment buffer)
    (PTree.set _t'3(Vlong value)(gateway_word_after_read_parameters arguments))memory).
  - apply gateway_word_store_ready_closed.
  - cbn;tauto.
  - intros another GOOD;apply unchanged_store_edge,edge_returnstate.
  - eapply gateway_framed_same with(next:=State f_host_word gateway_word_assignment
      (Kseq gateway_word_return Kstop)(gateway_word_environment buffer)
      (PTree.set _t'3(Vlong value)(gateway_word_after_read_parameters arguments))memory).
    + apply gateway_word_store_ready_closed.
    + cbn;tauto.
    + intros another GOOD;apply unchanged_store_edge,edge_skip_seq.
    + eapply gateway_framed_next with(next:=State f_host_word Sskip
        (Kseq gateway_word_return Kstop)(gateway_word_environment buffer)
        (PTree.set _t'3(Vlong value)(gateway_word_after_read_parameters arguments))memory)
        (middle:=gateway_word_stored buffer output(Ptrofs.unsigned ofs)value).
      * apply gateway_word_store_ready_closed.
      * cbn;tauto.
      * intros another[BUFFER OWN].
        destruct(Mem.valid_access_store another Mint64 output(Ptrofs.unsigned ofs)(Vlong value)OWN)
          as[stored STORE].
        exists stored;split.
        -- eapply assignment_source_edge with(b:=output)(ofs:=ofs)(v:=Vlong value)(w:=Vlong value).
           ++ apply pointer_location_value,old_expression_value,value_temp.
              change(Some(word_output arguments)=Some(Vptr output ofs));rewrite OUTPUT;reflexivity.
           ++ apply old_expression_value,value_temp;apply PTree.gss.
           ++ reflexivity.
           ++ apply assign_loc_value with(chunk:=Mint64);[reflexivity|].
              unfold Mem.storev;rewrite zle_true by exact BOUND;exact STORE.
        -- split.
           ++ intros position RANGE;eapply Mem.perm_store_1;[exact STORE|apply BUFFER;exact RANGE].
           ++ exact(Mem.load_store_same _ _ _ _ _ _ STORE).
      * eapply gateway_framed_same with(next:=State f_host_word gateway_word_return Kstop
          (gateway_word_environment buffer)
          (PTree.set _t'3(Vlong value)(gateway_word_after_read_parameters arguments))memory).
        -- apply gateway_word_stored_closed.
        -- cbn;tauto.
        -- intros another GOOD;apply unchanged_store_edge,edge_skip_seq.
        -- eapply gateway_framed_next with(next:=Returnstate(Vint Int.zero)Kstop memory)
             (middle:=fun after=>Mem.load Mint64 after output(Ptrofs.unsigned ofs)=Some(Vlong value)).
           ++ apply gateway_word_stored_closed.
           ++ cbn;tauto.
           ++ intros another[BUFFER LOAD].
              destruct(Mem.range_perm_free another buffer 0 8 BUFFER)as[freed FREE].
              exists freed;split.
              ** eapply certified_local_return_edge with(v:=Vint Int.zero)(w:=Vint Int.zero).
                 --- apply old_expression_value;constructor.
                 --- reflexivity.
                 --- change(Mem.free_list another[(buffer,0,8)]=Some freed).
                     cbn;rewrite FREE;reflexivity.
              ** rewrite(Mem.load_free _ _ _ _ _ FREE Mint64 output(Ptrofs.unsigned ofs));
                   [exact LOAD|left;exact SEPARATE].
           ++ apply gateway_framed_return;[apply gateway_word_output_closed|auto].
Qed.

Theorem gateway_actual_word_stores_decoder_value {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    active buffer arguments output ofs value before world events after next :
  word_output arguments=Vptr output ofs ->output<>buffer ->Ptrofs.unsigned ofs+8<=Ptrofs.modulus ->
  gateway_private_contract backend(gateway_word_store_region buffer output(Ptrofs.unsigned ofs))active ->
  active world ->gateway_word_store_ready buffer output(Ptrofs.unsigned ofs)before ->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vlong value)(gateway_word_get_cont buffer arguments)before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  Mem.loadv Mint64 after(Vptr output ofs)=Some(Vlong value) /\active next.
Proof.
  intros OUTPUT SEPARATE BOUND LAW ACTIVE READY RUN.
  destruct(gateway_framed_return_exact backend ge _ active LAW _ _ _ _ before world events
    (Vint Int.zero)after next ACTIVE READY
    (gateway_word_after_get_store_path ge buffer arguments output ofs value before OUTPUT SEPARATE BOUND)RUN)
    as[RESULT[LOAD NEXT]];split;[|exact NEXT].
  unfold Mem.loadv;rewrite zle_true by exact BOUND;exact LOAD.
Qed.

Lemma gateway_actual_get64_readonly arguments memory :
  gateway_readonly_state(Callstate(Internal f_host_get64)arguments Kstop memory).
Proof. split;reflexivity. Qed.

Theorem gateway_actual_get64_preserves_side {World Event}(backend:gateway_backend World Event)ge side
    (discipline:gateway_runtime_discipline backend side)arguments before world events value after next :
  side before world ->
  gateway_steps backend ge(gateway_live(Callstate(Internal f_host_get64)arguments Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->side after next.
Proof.
  intros SIDE RUN;eapply gateway_readonly_run_side;
    [exact discipline|apply gateway_actual_get64_readonly|exact SIDE|exact RUN].
Qed.

(* §AR-host-boundary.interfaces.gateway: Actual get64 consumes coupled runtime roots, not
   a world-only guess. *)
Theorem gateway_get64_actual_coupled {World Event}(backend:gateway_backend World Event)ge side
    block ofs values before world events returned after next :
  gateway_coupled_private_contract backend(gateway_byte_region block(Ptrofs.unsigned ofs)(length values))side ->
  side before world ->(length values<=8)%nat ->
  Ptrofs.unsigned ofs+Z.of_nat(length values)<=Ptrofs.modulus ->gateway_read_ready block ofs values before ->
  gateway_steps backend ge(gateway_live(gateway_get_initial block ofs(length values)Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  returned=Vlong(Int64.repr(Z.of_nat(gateway_natural_decode(gateway_int_bytes values)))) /\
    gateway_read_ready block ofs values after /\side after next.
Proof.
  intros LAW SIDE WIDTH BOUND READY RUN.
  destruct(gateway_framed_coupled_return_exact backend ge _ side LAW
    (gateway_read_ready block ofs values)(gateway_get_initial block ofs(length values)Kstop before)
    (Vlong(gateway_get_value values))(gateway_read_ready block ofs values)world events returned after next
    SIDE(gateway_actual_get64_readonly _ _)READY
    (gateway_get64_framed ge block ofs values before WIDTH BOUND)RUN)as[VALUE[POST NEXT]].
  split;[|split;assumption].
  rewrite VALUE;f_equal;rewrite<-(Int64.repr_unsigned(gateway_get_value values)).
  rewrite gateway_get_value_numeric;[reflexivity|eapply gateway_read_ready_bounds;exact READY|exact WIDTH].
Qed.

Theorem gateway_get64_shared_coupled {World Event}(backend:gateway_backend World Event)ge side
    block ofs values before world events returned after next :
  gateway_coupled_private_contract backend(gateway_byte_region block(Ptrofs.unsigned ofs)(length values))side ->
  side before world ->(length values<=8)%nat ->
  Ptrofs.unsigned ofs+Z.of_nat(length values)<=Ptrofs.modulus ->gateway_read_ready block ofs values before ->
  gateway_steps backend ge(gateway_live(gateway_get_initial block ofs(length values)Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  exists bytes,
    Mem.loadbytes before block(Ptrofs.unsigned ofs)(Z.of_nat(length values))=Some(map Byte bytes) /\
    Mem.loadbytes after block(Ptrofs.unsigned ofs)(Z.of_nat(length values))=Some(map Byte bytes) /\
    returned=Vlong(Int64.repr(Z.of_nat(nat_of_Nat(LeanCage_Host_GatewayWords_decode
      (gateway_imported_nats(gateway_byte_naturals bytes)))))) /\side after next.
Proof.
  intros LAW SIDE WIDTH BOUND READY RUN.
  destruct(gateway_get64_actual_coupled backend ge side block ofs values before world events returned after next
    LAW SIDE WIDTH BOUND READY RUN)as[VALUE[POST NEXT]].
  exists(gateway_native_bytes values);repeat split.
  - apply gateway_ready_actual_bytes;assumption.
  - apply gateway_ready_actual_bytes;assumption.
  - rewrite gateway_native_naturals by(eapply gateway_read_ready_bounds;exact READY).
    rewrite gateway_shared_decode;exact VALUE.
  - exact NEXT.
Qed.

Theorem gateway_word_actual_get_from_read_bytes_coupled {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    side buffer arguments before world events after next bytes symbol :
  gateway_coupled_private_contract backend(gateway_byte_region buffer 0(length bytes))side ->
  side before world ->(length bytes<=8)%nat ->
  Int.unsigned(word_width arguments)=Z.of_nat(length bytes) ->
  Mem.loadbytes before buffer 0(Z.of_nat(length bytes))=Some(inj_bytes bytes) ->
  Genv.find_symbol ge _host_get64=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some(Internal f_host_get64) ->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vint Int.zero)(gateway_word_read_cont buffer arguments Kstop)before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  exists prefix get_events suffix get_before get_world get_after get_next,
    events=prefix++get_events++suffix /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)(gateway_word_read_cont buffer arguments Kstop)before)world)prefix
      (gateway_live(Callstate(Internal f_host_get64)(gateway_word_get_arguments buffer arguments)
        (gateway_word_get_cont buffer arguments)get_before)get_world) /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_get64)(gateway_word_get_arguments buffer arguments)Kstop get_before)get_world)
      get_events(gateway_live(Returnstate
        (Vlong(Int64.repr(Z.of_nat(nat_of_Nat(LeanCage_Host_GatewayWords_decode
          (gateway_imported_nats(gateway_byte_naturals bytes)))))))Kstop get_after)get_next) /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vlong(Int64.repr(Z.of_nat(nat_of_Nat(LeanCage_Host_GatewayWords_decode
          (gateway_imported_nats(gateway_byte_naturals bytes)))))))(gateway_word_get_cont buffer arguments)get_after)get_next)
      suffix(gateway_live(Returnstate(Vint Int.zero)Kstop after)next) /\
    side get_before get_world /\side get_after get_next /\Forall gateway_quiet_event prefix.
Proof.
  intros LAW SIDE WIDTH COUNT LOADED SYMBOL FUNCTION RUN.
  assert(BOUND:Ptrofs.unsigned Ptrofs.zero+Z.of_nat(length bytes)<=Ptrofs.modulus).
  { change(0+Z.of_nat(length bytes)<=18446744073709551616);lia. }
  pose proof(gateway_read_ready_from_bytes before buffer Ptrofs.zero bytes BOUND LOADED)as READY.
  assert(CLOSED:gateway_region_closed(gateway_byte_region buffer 0(length bytes))
    (gateway_read_ready buffer Ptrofs.zero(map Readers.byte_word bytes))).
  { rewrite<-(length_map Readers.byte_word bytes)at 1.
    apply gateway_read_ready_closed;rewrite length_map;exact BOUND. }
  set(guarded:=fun memory world=>side memory world /\
    gateway_read_ready buffer Ptrofs.zero(map Readers.byte_word bytes)memory).
  assert(DISCIPLINE:gateway_runtime_discipline backend guarded).
  { intros memory current changed following[CURRENT BYTES]INTERFERENCE.
    destruct(gateway_coupled_ambient _ _ _ LAW _ _ _ _ CURRENT INTERFERENCE)as[NEXT FRAME].
    split;[exact NEXT|eapply CLOSED;[exact BYTES|exact FRAME]]. }
  destruct(gateway_retained_call_ready_cut backend ge guarded DISCIPLINE
    (Internal f_host_get64)(gateway_word_get_arguments buffer arguments)(gateway_word_get_cont buffer arguments)
    (Returnstate(Vint Int.zero)(gateway_word_read_cont buffer arguments Kstop)before)world events(Vint Int.zero)after next
    (gateway_word_zero_read_get_path_retained ge buffer arguments before symbol SYMBOL FUNCTION)
    ltac:(split;assumption)RUN)
    as[prefix[get_tail[get_before[get_world[EVENTS[QUIET[PREFIX[[GET_SIDE GET_READY]FROM_GET]]]]]]]].
  destruct(gateway_return_cut backend ge(Internal f_host_get64)(gateway_word_get_arguments buffer arguments)
    (gateway_word_get_cont buffer arguments)get_before get_world get_tail
    (Returnstate(Vint Int.zero)Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_GET)
    as[get_events[suffix[get_value[get_after[get_next[GET_EVENTS[GET_RUN GET_REST]]]]]]].
  assert(SHARED_RUN:gateway_steps backend ge
    (gateway_live(gateway_get_initial buffer Ptrofs.zero(length(map Readers.byte_word bytes))Kstop get_before)get_world)
    get_events(gateway_live(Returnstate get_value Kstop get_after)get_next)).
  { unfold gateway_get_initial;rewrite length_map,<-COUNT,Int.repr_unsigned;exact GET_RUN. }
  assert(GET_LAW:gateway_coupled_private_contract backend
    (gateway_byte_region buffer(Ptrofs.unsigned Ptrofs.zero)(length(map Readers.byte_word bytes)))side).
  { rewrite length_map;exact LAW. }
  destruct(gateway_get64_shared_coupled backend ge side buffer Ptrofs.zero(map Readers.byte_word bytes)
    get_before get_world get_events get_value get_after get_next GET_LAW GET_SIDE
    ltac:(rewrite length_map;exact WIDTH)ltac:(rewrite length_map;exact BOUND)GET_READY SHARED_RUN)
    as[actual_bytes[INITIAL[FINAL[VALUE NEXT_SIDE]]]].
  assert(EXPECTED:Mem.loadbytes get_before buffer 0(Z.of_nat(length bytes))=Some(inj_bytes bytes)).
  { pose proof(gateway_ready_actual_bytes buffer Ptrofs.zero(map Readers.byte_word bytes)get_before
      ltac:(rewrite length_map;exact BOUND)GET_READY)as NATIVE_LOAD.
    rewrite length_map,gateway_native_byte_roundtrip in NATIVE_LOAD;exact NATIVE_LOAD. }
  rewrite length_map in INITIAL.
  change(Mem.loadbytes get_before buffer 0(Z.of_nat(length bytes))=Some(inj_bytes actual_bytes))in INITIAL.
  assert(SAME:inj_bytes actual_bytes=inj_bytes bytes)by(congruence).
  apply(f_equal proj_bytes)in SAME;rewrite !proj_inj_bytes in SAME;inversion SAME;subst actual_bytes.
  subst get_value;exists prefix,get_events,suffix,get_before,get_world,get_after,get_next.
  split;[rewrite EVENTS,GET_EVENTS,app_assoc;reflexivity|].
  split;[exact PREFIX|]. split;[exact GET_RUN|]. split;[exact GET_REST|].
  split;[exact GET_SIDE|]. split;[exact NEXT_SIDE|exact QUIET].
Qed.

Theorem gateway_word_actual_get_from_read_bytes {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    active buffer arguments before world events after next bytes symbol :
  gateway_private_contract backend(gateway_byte_region buffer 0(length bytes))active ->
  active world ->(length bytes<=8)%nat ->
  Int.unsigned(word_width arguments)=Z.of_nat(length bytes) ->
  Mem.loadbytes before buffer 0(Z.of_nat(length bytes))=Some(inj_bytes bytes) ->
  Genv.find_symbol ge _host_get64=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some(Internal f_host_get64) ->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vint Int.zero)(gateway_word_read_cont buffer arguments Kstop)before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  exists prefix get_events suffix get_before get_world get_after get_next,
    events=prefix++get_events++suffix /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)(gateway_word_read_cont buffer arguments Kstop)before)world)prefix
      (gateway_live(Callstate(Internal f_host_get64)(gateway_word_get_arguments buffer arguments)
        (gateway_word_get_cont buffer arguments)get_before)get_world) /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_get64)(gateway_word_get_arguments buffer arguments)Kstop get_before)get_world)
      get_events(gateway_live(Returnstate
        (Vlong(Int64.repr(Z.of_nat(nat_of_Nat(LeanCage_Host_GatewayWords_decode
          (gateway_imported_nats(gateway_byte_naturals bytes)))))))Kstop get_after)get_next) /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vlong(Int64.repr(Z.of_nat(nat_of_Nat(LeanCage_Host_GatewayWords_decode
          (gateway_imported_nats(gateway_byte_naturals bytes)))))))(gateway_word_get_cont buffer arguments)get_after)get_next)
      suffix(gateway_live(Returnstate(Vint Int.zero)Kstop after)next).
Proof.
  intros LAW ACTIVE WIDTH COUNT LOADED SYMBOL FUNCTION RUN.
  assert(COUPLED:gateway_coupled_private_contract backend(gateway_byte_region buffer 0(length bytes))
    (fun _ world=>active world)).
  { constructor;intros memory current changed following CURRENT INTERFERENCE.
    eapply gateway_private_ambient;[exact LAW|exact CURRENT|exact INTERFERENCE]. }
  destruct(gateway_word_actual_get_from_read_bytes_coupled backend ge(fun _ world=>active world)
    buffer arguments before world events after next bytes symbol COUPLED ACTIVE WIDTH COUNT LOADED SYMBOL FUNCTION RUN)
    as[prefix[get_events[suffix[get_before[get_world[get_after[get_next FACTS]]]]]]].
  exists prefix,get_events,suffix,get_before,get_world,get_after,get_next;tauto.
Qed.
