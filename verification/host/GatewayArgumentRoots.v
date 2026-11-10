(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual retain loop roots each parsed argument before conversion. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayRuntime GatewayArgumentContext
  GatewayArgumentsSource GatewayArgumentsPure GatewayEffectRuntime GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Section ArgumentRoots.
Context {World Event}(backend:gateway_backend World Event)(python:World->python_world)
  (runtime:gateway_cpython_contract backend python)(quiet:gateway_quiet_gil backend python).
Variable ge:Clight.genv.
Variable array:block.
Variable offset:ptrofs.
Variable symbol:block.
Hypotheses(SYMBOL:Genv.find_symbol ge _Py_IncRef=Some symbol)
  (FUNCTION:Genv.find_funct_ptr ge symbol=Some python_incref_definition).

Local Definition argument_ready values processed original:=
  gateway_argument_context python array offset values processed original.

Ltac argument_same target:=
  eapply gateway_effect_same with(next:=target);
    [eapply gateway_argument_context_ambient;exact quiet|cbn;tauto
    |intros available current GOOD;cbn[gateway_replace_memory]|].

Lemma argument_selected_element values processed original before world temporaries index object:
  argument_ready values processed original before world->
  temporaries!_arguments=Some(Vptr array offset)->temporaries!_index=Some(Vint(Int.repr(Z.of_nat index)))->
  (length values<=14)%nat->nth_error values index=Some object->
  expression_value ge empty_env temporaries before arguments_element object.
Proof.
  intros CONTEXT POINTER INDEX BOUND SELECTED.
  assert(SMALL:(index<length values)%nat)by(apply nth_error_Some;rewrite SELECTED;discriminate).
  eapply actual_argument_element;[exact POINTER|exact INDEX| | |].
  - apply Nat2Z.inj_lt in SMALL;apply Nat2Z.inj_le in BOUND;lia.
  - pose proof(@gateway_argument_bound World python array offset values processed original before world CONTEXT).
    apply Nat2Z.inj_lt in SMALL;lia.
  - exact(@gateway_argument_cells World python array offset values processed original before world CONTEXT index object SELECTED).
Qed.

Lemma argument_advance values processed original temporaries memory index result:
  temporaries!_index=Some(Vint(Int.repr(Z.of_nat index)))->(index<=14)%nat->
  gateway_effect_path backend ge(argument_ready values processed original)
    (State f_host_arguments_retain arguments_retain_loop Kstop empty_env
      (PTree.set _index(Vint(Int.repr(Z.of_nat index+1)))temporaries)memory)Vundef result->
  gateway_effect_path backend ge(argument_ready values processed original)
    (State f_host_arguments_retain Sskip arguments_retain_cont empty_env temporaries memory)Vundef result.
Proof.
  intros INDEX BOUND REST;eapply actual_arguments_increment.
  - eapply gateway_argument_context_ambient;exact quiet.
  - exact INDEX.
  - apply Nat2Z.inj_le in BOUND;lia.
  - exact REST.
Qed.

Theorem actual_arguments_retain_loop values original remaining:
  forall processed temporaries memory,
  values=processed++remaining->Forall gateway_argument_pointer remaining->(length values<=14)%nat->
  temporaries!_arguments=Some(Vptr array offset)->
  temporaries!_count=Some(Vint(Int.repr(Z.of_nat(length values))))->
  temporaries!_index=Some(Vint(Int.repr(Z.of_nat(length processed))))->
  gateway_effect_path backend ge(argument_ready values processed original)
    (State f_host_arguments_retain arguments_retain_loop Kstop empty_env temporaries memory)Vundef
    (argument_ready values values original).
Proof.
  induction remaining as[|object rest IH];intros processed temporaries memory VALUES POINTERS BOUND POINTER COUNT INDEX.
  - rewrite app_nil_r in VALUES;subst processed.
    eapply actual_arguments_end;[eapply gateway_argument_context_ambient;exact quiet|exact INDEX|exact COUNT| |reflexivity|auto].
    apply Nat2Z.inj_le in BOUND;lia.
  - inversion POINTERS as[|head remaining HEAD TAIL];subst head remaining.
    assert(SELECTED:nth_error values(length processed)=Some object).
    { rewrite VALUES,nth_error_app2 by lia;rewrite Nat.sub_diag;reflexivity. }
    assert(INDEX_BOUND:(length processed<length values)%nat).
    { rewrite VALUES,length_app;cbn;lia. }
    assert(NEXT_VALUES:values=(processed++[object])++rest).
    { rewrite<-app_assoc;exact VALUES. }
    assert(NEXT_INDEX:Z.of_nat(length(processed++[object]))=Z.of_nat(length processed)+1).
    { rewrite length_app,Nat2Z.inj_add;reflexivity. }
    assert(ADVANCE:forall changed current_memory,
      changed!_arguments=Some(Vptr array offset)->
      changed!_count=Some(Vint(Int.repr(Z.of_nat(length values))))->
      changed!_index=Some(Vint(Int.repr(Z.of_nat(length processed))))->
      gateway_effect_path backend ge(argument_ready values(processed++[object])original)
        (State f_host_arguments_retain Sskip arguments_retain_cont empty_env changed current_memory)Vundef
        (argument_ready values values original)).
    { intros changed current_memory ARGUMENTS COUNT_VALUE INDEX_VALUE.
      eapply argument_advance;[exact INDEX_VALUE|lia|].
      apply IH;[exact NEXT_VALUES|exact TAIL|exact BOUND| | |].
      - rewrite PTree.gso by discriminate;exact ARGUMENTS.
      - rewrite PTree.gso by discriminate;exact COUNT_VALUE.
      - rewrite PTree.gss,NEXT_INDEX;reflexivity. }
    argument_same(State f_host_arguments_retain arguments_retain_first arguments_retain_cont empty_env temporaries memory).
    { apply unchanged_store_edge,edge_loop. }
    argument_same(State f_host_arguments_retain(Sifthenelse arguments_guard Sskip Sbreak)
      (Kseq arguments_retain_body arguments_retain_cont)empty_env temporaries memory).
    { apply unchanged_store_edge,edge_seq. }
    argument_same(State f_host_arguments_retain Sskip(Kseq arguments_retain_body arguments_retain_cont)empty_env temporaries memory).
    { apply certified_if_edge with(v:=Vint Int.one)(b:=true).
      - pose proof(actual_arguments_guard ge temporaries available(Z.of_nat(length processed))(Z.of_nat(length values))
          INDEX COUNT ltac:(apply Nat2Z.inj_lt in INDEX_BOUND;apply Nat2Z.inj_le in BOUND;lia)
          ltac:(apply Nat2Z.inj_le in BOUND;lia))as TEST.
        destruct(zlt(Z.of_nat(length processed))(Z.of_nat(length values)));[exact TEST|].
        apply Nat2Z.inj_lt in INDEX_BOUND;lia.
      - reflexivity. }
    argument_same(State f_host_arguments_retain arguments_retain_body arguments_retain_cont empty_env temporaries memory).
    { apply unchanged_store_edge,edge_skip_seq. }
    argument_same(State f_host_arguments_retain(Sset _t'1 arguments_element)
      (Kseq arguments_retain_test arguments_retain_cont)empty_env temporaries memory).
    { apply unchanged_store_edge,edge_seq. }
    argument_same(State f_host_arguments_retain Sskip(Kseq arguments_retain_test arguments_retain_cont)empty_env
      (PTree.set _t'1 object temporaries)memory).
    { apply certified_set_edge;eapply argument_selected_element;eassumption. }
    argument_same(State f_host_arguments_retain arguments_retain_test arguments_retain_cont empty_env
      (PTree.set _t'1 object temporaries)memory).
    { apply unchanged_store_edge,edge_skip_seq. }
    destruct HEAD as[NULL|[object_block[object_offset OBJECT]]].
    + subst object.
      argument_same(State f_host_arguments_retain Sskip arguments_retain_cont empty_env
        (PTree.set _t'1 Vnullptr temporaries)memory).
      { apply certified_if_edge with(v:=Vnullptr)(b:=false);
          [apply old_expression_value,value_temp;apply PTree.gss|reflexivity]. }
      eapply gateway_effect_pre.
      * apply ADVANCE;repeat rewrite PTree.gso by discriminate;assumption.
      * eapply gateway_argument_context_ambient;exact quiet.
      * intros available current GOOD;apply gateway_argument_context_skip_null;exact GOOD.
    + subst object.
      argument_same(State f_host_arguments_retain(Ssequence(Sset _t'2 arguments_element)arguments_retain_call)
        arguments_retain_cont empty_env(PTree.set _t'1(Vptr object_block object_offset)temporaries)memory).
      { apply certified_if_edge with(v:=Vptr object_block object_offset)(b:=true);
          [apply old_expression_value,value_temp;apply PTree.gss|].
        change ((if Mem.weak_valid_pointer available object_block(Ptrofs.unsigned object_offset)
          then Some true else None)=Some true).
        rewrite(@gateway_argument_addresses World python array offset values processed original available current GOOD
          (Vptr object_block object_offset)object_block object_offset ltac:(eapply nth_error_In;exact SELECTED)eq_refl).
        reflexivity. }
      argument_same(State f_host_arguments_retain(Sset _t'2 arguments_element)
        (Kseq arguments_retain_call arguments_retain_cont)empty_env
        (PTree.set _t'1(Vptr object_block object_offset)temporaries)memory).
      { apply unchanged_store_edge,edge_seq. }
      argument_same(State f_host_arguments_retain Sskip(Kseq arguments_retain_call arguments_retain_cont)empty_env
        (PTree.set _t'2(Vptr object_block object_offset)(PTree.set _t'1(Vptr object_block object_offset)temporaries))memory).
      { apply certified_set_edge;eapply argument_selected_element;
          [exact GOOD|rewrite PTree.gso by discriminate;exact POINTER|
           rewrite PTree.gso by discriminate;exact INDEX|exact BOUND|exact SELECTED]. }
      argument_same(State f_host_arguments_retain arguments_retain_call arguments_retain_cont empty_env
        (PTree.set _t'2(Vptr object_block object_offset)(PTree.set _t'1(Vptr object_block object_offset)temporaries))memory).
      { apply unchanged_store_edge,edge_skip_seq. }
      argument_same(Callstate python_incref_definition[Vptr object_block object_offset]
        (Kcall None f_host_arguments_retain empty_env
          (PTree.set _t'2(Vptr object_block object_offset)(PTree.set _t'1(Vptr object_block object_offset)temporaries))
          arguments_retain_cont)memory).
      { apply actual_arguments_retain_call with(symbol:=symbol);[apply PTree.gss|eauto|exact SYMBOL|exact FUNCTION]. }
      eapply gateway_effect_external.
      * eapply gateway_argument_context_ambient;exact quiet.
      * intros called call_world returned changed next observed AT OPERATION.
        assert(LIVE:python_live(python call_world)(Vptr object_block object_offset)).
        { eapply gateway_argument_context_member;[exact AT|eapply nth_error_In;exact SELECTED|discriminate]. }
        pose proof(gateway_incref_operation backend python runtime(Vptr object_block object_offset)
          called call_world returned changed next observed
          (@gateway_argument_gil World python array offset values processed original called call_world AT)
          (@gateway_argument_valid World python array offset values processed original called call_world AT)LIVE OPERATION)as RETURN.
        exists(argument_ready values(processed++[Vptr object_block object_offset])original);split.
        -- eapply gateway_argument_context_incref;eassumption.
        -- argument_same(State f_host_arguments_retain Sskip arguments_retain_cont empty_env
            (PTree.set _t'2(Vptr object_block object_offset)(PTree.set _t'1(Vptr object_block object_offset)temporaries))changed).
           { apply unchanged_store_edge,edge_returnstate. }
           apply ADVANCE;repeat rewrite PTree.gso by discriminate;assumption.
Qed.

Theorem actual_arguments_retain_path values original memory:
  Forall gateway_argument_pointer values->(length values<=14)%nat->
  gateway_effect_path backend ge(argument_ready values[]original)
    (Callstate(Internal f_host_arguments_retain)[Vptr array offset;Vint(Int.repr(Z.of_nat(length values)))]Kstop memory)
    Vundef(argument_ready values values original).
Proof.
  intros POINTERS BOUND.
  argument_same(State f_host_arguments_retain(fn_body f_host_arguments_retain)Kstop empty_env
    (arguments_retain_parameters(Vptr array offset)(Z.of_nat(length values)))memory).
  { apply function_entry_source_edge,actual_arguments_retain_entry. }
  argument_same(State f_host_arguments_retain(Sset _index(Econst_int Int.zero tint))
    (Kseq arguments_retain_loop Kstop)empty_env
    (arguments_retain_parameters(Vptr array offset)(Z.of_nat(length values)))memory).
  { apply unchanged_store_edge,edge_seq. }
  argument_same(State f_host_arguments_retain Sskip(Kseq arguments_retain_loop Kstop)empty_env
    (PTree.set _index(Vint Int.zero)(arguments_retain_parameters(Vptr array offset)(Z.of_nat(length values))))memory).
  { apply certified_set_edge,old_expression_value;constructor. }
  argument_same(State f_host_arguments_retain arguments_retain_loop Kstop empty_env
    (PTree.set _index(Vint Int.zero)(arguments_retain_parameters(Vptr array offset)(Z.of_nat(length values))))memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  eapply actual_arguments_retain_loop with(remaining:=values)(processed:=[]).
  - reflexivity.
  - exact POINTERS.
  - exact BOUND.
  - unfold arguments_retain_parameters;repeat rewrite PTree.gso by discriminate;apply PTree.gss.
  - unfold arguments_retain_parameters;rewrite PTree.gso by discriminate;apply PTree.gss.
  - apply PTree.gss.
Qed.

Theorem actual_arguments_retain values original before world events returned after next:
  gateway_argument_context python array offset values[]original before world->(length values<=14)%nat->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_arguments_retain)
      [Vptr array offset;Vint(Int.repr(Z.of_nat(length values)))]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  returned=Vundef /\gateway_argument_context python array offset values values original after next /\
    (forall object,In object values->object<>Vnullptr->(0<python_native_strong(python next)object)%nat).
Proof.
  intros INITIAL BOUND RUN.
  destruct(gateway_effect_return_exact backend ge(argument_ready values[]original)
    (Callstate(Internal f_host_arguments_retain)[Vptr array offset;Vint(Int.repr(Z.of_nat(length values)))]Kstop before)
    Vundef(argument_ready values values original)before world events returned after next
    INITIAL ltac:(apply actual_arguments_retain_path;[eapply gateway_argument_context_pointers;exact INITIAL|exact BOUND])RUN)
    as[VALUE FINAL].
  split;[exact VALUE|]. split;[exact FINAL|]. eapply gateway_arguments_independently_rooted;exact FINAL.
Qed.

End ArgumentRoots.
