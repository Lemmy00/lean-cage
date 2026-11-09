(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.clock: Prove actual clock argument construction and arithmetic in source. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs
  Errors Ctypes Ctypesdefs Cop Clight.
Require Import IO Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll ErrorNumber.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessAllocation ProcessReturns ProcessPaths.
From LeanCageMain Require Import MainFields.
Import ListNotations.
Open Scope Z_scope.

Definition clock_type := Tstruct _timespec noattr.
Definition clock_env(output:block):env:=PTree.set _t(output,clock_type)empty_env.
Definition clock_temps:=create_undef_temps(fn_temps f_now_ms).
Definition clock_seconds:=Efield(Evar _t clock_type)_tv_sec tlong.
Definition clock_nanos:=Efield(Evar _t clock_type)_tv_nsec tlong.
Definition clock_lower:=Sifthenelse(Etempvar _t'1 tint)
  (Sset _t'2(Econst_int Int.one tint))
  (Ssequence(Sset _t'7 clock_seconds)
    (Sset _t'2(Ecast(Ebinop Olt(Etempvar _t'7 tlong)(Econst_int Int.zero tint)tint)tbool))).
Definition clock_limit:=Ebinop Osub
  (Ebinop Odiv(Econst_long Int64.mone tulong)(Econst_int(Int.repr 1000)tint)tulong)
  (Econst_int Int.one tint)tulong.
Definition clock_upper:=Sifthenelse(Etempvar _t'2 tint)
  (Sset _t'3(Econst_int Int.one tint))
  (Ssequence(Sset _t'6 clock_seconds)
    (Sset _t'3(Ecast(Ebinop Ogt(Ecast(Etempvar _t'6 tlong)tulong)clock_limit tint)tbool))).
Definition clock_check:=Sifthenelse(Etempvar _t'3 tint)
  (Sreturn(Some(Econst_int Int.zero tint)))Sskip.
Definition clock_result_expression:=Ebinop Oadd
  (Ebinop Omul(Ecast(Etempvar _t'4 tlong)tulong)(Econst_int(Int.repr 1000)tint)tulong)
  (Ebinop Odiv(Ecast(Etempvar _t'5 tlong)tulong)(Econst_int(Int.repr 1000000)tint)tulong)tulong.
Definition clock_result:=Ssequence(Sset _t'4 clock_seconds)
  (Ssequence(Sset _t'5 clock_nanos)
    (Sreturn(Some clock_result_expression))).
Definition clock_call:=Scall(Some _t'1)
  (Evar _clock_gettime(Tfunction[tint;tptr clock_type]tint cc_default))
  [Econst_int Int.one tint;Eaddrof(Evar _t clock_type)(tptr clock_type)].
Definition clock_cont output le k:=Kcall(Some _t'1)f_now_ms(clock_env output)le
  (Kseq clock_lower(Kseq clock_upper(Kseq clock_check(Kseq clock_result k)))).

Theorem clock_actual_body:fn_body f_now_ms=
  Ssequence(Ssequence(Ssequence(Ssequence clock_call clock_lower)clock_upper)clock_check)clock_result.
Proof. reflexivity. Qed.

Theorem clock_actual_layout:
  sizeof admission_ge clock_type=16 /\alignof admission_ge clock_type=8 /\
  (exists co,(genv_cenv admission_ge)!_timespec=Some co /\
    field_offset admission_ge _tv_sec(co_members co)=OK(0,Full)) /\
  (exists co,(genv_cenv admission_ge)!_timespec=Some co /\
    field_offset admission_ge _tv_nsec(co_members co)=OK(8,Full)).
Proof.
  split.
  - change(sizeof(prog_comp_env EntrySource.prog)clock_type=16);vm_compute;reflexivity.
  - split.
    + change(alignof(prog_comp_env EntrySource.prog)clock_type=8);vm_compute;reflexivity.
    + split;apply field_lookup_sound.
      * change(match(prog_comp_env EntrySource.prog)!_timespec with Some co=>
          field_offset(prog_comp_env EntrySource.prog)_tv_sec(co_members co)=OK(0,Full)|None=>False end).
        vm_compute;reflexivity.
      * change(match(prog_comp_env EntrySource.prog)!_timespec with Some co=>
          field_offset(prog_comp_env EntrySource.prog)_tv_nsec(co_members co)=OK(8,Full)|None=>False end).
        vm_compute;reflexivity.
Qed.

Theorem clock_actual_symbol:exists object,Genv.find_symbol admission_ge _clock_gettime=Some object /\
  Genv.find_funct admission_ge(Vptr object Ptrofs.zero)=Some process_clock_definition.
Proof. eexists;split;vm_compute;reflexivity. Qed.

Local Opaque EntrySource.prog.

Lemma clock_local_address output le memory:
  expression_value admission_ge(clock_env output)le memory(Eaddrof(Evar _t clock_type)(tptr clock_type))
    (Vptr output Ptrofs.zero).
Proof.
  assert(LOCAL:(clock_env output)!_t=Some(output,clock_type))by(unfold clock_env;apply PTree.gss).
  split;[apply eval_Eaddrof,eval_Evar_local;exact LOCAL|].
  intros other VALUE;inversion VALUE;subst.
  - match goal with LOCATION:eval_lvalue _ _ _ _(Evar _ _) _ _ _|-_=>
      inversion LOCATION;subst;try congruence end;f_equal;congruence.
  - match goal with LOCATION:eval_lvalue _ _ _ _(Eaddrof _ _) _ _ _|-_=>inversion LOCATION end.
Qed.

Lemma clock_field_value output le memory field offset value:
  0<=offset<=8 ->
  (exists co,(genv_cenv admission_ge)!_timespec=Some co /\
    field_offset admission_ge field(co_members co)=OK(offset,Full)) ->
  Mem.load Mint64 memory output offset=Some(Vlong value) ->
  expression_value admission_ge(clock_env output)le memory(Efield(Evar _t clock_type)field tlong)(Vlong value).
Proof.
  intros OFFSET[co[COMPOSITE FIELD]]LOAD;eapply location_read_value with(b:=output)(ofs:=Ptrofs.repr offset).
  - replace(Ptrofs.repr offset)with(Ptrofs.add Ptrofs.zero(Ptrofs.repr offset))by(apply Ptrofs.add_zero_l).
    eapply struct_location_value with(id:=_timespec)(co:=co)(delta:=offset).
    + eapply location_read_value;[apply local_location_value;unfold clock_env;apply PTree.gss|].
      apply deref_loc_copy;reflexivity.
    + reflexivity.
    + exact COMPOSITE.
    + exact FIELD.
  - eapply deref_loc_value;[reflexivity|].
    unfold Mem.loadv;rewrite Ptrofs.unsigned_repr by
      (change Ptrofs.max_unsigned with 18446744073709551615;lia).
    destruct(zle _ _)as[BOUND|];[exact LOAD|].
    exfalso;change Ptrofs.modulus with 18446744073709551616 in *;cbn in *;lia.
Qed.

Theorem clock_function_entry before allocated output:
  Mem.alloc before 0 16=(allocated,output) ->
  function_entry2 admission_ge f_now_ms[]before(clock_env output)clock_temps allocated.
Proof.
  intro ALLOC;constructor.
  - repeat(apply list_norepet_cons;[cbn;intuition discriminate|]);apply list_norepet_nil.
  - repeat(apply list_norepet_cons;[cbn;intuition discriminate|]);apply list_norepet_nil.
  - unfold list_disjoint,var_names;cbn;intros a b A;contradiction.
  - unfold clock_env;cbn[fn_vars f_now_ms];econstructor.
    + pose proof(proj1 clock_actual_layout)as SIZE;unfold clock_type in SIZE.
      rewrite SIZE;exact ALLOC.
    + constructor.
  - reflexivity.
Qed.

Theorem clock_start_to_call before allocated output k:
  Mem.alloc before 0 16=(allocated,output) ->
  store_path admission_ge(fun _=>True)(Callstate(Internal f_now_ms)[]k before)6
    (Callstate process_clock_definition[Vint Int.one;Vptr output Ptrofs.zero]
      (clock_cont output clock_temps k)allocated).
Proof.
  intro ALLOC;destruct clock_actual_symbol as[object[SYMBOL FUNCTION]].
  eapply store_next;[exact I|apply function_entry_source_edge,clock_function_entry;exact ALLOC|].
  rewrite clock_actual_body;admission_route;admission_route;admission_route;admission_route.
  unfold clock_call;eapply store_next;[exact I|eapply certified_call_edge|apply store_done;exact I].
  - reflexivity.
  - apply old_expression_value;eapply value_function.
    + unfold clock_env;rewrite PTree.gso by discriminate;apply PTree.gempty.
    + exact SYMBOL.
    + reflexivity.
  - eapply cons_argument_values;[apply old_expression_value,value_int|reflexivity|].
    eapply cons_argument_values;[apply clock_local_address|reflexivity|apply no_argument_values].
  - exact FUNCTION.
  - reflexivity.
Qed.

Ltac clock_route:=eapply store_next;[reflexivity|apply unchanged_store_edge;WriteAll.structural|].
Ltac clock_set:=eapply store_next;[reflexivity|apply certified_set_edge|].

Lemma clock_long_value ge e le memory word ty:
  expression_value ge e le memory(Econst_long word ty)(Vlong word).
Proof.
  split;[constructor|]. intros other VALUE;inversion VALUE;subst;try reflexivity.
  match goal with LOCATION:eval_lvalue _ _ _ _(Econst_long _ _) _ _ _|-_=>inversion LOCATION end.
Qed.

Lemma clock_limit_value e le memory:
  expression_value admission_ge e le memory clock_limit(Vlong(Int64.repr 18446744073709550)).
Proof.
  unfold clock_limit;eapply binary_expression_value.
  - eapply binary_expression_value;
      [apply clock_long_value|apply old_expression_value,value_int|reflexivity].
  - apply old_expression_value,value_int.
  - reflexivity.
Qed.

Definition clock_error_env le:=PTree.set _t'3(Vint Int.one)
  (PTree.set _t'2(Vint Int.one)(PTree.set _t'1(Vint Int.mone)le)).

Theorem clock_failed_source output le memory k:
  store_path admission_ge(fun current=>current=memory)
    (Returnstate(Vint Int.mone)(clock_cont output le k)memory)9
    (State f_now_ms(Sreturn(Some(Econst_int Int.zero tint)))(Kseq clock_result k)
      (clock_env output)(clock_error_env le)memory).
Proof.
  unfold clock_cont,clock_lower,clock_upper,clock_check,clock_error_env.
  clock_route;clock_route.
  eapply store_next;[reflexivity|apply certified_if_edge with(v:=Vint Int.mone)(b:=true)|].
  - apply old_expression_value,value_temp;apply PTree.gss.
  - reflexivity.
  - clock_set;[apply old_expression_value,value_int|]. clock_route.
    eapply store_next;[reflexivity|apply certified_if_edge with(v:=Vint Int.one)(b:=true)|].
    + apply old_expression_value,value_temp;apply PTree.gss.
    + reflexivity.
    + clock_set;[apply old_expression_value,value_int|]. clock_route.
      eapply store_next;[reflexivity|apply certified_if_edge with(v:=Vint Int.one)(b:=true)|].
      * apply old_expression_value,value_temp;apply PTree.gss.
      * reflexivity.
      * apply store_done;reflexivity.
Qed.

Lemma clock_nonnegative_unsigned word:0<=Int64.signed word ->Int64.unsigned word=Int64.signed word.
Proof.
  intro NONNEGATIVE;rewrite<-(Int64.repr_signed word)at 1.
  apply Int64.unsigned_repr;pose proof(Int64.signed_range word).
  change Int64.max_unsigned with 18446744073709551615.
  change Int64.max_signed with 9223372036854775807 in H;lia.
Qed.

Lemma clock_lower_false memory seconds:0<=Int64.signed seconds ->
  sem_binary_operation admission_ge Olt(Vlong seconds)tlong(Vint Int.zero)tint memory=Some(Vint Int.zero).
Proof.
  intro NONNEGATIVE;change(Some(Val.of_bool(Int64.lt seconds Int64.zero))=Some(Vint Int.zero)).
  unfold Int64.lt;change(Some(Val.of_bool(if zlt(Int64.signed seconds)0 then true else false))=Some(Vint Int.zero)).
  destruct(zlt _ _);[lia|reflexivity].
Qed.

Lemma clock_upper_false memory seconds:0<=Int64.signed seconds<=18446744073709550 ->
  sem_binary_operation admission_ge Ogt(Vlong seconds)tulong
    (Vlong(Int64.repr 18446744073709550))tulong memory=Some(Vint Int.zero).
Proof.
  intro BOUND;change(Some(Val.of_bool(Int64.ltu(Int64.repr 18446744073709550)seconds))=Some(Vint Int.zero)).
  unfold Int64.ltu;rewrite Int64.unsigned_repr by(change Int64.max_unsigned with 18446744073709551615;lia).
  rewrite clock_nonnegative_unsigned by lia.
  destruct(zlt _ _);[lia|reflexivity].
Qed.

Definition clock_success_env le seconds nanos:=
  PTree.set _t'5(Vlong nanos)(PTree.set _t'4(Vlong seconds)
    (PTree.set _t'3(Vint Int.zero)(PTree.set _t'6(Vlong seconds)
      (PTree.set _t'2(Vint Int.zero)(PTree.set _t'7(Vlong seconds)(PTree.set _t'1(Vint Int.zero)le)))))).

Theorem clock_success_source output le memory k seconds nanos:
  0<=Int64.signed seconds<=18446744073709550 ->
  Mem.load Mint64 memory output 0=Some(Vlong seconds) ->
  Mem.load Mint64 memory output 8=Some(Vlong nanos) ->
  store_path admission_ge(fun current=>current=memory)
    (Returnstate(Vint Int.zero)(clock_cont output le k)memory)22
    (State f_now_ms(Sreturn(Some clock_result_expression))k(clock_env output)
      (clock_success_env le seconds nanos)memory).
Proof.
  intros BOUND SECONDS NANOS.
  destruct clock_actual_layout as[_[_[SECONDS_LAYOUT NANOS_LAYOUT]]].
  unfold clock_cont,clock_lower,clock_upper,clock_check,clock_result,clock_success_env.
  clock_route;clock_route.
  eapply store_next;[reflexivity|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
  - apply old_expression_value,value_temp;apply PTree.gss.
  - reflexivity.
  - clock_route;clock_set.
    + apply clock_field_value with(offset:=0);[lia|exact SECONDS_LAYOUT|exact SECONDS].
    + clock_route;clock_set.
      * eapply cast_expression_value.
        -- eapply binary_expression_value.
           ++ apply old_expression_value,value_temp;apply PTree.gss.
           ++ apply old_expression_value,value_int.
           ++ apply clock_lower_false;lia.
        -- reflexivity.
      * clock_route.
        eapply store_next;[reflexivity|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
        -- apply old_expression_value,value_temp;apply PTree.gss.
        -- reflexivity.
        -- clock_route;clock_set.
           ++ apply clock_field_value with(offset:=0);[lia|exact SECONDS_LAYOUT|exact SECONDS].
           ++ clock_route;clock_set.
              ** eapply cast_expression_value.
                 --- eapply binary_expression_value.
                     +++ eapply cast_expression_value;[apply old_expression_value,value_temp;apply PTree.gss|reflexivity].
                     +++ apply clock_limit_value.
                     +++ apply clock_upper_false;exact BOUND.
                 --- reflexivity.
              ** clock_route.
                 eapply store_next;[reflexivity|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
                 --- apply old_expression_value,value_temp;apply PTree.gss.
                 --- reflexivity.
                 --- clock_route;clock_route;clock_set.
                     +++ apply clock_field_value with(offset:=0);[lia|exact SECONDS_LAYOUT|exact SECONDS].
                     +++ clock_route;clock_route;clock_set.
                         *** apply clock_field_value with(offset:=8);[lia|exact NANOS_LAYOUT|exact NANOS].
                         *** clock_route;apply store_done;reflexivity.
Qed.

Definition clock_millis seconds nanos:=
  Int64.add(Int64.mul seconds(Int64.repr 1000))(Int64.divu nanos(Int64.repr 1000000)).

Theorem clock_computed_result output le memory seconds nanos:
  expression_value admission_ge(clock_env output)(clock_success_env le seconds nanos)memory
    clock_result_expression(Vlong(clock_millis seconds nanos)).
Proof.
  unfold clock_result_expression,clock_millis;eapply binary_expression_value.
  - eapply binary_expression_value.
    + eapply cast_expression_value;[apply old_expression_value,value_temp;unfold clock_success_env;WriteAll.lookup|reflexivity].
    + apply old_expression_value,value_int.
    + reflexivity.
  - eapply binary_expression_value.
    + eapply cast_expression_value;[apply old_expression_value,value_temp;unfold clock_success_env;WriteAll.lookup|reflexivity].
    + apply old_expression_value,value_int.
    + reflexivity.
  - reflexivity.
Qed.

Lemma clock_lower_true memory seconds:Int64.signed seconds<0 ->
  sem_binary_operation admission_ge Olt(Vlong seconds)tlong(Vint Int.zero)tint memory=Some(Vint Int.one).
Proof.
  intro NEGATIVE;change(Some(Val.of_bool(Int64.lt seconds Int64.zero))=Some(Vint Int.one)).
  unfold Int64.lt;change(Some(Val.of_bool(if zlt(Int64.signed seconds)0 then true else false))=Some(Vint Int.one)).
  destruct(zlt _ _);[reflexivity|lia].
Qed.

Definition clock_negative_env le seconds:=PTree.set _t'3(Vint Int.one)
  (PTree.set _t'2(Vint Int.one)(PTree.set _t'7(Vlong seconds)(PTree.set _t'1(Vint Int.zero)le))).

Theorem clock_negative_source output le memory k seconds:
  Int64.signed seconds<0 ->Mem.load Mint64 memory output 0=Some(Vlong seconds) ->
  store_path admission_ge(fun current=>current=memory)
    (Returnstate(Vint Int.zero)(clock_cont output le k)memory)12
    (State f_now_ms(Sreturn(Some(Econst_int Int.zero tint)))(Kseq clock_result k)
      (clock_env output)(clock_negative_env le seconds)memory).
Proof.
  intros NEGATIVE SECONDS;destruct clock_actual_layout as[_[_[LAYOUT _]]].
  unfold clock_cont,clock_lower,clock_upper,clock_check,clock_negative_env.
  clock_route;clock_route.
  eapply store_next;[reflexivity|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
  - apply old_expression_value,value_temp;apply PTree.gss.
  - reflexivity.
  - clock_route;clock_set.
    + apply clock_field_value with(offset:=0);[lia|exact LAYOUT|exact SECONDS].
    + clock_route;clock_set.
      * eapply cast_expression_value.
        -- eapply binary_expression_value.
           ++ apply old_expression_value,value_temp;apply PTree.gss.
           ++ apply old_expression_value,value_int.
           ++ apply clock_lower_true;exact NEGATIVE.
        -- reflexivity.
      * clock_route.
        eapply store_next;[reflexivity|apply certified_if_edge with(v:=Vint Int.one)(b:=true)|].
        -- apply old_expression_value,value_temp;apply PTree.gss.
        -- reflexivity.
        -- clock_set;[apply old_expression_value,value_int|]. clock_route.
           eapply store_next;[reflexivity|apply certified_if_edge with(v:=Vint Int.one)(b:=true)|].
           ++ apply old_expression_value,value_temp;apply PTree.gss.
           ++ reflexivity.
           ++ apply store_done;reflexivity.
Qed.

Lemma clock_upper_true memory seconds:18446744073709550<Int64.signed seconds ->
  sem_binary_operation admission_ge Ogt(Vlong seconds)tulong
    (Vlong(Int64.repr 18446744073709550))tulong memory=Some(Vint Int.one).
Proof.
  intro BOUND;change(Some(Val.of_bool(Int64.ltu(Int64.repr 18446744073709550)seconds))=Some(Vint Int.one)).
  unfold Int64.ltu;rewrite Int64.unsigned_repr by(change Int64.max_unsigned with 18446744073709551615;lia).
  rewrite clock_nonnegative_unsigned by lia;destruct(zlt _ _);[reflexivity|lia].
Qed.

Definition clock_overflow_env le seconds:=PTree.set _t'3(Vint Int.one)(PTree.set _t'6(Vlong seconds)
  (PTree.set _t'2(Vint Int.zero)(PTree.set _t'7(Vlong seconds)(PTree.set _t'1(Vint Int.zero)le)))).

Theorem clock_overflow_source output le memory k seconds:
  18446744073709550<Int64.signed seconds ->Mem.load Mint64 memory output 0=Some(Vlong seconds) ->
  store_path admission_ge(fun current=>current=memory)
    (Returnstate(Vint Int.zero)(clock_cont output le k)memory)15
    (State f_now_ms(Sreturn(Some(Econst_int Int.zero tint)))(Kseq clock_result k)
      (clock_env output)(clock_overflow_env le seconds)memory).
Proof.
  intros OVERFLOW SECONDS;destruct clock_actual_layout as[_[_[LAYOUT _]]].
  unfold clock_cont,clock_lower,clock_upper,clock_check,clock_overflow_env.
  clock_route;clock_route.
  eapply store_next;[reflexivity|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
  - apply old_expression_value,value_temp;apply PTree.gss.
  - reflexivity.
  - clock_route;clock_set.
    + apply clock_field_value with(offset:=0);[lia|exact LAYOUT|exact SECONDS].
    + clock_route;clock_set.
      * eapply cast_expression_value.
        -- eapply binary_expression_value.
           ++ apply old_expression_value,value_temp;apply PTree.gss.
           ++ apply old_expression_value,value_int.
           ++ apply clock_lower_false;lia.
        -- reflexivity.
      * clock_route.
        eapply store_next;[reflexivity|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
        -- apply old_expression_value,value_temp;apply PTree.gss.
        -- reflexivity.
        -- clock_route;clock_set.
           ++ apply clock_field_value with(offset:=0);[lia|exact LAYOUT|exact SECONDS].
           ++ clock_route;clock_set.
              ** eapply cast_expression_value.
                 --- eapply binary_expression_value.
                     +++ eapply cast_expression_value;[apply old_expression_value,value_temp;apply PTree.gss|reflexivity].
                     +++ apply clock_limit_value.
                     +++ apply clock_upper_true;exact OVERFLOW.
                 --- reflexivity.
              ** clock_route.
                 eapply store_next;[reflexivity|apply certified_if_edge with(v:=Vint Int.one)(b:=true)|].
                 --- apply old_expression_value,value_temp;apply PTree.gss.
                 --- reflexivity.
                 --- apply store_done;reflexivity.
Qed.
