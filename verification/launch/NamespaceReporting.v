(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Execute mandatory result construction and elapsed-time storage before release. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll LibraryMachine ProcessEffects.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine.
From EntryReporting Require Import ResultLayout ResultSource ResultSafety ResultOwnership.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespaceAllocation NamespacePaths NamespaceCaller NamespaceRelease.
Import ListNotations.
Open Scope Z_scope.
Lemma namespace_reporting_environment:namespace_ge=result_ge.
Proof. reflexivity. Qed.
Local Opaque namespace_ge result_ge namespace_symbol.

Definition namespace_admission_copy:=Sassign(Evar _admission result_type)(Evar __res__6 result_type).
Definition namespace_admission_result_cont e le k:=
  Kcall None f_namespace_init e le(Kseq namespace_admission_copy(Kseq(namespace_tail 28)k)).

Theorem namespace_admission_result_call_source e le m k temporary:
  e!_result_of=None ->e!__res__6=Some(temporary,result_type) ->
  exists count,store_path namespace_ge(fun current=>current=m)
    (State f_namespace_init(namespace_tail 27)k e le m)count
    (result_initial temporary 0(Int.repr 5)Int.zero Int.zero Int.zero(namespace_admission_result_cont e le k)m).
Proof.
  intros GLOBAL TEMPORARY;unfold namespace_admission_result_cont,namespace_admission_copy,result_initial,result_args,
    namespace_tail,child_tail;cbn[fn_body].
  eexists;child_route;child_route.
  eapply store_next;[reflexivity|namespace_call _result_of|apply store_done;reflexivity].
  eapply cons_argument_values.
  - apply namespace_local_address;exact TEMPORARY.
  - reflexivity.
  - repeat child_argument;apply no_argument_values.
Qed.

Theorem namespace_admission_result_return_source e le before after k temporary admission:
  e!__res__6=Some(temporary,result_type) ->e!_admission=Some(admission,result_type) ->
  assign_loc namespace_ge result_type before admission Ptrofs.zero Full(Vptr temporary Ptrofs.zero)after ->
  exists count,store_path namespace_ge(fun current=>current=before\/current=after)
    (Returnstate Vundef(namespace_admission_result_cont e le k)before)count
    (State f_namespace_init(namespace_tail 28)k e le after).
Proof.
  intros TEMPORARY ADMISSION COPY;unfold namespace_admission_result_cont,namespace_admission_copy.
  eexists;child_route;child_route.
  eapply store_next;[left;reflexivity|eapply assignment_source_edge|].
  - apply local_location_value;exact ADMISSION.
  - eapply location_read_value;[apply local_location_value;exact TEMPORARY|apply deref_loc_copy;reflexivity].
  - reflexivity.
  - exact COPY.
  - child_route;apply store_done;right;reflexivity.
Qed.

Definition namespace_admission_elapsed:=
  Sassign(Efield(Evar _admission result_type)_elapsed tulong)(Etempvar _t'15 tulong).
Definition namespace_admission_clock_cast:=Sset _t'15(Ecast(Etempvar _t'14 tulong)tulong).
Definition namespace_admission_clock_guard:=Sifthenelse(Eunop Onotbool(Etempvar _t'15 tulong)tint)
  (Sset _bad(Econst_int Int.one tint))Sskip.
Definition namespace_admission_clock_cont e le k:=
  Kcall(Some _t'14)f_namespace_init e le
    (Kseq namespace_admission_clock_cast
      (Kseq namespace_admission_elapsed(Kseq namespace_admission_clock_guard(Kseq(namespace_tail 29)k)))).
Definition namespace_admission_clock_env le milliseconds:=
  PTree.set _t'15(Vlong milliseconds)(PTree.set _t'14(Vlong milliseconds)le).
Definition namespace_checked_clock_env le milliseconds:=
  if Int64.eq milliseconds Int64.zero then PTree.set _bad(Vint Int.one)(namespace_admission_clock_env le milliseconds)
  else namespace_admission_clock_env le milliseconds.

Theorem namespace_admission_clock_call_source e le m k:
  e!_now_ms=None ->exists count,store_path namespace_ge(fun current=>current=m)
    (State f_namespace_init(namespace_tail 28)k e le m)count
    (Callstate(Internal f_now_ms)[](namespace_admission_clock_cont e le k)m).
Proof.
  intro GLOBAL;unfold namespace_admission_clock_cont,namespace_admission_clock_cast,namespace_admission_clock_guard,
    namespace_admission_elapsed,namespace_tail,child_tail;cbn[fn_body].
  eexists;child_route;child_route;child_route;child_route.
  eapply store_next;[reflexivity|namespace_call _now_ms|apply store_done;reflexivity].
  apply no_argument_values.
Qed.

Theorem namespace_admission_clock_store_source e le before after k admission milliseconds:
  e!_admission=Some(admission,result_type) ->
  Mem.store Mint64 before admission 72(Vlong milliseconds)=Some after ->
  store_path namespace_ge(fun current=>current=before\/current=after)
    (Returnstate(Vlong milliseconds)(namespace_admission_clock_cont e le k)before)6
    (State f_namespace_init namespace_admission_clock_guard(Kseq(namespace_tail 29)k)
      e(namespace_admission_clock_env le milliseconds)after).
Proof.
  intros ADMISSION STORE;unfold namespace_admission_clock_cont,namespace_admission_clock_cast,
    namespace_admission_elapsed,namespace_admission_clock_env.
  child_route;child_route;child_set.
  - apply old_expression_value;WriteAll.expression.
  - child_route.
    eapply store_next;[left;reflexivity|eapply assignment_source_edge|].
    + rewrite namespace_reporting_environment.
      eapply current_result_field_location with(offset:=Ptrofs.zero)(delta:=72).
      * eapply location_read_value;[apply local_location_value;exact ADMISSION|apply deref_loc_copy;reflexivity].
      * reflexivity.
      * reflexivity.
    + apply old_expression_value,value_temp;apply PTree.gss.
    + reflexivity.
    + eapply assign_loc_value;[reflexivity|exact STORE].
    + child_route;apply store_done;right;reflexivity.
Qed.


Theorem namespace_admission_clock_return_source e le before after k admission milliseconds:
  e!_admission=Some(admission,result_type) ->
  Mem.store Mint64 before admission 72(Vlong milliseconds)=Some after ->
  exists count,store_path namespace_ge(fun current=>current=before\/current=after)
    (Returnstate(Vlong milliseconds)(namespace_admission_clock_cont e le k)before)count
    (State f_namespace_init(namespace_tail 29)k e(namespace_checked_clock_env le milliseconds)after).
Proof.
  intros ADMISSION STORE;unfold namespace_checked_clock_env.
  destruct(Int64.eq_dec milliseconds Int64.zero)as[ZERO|NONZERO].
  - subst milliseconds;rewrite Int64.eq_true;exists 9%nat.
    eapply store_path_trans with(n:=6%nat).
    + eapply namespace_admission_clock_store_source;eassumption.
    + unfold namespace_admission_clock_guard.
      eapply store_next;[right;reflexivity|apply certified_if_edge with(v:=Vint Int.one)(b:=true)|].
      * apply old_expression_value;unfold namespace_admission_clock_env;WriteAll.expression.
      * reflexivity.
      * child_set;[apply old_expression_value,value_int|].
        child_route;apply store_done;right;reflexivity.
  - rewrite Int64.eq_false by exact NONZERO;exists 8%nat.
    eapply store_path_trans with(n:=6%nat).
    + eapply namespace_admission_clock_store_source;eassumption.
    + unfold namespace_admission_clock_guard.
      eapply store_next;[right;reflexivity|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
      * apply old_expression_value;eapply value_unary.
        -- apply value_temp;unfold namespace_admission_clock_env;apply PTree.gss.
        -- cbn;rewrite Int64.eq_false by exact NONZERO;reflexivity.
      * reflexivity.
      * child_route;apply store_done;right;reflexivity.
Qed.

Theorem failed_clock_latches_bad le:
  (namespace_checked_clock_env le Int64.zero)!_bad=Some(Vint Int.one).
Proof. unfold namespace_checked_clock_env;rewrite Int64.eq_true;apply PTree.gss. Qed.

Theorem release_after_clock_requires_nonzero le milliseconds:
  (namespace_checked_clock_env le milliseconds)!_bad=Some(Vint Int.zero) ->
  milliseconds<>Int64.zero /\le!_bad=Some(Vint Int.zero).
Proof.
  unfold namespace_checked_clock_env;destruct(Int64.eq_dec milliseconds Int64.zero)as[ZERO|NONZERO].
  - subst milliseconds;rewrite Int64.eq_true,PTree.gss;discriminate.
  - rewrite Int64.eq_false by exact NONZERO;unfold namespace_admission_clock_env.
    repeat rewrite PTree.gso by discriminate;intros BAD;auto.
Qed.
