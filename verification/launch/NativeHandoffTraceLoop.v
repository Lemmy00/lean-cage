(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: The four actual descriptor operations precede the public stdout operation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffStructure NativeHandoffArguments
  NativeHandoffAllocation NativeHandoffInput NativeHandoffMemory NativeHandoffFormat NativeHandoffDescriptors
  NativeHandoffFlags NativeHandoffEncoding NativeHandoffLoop NativeHandoffStdout NativeHandoffSuccess
  NativeHandoffTracePaths NativeHandoffTraceChecks NativeHandoffTraceEncoding.
Import ListNotations.
Open Scope Z_scope.
Local Opaque handoff_ge handoff_symbol.
Ltac handoff_trace_route := eapply handoff_trace_spec_edge;[apply unchanged_store_edge;WriteAll.structural|].

Fixpoint handoff_trace_descriptor_events words index slots := match slots with
  | O=>[]
  | S rest=>handoff_flag_event(words index)Int.zero Int.zero::handoff_trace_descriptor_events words(index+1)rest
  end.

Theorem handoff_trace_iterations cell input b words failure R tail : forall slots index before le k,
  handoff_trace_failure_safe cell ->
  handoff_private_layout cell input b -> handoff_live_data cell input b words before ->
  0<=index -> index+Z.of_nat slots=4 ->
  le!EntrySource._i=Some(Vint(Int.repr index)) -> le!EntrySource._failure=Some(Vint failure) ->
  handoff_descriptors_checked words 4 ->
  (forall after final,handoff_live_data cell input b words after ->final!EntrySource._failure=Some(Vint failure) ->
    handoff_trace_spec handoff_ge cell R tail(State EntrySource.f_guest Sskip k(handoff_locals_env b)final after)) ->
  handoff_trace_spec handoff_ge cell R(handoff_trace_descriptor_events words index slots++tail)
    (State EntrySource.f_guest handoff_descriptor_iterations k(handoff_locals_env b)le before).
Proof.
  induction slots as[|slots IH];intros index before le k SAFE LAYOUT LIVE LOW END INDEX FAILURE CHECKED NEXT.
  - cbn[Z.of_nat]in END;assert(index=4)by lia;subst index.
    eapply handoff_trace_spec_source;[apply handoff_descriptor_exit_source;exact INDEX|].
    apply NEXT;assumption.
  - assert(BOUND:0<=index<4)by(rewrite Nat2Z.inj_succ in END;lia).
    destruct(CHECKED index BOUND)as[POSITIVE DISTINCT].
    set(loopk:=Kloop1 handoff_descriptor_body handoff_descriptor_increment k).
    destruct(handoff_validation_success(handoff_locals_env b)le before loopk(handoff_handles b)words index
      ltac:(unfold handoff_locals_env;WriteAll.lookup)INDEX BOUND(handoff_live_handles _ _ _ _ _ LIVE)POSITIVE DISTINCT)
      as[count[validated[FRAME PATH]]].
    assert(VALIDINDEX:validated!EntrySource._i=Some(Vint(Int.repr index))).
    { rewrite FRAME by discriminate;exact INDEX. }
    assert(VALIDFAILURE:validated!EntrySource._failure=Some(Vint failure)).
    { rewrite FRAME by discriminate;exact FAILURE. }
    eapply handoff_trace_spec_source;[apply handoff_descriptor_iteration_source with(index:=index);assumption|].
    eapply handoff_trace_spec_source;[exact PATH|].
    cbn[handoff_trace_descriptor_events app].
    refine(handoff_trace_fd cell input b words before validated loopk failure index R
      (handoff_trace_descriptor_events words(index+1)slots++tail)SAFE LAYOUT LIVE BOUND POSITIVE VALIDINDEX VALIDFAILURE _).
    intros after final AFTER FINALINDEX FINALFAILURE.
    eapply handoff_trace_spec_source;[apply handoff_descriptor_increment_source with(index:=index);assumption|].
    apply IH with(index:=index+1);try assumption.
    + lia.
    + rewrite Nat2Z.inj_succ in END;lia.
    + apply PTree.gss.
    + rewrite PTree.gso by discriminate;exact FINALFAILURE.
Qed.

Theorem handoff_trace_descriptors cell input b words before le k failure R tail :
  handoff_trace_failure_safe cell ->
  handoff_private_layout cell input b -> handoff_live_data cell input b words before ->
  le!EntrySource._failure=Some(Vint failure) -> handoff_descriptors_checked words 4 ->
  (forall after final,handoff_live_data cell input b words after ->final!EntrySource._failure=Some(Vint failure) ->
    handoff_trace_spec handoff_ge cell R tail(State EntrySource.f_guest Sskip k(handoff_locals_env b)final after)) ->
  handoff_trace_spec handoff_ge cell R(handoff_trace_descriptor_events words 0 4++tail)
    (State EntrySource.f_guest handoff_descriptor_loop k(handoff_locals_env b)le before).
Proof.
  intros SAFE LAYOUT LIVE FAILURE CHECKED NEXT;rewrite handoff_descriptor_loop_actual at 1;handoff_trace_route.
  eapply handoff_trace_spec_edge;[apply certified_set_edge;apply old_expression_value,value_int|]. handoff_trace_route.
  apply handoff_trace_iterations with(input:=input)(words:=words)(slots:=4%nat)(index:=0)(failure:=failure);
    try assumption;try lia;try reflexivity.
  - apply PTree.gss.
  - rewrite PTree.gso by discriminate;exact FAILURE.
Qed.

Theorem handoff_trace_stdout cell input b words before le k failure R tail :
  handoff_trace_failure_safe cell ->
  handoff_private_layout cell input b -> handoff_live_data cell input b words before ->
  le!EntrySource._failure=Some(Vint failure) ->
  (forall after final,handoff_live_data cell input b words after ->final!EntrySource._failure=Some(Vint failure) ->
    handoff_trace_spec handoff_ge cell R tail(State EntrySource.f_guest guest_argument_tail k(handoff_locals_env b)final after)) ->
  handoff_trace_spec handoff_ge cell R(handoff_flag_event Int.one Int.one Int.zero::tail)
    (State EntrySource.f_guest(guest_tail 10(fn_body EntrySource.f_guest))k(handoff_locals_env b)le before).
Proof.
  intros SAFE LAYOUT LIVE FAILURE NEXT;rewrite handoff_stdout_tail_actual at 1;handoff_trace_route.
  eapply handoff_trace_spec_source.
  - apply handoff_stdout_flags_call_source;apply handoff_nonlocal_binding;cbn;intuition discriminate.
  - apply handoff_trace_spec_checked_flags with(failure:=failure).
    + exact SAFE.
    + apply handoff_nonlocal_binding;cbn;intuition discriminate.
    + apply handoff_nonlocal_binding;cbn;intuition discriminate.
    + discriminate.
    + discriminate.
    + exact FAILURE.
    + intros after FRAME READY;handoff_trace_route;apply NEXT.
      * eapply handoff_live_errno_returned;[exact LAYOUT|exact LIVE|exact FRAME|exact READY].
      * rewrite PTree.gso by discriminate;exact FAILURE.
Qed.
