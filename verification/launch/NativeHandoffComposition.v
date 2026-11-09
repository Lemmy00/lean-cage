(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Compose actual allocation, setup guards, encoding and argument-table source regions. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps Library WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine HandoffRegion NativeHandoffStructure
  NativeHandoffArguments NativeHandoffAllocation NativeHandoffInput NativeHandoffInitial NativeHandoffMemory
  NativeHandoffEncoding NativeHandoffLoop NativeHandoffStdout.
From LeanCageMainNumber Require Import NumberMemory NumberMath.
Import ListNotations.
Open Scope Z_scope.
Local Opaque handoff_ge handoff_symbol.

Lemma handoff_region_relax ge cell P Q R S n state :
  handoff_region ge cell P R n state ->
  (forall m,P m->Q m) -> (forall endpoint,R endpoint->S endpoint) ->
  handoff_region ge cell Q S n state.
Proof.
  revert state;induction n as[|n IH];intros state CERT MEMORY RESULT;
    inversion CERT as[count current GOOD END|count current GOOD PROGRESS CASES];subst.
  - apply handoff_region_stop;[apply MEMORY;exact GOOD|apply RESULT;exact END].
  - apply handoff_region_stop;[apply MEMORY;exact GOOD|apply RESULT;exact END].
  - eapply handoff_region_next;[apply MEMORY;exact GOOD|exact PROGRESS|].
    intros event target STEP;destruct(CASES _ _ STEP)as[WAIT|[DEAD|[next[TARGET[ADV[IMAGE NEXT]]]]]];[left;exact WAIT| |].
    + right;left;destruct DEAD as[after[TARGET[GOODAFTER NOIMAGE]]];exists after;auto.
    + right;right;exists next;split;[exact TARGET|]. split;[exact ADV|]. split;[exact IMAGE|].
      apply IH;assumption.
Qed.

Theorem handoff_guest_initial_region cell input before input_fd output_fd errors_fd failure k R budget :
  handoff_borrowed_input cell before input ->
  (forall state,handoff_failure_result cell failure state->R state) ->
  (forall b after final,
    handoff_private_layout cell input b ->
    handoff_live_data cell input b(handoff_original_words input_fd output_fd errors_fd failure)after ->
    final!EntrySource._failure=Some(Vint failure) ->
    handoff_borrowed_mode_bytes input=handoff_normal_bytes ->
    100000<=Int.unsigned(handoff_borrowed_uid input)<=100999 ->
    handoff_region handoff_ge cell(fun _=>True) R budget
      (State EntrySource.f_guest(guest_tail 6(fn_body EntrySource.f_guest))k(handoff_locals_env b)final after)) ->
  handoff_region handoff_ge cell(fun _=>True) R (128+budget)
    (Callstate(Internal EntrySource.f_guest)[Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k before).
Proof.
  intros INPUT ACCEPT NEXT.
  destruct(handoff_entry_allocates before input_fd output_fd errors_fd failure k)
    as[b[allocated[ENTRY[ALLOC OWN]]]].
  destruct(handoff_layout_allocated cell input before b allocated INPUT ALLOC)as[LAYOUT LOCALOWN].
  pose proof(handoff_borrowed_allocated cell input before b allocated INPUT ALLOC)as BORROWED.
  set(original:=handoff_parameter_env input_fd output_fd errors_fd failure).
  destruct(handoff_parameter_bindings input_fd output_fd errors_fd failure)as[PARAMINPUT[PARAMOUTPUT[PARAMERRORS PARAMFAILURE]]].
  assert(RUNUIDSEPARATE:handoff_symbol EntrySource._run_uid<>handoff_handles b).
  { destruct(handoff_private_object cell input b(handoff_handles b)16 LAYOUT
      ltac:(unfold handoff_objects;cbn;auto))as[_ SHARED].
    intros SAME;apply SHARED;rewrite <- SAME;apply handoff_borrowed_global_member;cbn;auto. }
  assert(NORMAL:c_string allocated handoff_normal_address handoff_normal_bytes).
  { pose proof(handoff_borrowed_literals _ _ _ BORROWED)as LITERALS;inversion LITERALS;subst;exact H1. }
  eapply handoff_region_weaken with(n:=(1+64+budget)%nat);[|lia].
  eapply handoff_region_source_prepend;[exact I|exact ENTRY|].
  eapply handoff_region_bind with(n:=64%nat).
  - eapply handoff_region_relax.
    + apply handoff_initial_region with(input:=input_fd)(output:=output_fd)(errors:=errors_fd)
        (failure:=failure)(uid:=handoff_borrowed_uid input)(mode:=handoff_borrowed_mode input)
        (modebytes:=handoff_borrowed_mode_bytes input).
      * exact PARAMINPUT.
      * exact PARAMOUTPUT.
      * exact PARAMERRORS.
      * exact PARAMFAILURE.
      * apply handoff_local_object with(b:=b)(size:=16);[exact LOCALOWN|unfold handoff_objects;cbn;auto].
      * exact RUNUIDSEPARATE.
      * exact(handoff_borrowed_uid_load _ _ _ BORROWED).
      * exact(handoff_borrowed_mode_load _ _ _ BORROWED).
      * exact(handoff_borrowed_mode_text _ _ _ BORROWED).
      * exact NORMAL.
    + intros;exact I.
    + exact(fun endpoint LEAF=>LEAF).
  - intros endpoint[[after[continuation[ENDPOINT[FRAME CALL]]]]|[after[value[ENDPOINT[STORES[MODE[ZERO UID]]]]]]];subst endpoint.
    + assert(ERRNO:entry_errno_ready cell after).
      { eapply handoff_errno_unchanged;[|exact(handoff_borrowed_errno _ _ _ BORROWED)].
        eapply Mem.unchanged_on_implies;[exact FRAME|].
        pose proof(proj1(handoff_private_object cell input b(handoff_handles b)16 LAYOUT
          ltac:(unfold handoff_objects;cbn;auto)))as HANDLETLS.
        intros object pos SAME VALID;subst object;congruence. }
      apply handoff_region_stop;[exact I|]. apply ACCEPT.
      exists Int.one,(Int.repr 22),continuation,after;split;[reflexivity|].
      split;[left;reflexivity|]. split;[change(1<=22<=4095);lia|]. split;assumption.
    + rewrite PARAMINPUT,PARAMOUTPUT,PARAMERRORS in STORES.
      apply NEXT with(b:=b).
      * exact LAYOUT.
      * apply handoff_live_initialized with(before:=allocated);assumption.
      * rewrite handoff_initial_temps_preserved by(cbn;intuition discriminate);exact PARAMFAILURE.
      * exact MODE.
      * exact UID.
Qed.
