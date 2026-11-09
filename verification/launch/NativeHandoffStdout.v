(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: The inherited public stdout is marked for closing at the checked source boundary. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine HandoffRegion NativeHandoffStructure
  NativeHandoffArguments NativeHandoffAllocation NativeHandoffInput NativeHandoffMemory
  NativeHandoffFlags NativeHandoffEffects NativeHandoffCount NativeHandoffEncoding.
From LeanCageMainNumber Require Import NumberInitial.
Import ListNotations.
Open Scope Z_scope.
Local Opaque handoff_ge handoff_symbol.

Theorem handoff_stdout_region cell input b words before le k failure R budget :
  handoff_private_layout cell input b -> handoff_live_data cell input b words before ->
  le!EntrySource._failure=Some(Vint failure) ->
  (forall state,handoff_failure_result cell failure state->R state) ->
  (forall after final,
    handoff_live_data cell input b words after -> final!EntrySource._failure=Some(Vint failure) ->
    entry_errno_frame cell before after ->
    handoff_region handoff_ge cell(fun _=>True) R budget
      (State EntrySource.f_guest Sskip k(handoff_locals_env b)final after)) ->
  handoff_region handoff_ge cell(fun _=>True) R (512+budget)
    (State EntrySource.f_guest(guest_phase 10)k(handoff_locals_env b)le before).
Proof.
  intros LAYOUT LIVE FAILURE ACCEPT NEXT.
  eapply handoff_region_weaken with(n:=(2+1+(3+128+budget))%nat);[|lia].
  eapply handoff_region_store_path with(count:=2%nat).
  - eapply number_path_implication with(P:=fun after=>after=before);[intros;exact I|].
    apply handoff_stdout_flags_call_source;apply handoff_nonlocal_binding;cbn;intuition discriminate.
  - apply handoff_flags_region.
    + exact I.
    + exact(handoff_borrowed_errno _ _ _ (handoff_live_borrowed _ _ _ _ _ LIVE)).
    + intros;exact I.
    + intros returned after FRAME ERRNO.
      assert(AFTER:handoff_live_data cell input b words after)
        by(eapply handoff_live_errno_returned;[exact LAYOUT|exact LIVE|exact FRAME|exact ERRNO]).
      set(final:=PTree.set EntrySource._t'18(Vint returned)le).
      assert(FINALFAILURE:final!EntrySource._failure=Some(Vint failure)).
      { unfold final;rewrite PTree.gso by discriminate;exact FAILURE. }
      eapply handoff_region_store_path with(count:=3%nat).
      * eapply number_path_implication with(P:=fun current=>current=after);[intros;exact I|].
        apply handoff_flags_return_source.
      * destruct(Int.eq returned Int.zero)eqn:ZERO.
        -- eapply handoff_region_weaken with(n:=budget);[|lia].
           apply NEXT;assumption.
        -- change(handoff_region handoff_ge cell(fun _=>True) R (128+budget)
             (State EntrySource.f_guest(handoff_error_failure_program EntrySource._t'17(Int.repr 3))
               k(handoff_locals_env b)final after)).
           eapply handoff_region_bind with(n:=128%nat).
           ++ apply handoff_error_failure_region with(failure:=failure).
              ** apply handoff_nonlocal_binding;cbn;intuition discriminate.
              ** apply handoff_nonlocal_binding;cbn;intuition discriminate.
              ** discriminate.
              ** exact FINALFAILURE.
              ** exact ERRNO.
              ** exact I.
           ++ intros endpoint[error[ERROR ENDPOINT]];subst endpoint.
              apply handoff_region_stop;[exact I|]. apply ACCEPT.
              exists(Int.repr 3),error,
                (Kcall None EntrySource.f_guest(handoff_locals_env b)(PTree.set EntrySource._t'17(Vint error)final)k),after.
              split;[reflexivity|]. split;[right;reflexivity|]. split;[exact ERROR|]. split;[exact ERRNO|exact I].
Qed.

Lemma handoff_stdout_tail_actual : guest_tail 10(fn_body EntrySource.f_guest)=
  Ssequence(guest_phase 10)guest_argument_tail.
Proof. reflexivity. Qed.

Theorem handoff_stdout_tail_region cell input b words before le k failure R budget :
  handoff_private_layout cell input b -> handoff_live_data cell input b words before ->
  le!EntrySource._failure=Some(Vint failure) ->
  (forall state,handoff_failure_result cell failure state->R state) ->
  (forall after final,
    handoff_live_data cell input b words after -> final!EntrySource._failure=Some(Vint failure) ->
    entry_errno_frame cell before after ->
    handoff_region handoff_ge cell(fun _=>True) R budget
      (State EntrySource.f_guest guest_argument_tail k(handoff_locals_env b)final after)) ->
  handoff_region handoff_ge cell(fun _=>True) R (514+budget)
    (State EntrySource.f_guest(guest_tail 10(fn_body EntrySource.f_guest))k(handoff_locals_env b)le before).
Proof.
  intros LAYOUT LIVE FAILURE ACCEPT NEXT;rewrite handoff_stdout_tail_actual at 1.
  eapply handoff_region_source_prepend;[exact I|apply unchanged_store_edge;WriteAll.structural|].
  refine(handoff_stdout_region cell input b words before le
    (Kseq guest_argument_tail k)failure R(1+budget)%nat LAYOUT LIVE FAILURE ACCEPT _).
  intros after final AFTER FINALFAILURE FRAME.
  eapply handoff_region_source_prepend;[exact I|apply unchanged_store_edge;WriteAll.structural|].
  apply NEXT;assumption.
Qed.
