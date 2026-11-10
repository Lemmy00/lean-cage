(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Restrict write authority and derive descriptor retention. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Integers Values Memory.
From HostGateway Require Import GatewayMachine GatewayThreadRuntime GatewayProtectedMemory.
Open Scope Z_scope.

Definition gateway_protected_discipline {World} (discipline : option val -> mem -> World -> Prop)
    native protected immutable snapshot mode memory world : Prop :=
  discipline mode memory world /\ gateway_protected_memory native protected immutable snapshot memory world.

Section ProtectedThreads.
Context {World Event} (backend : gateway_backend World Event) io native stable discipline thread_errno
  (runtime : gateway_thread_runtime backend io native stable discipline thread_errno)
  (protected immutable : block -> Prop) (snapshot : mem).
Let restricted := gateway_protected_native native protected immutable.
Let side := gateway_protected_discipline discipline native protected immutable snapshot.

Local Lemma protected_quiet mode before world after next :
  side mode before world -> discipline mode after next ->
  gateway_access_retained native stable before world next ->
  gateway_native_frame native stable gateway_native_no_output world before after -> side mode after next.
Proof.
  intros [SIDE STATE] NEXT ACCESS FRAME; split; [exact NEXT |].
  eapply gateway_protected_effect; [exact STATE |exact ACCESS |exact FRAME |].
  intros; unfold gateway_native_no_output; tauto.
Qed.

Local Lemma protected_written mode before world after next object offset amount output :
  side mode before world -> discipline mode after next ->
  gateway_access_retained native stable before world next ->
  gateway_native_frame native stable output world before after ->
  restricted world object -> gateway_native_pointer before object offset amount Writable -> 0 < amount ->
  (forall candidate position, output candidate position -> candidate = object) -> side mode after next.
Proof.
  intros [SIDE STATE] NEXT ACCESS FRAME OWNED POINTER POSITIVE OUTPUT; split; [exact NEXT |].
  eapply gateway_protected_effect; [exact STATE |exact ACCESS |exact FRAME |].
  intros candidate position GUARDED WRITTEN.
  pose proof (OUTPUT candidate position WRITTEN) as SAME; subst candidate.
  eapply gateway_protected_pointer_separate; eassumption.
Qed.

Theorem gateway_protected_threads : gateway_thread_runtime backend io restricted stable side thread_errno.
Proof.
  constructor.
  - intros mode before world after next SIDE OPERATION.
    destruct (gateway_thread_ambient _ _ _ _ _ _ runtime mode before world after next (proj1 SIDE) OPERATION)
      as [NEXT [ACCESS FRAME]].
    split; [eapply protected_quiet; eassumption |].
    split; [apply gateway_protected_access; exact ACCESS |apply gateway_protected_frame; exact FRAME].
  - intros mode before world object [SIDE STATE] FRESH; split.
    + eapply gateway_thread_fresh_native; eassumption.
    + intro GUARDED; exfalso; apply FRESH; eapply gateway_protected_live; eassumption.
  - intros mode before world object position [SIDE STATE] [OWNED EXCLUDED].
    eapply gateway_thread_native_stable; eassumption.
  - intros mode before world after object low high [SIDE STATE] ALLOC; split.
    + eapply gateway_thread_native_alloc; eassumption.
    + eapply gateway_protected_alloc; eassumption.
  - intros mode before world after object low high [SIDE STATE] OWNED FREE; split.
    + eapply gateway_thread_native_free; [exact runtime |exact SIDE |exact (proj1 OWNED) |exact FREE].
    + eapply gateway_protected_free; eassumption.
  - intros mode before world after object offset chunk value [SIDE STATE] OWNED STORE; split.
    + eapply gateway_thread_native_store; [exact runtime |exact SIDE |exact (proj1 OWNED) |exact STORE].
    + eapply gateway_protected_store; eassumption.
  - intros before world result after next observed SIDE OPERATION.
    destruct (gateway_save_thread_operation _ _ _ _ _ _ runtime before world result after next observed
      (proj1 SIDE) OPERATION) as [POINTER [NEXT [ACCESS [FRAME QUIET]]]].
    split; [exact POINTER |]. split.
    + split; [exact NEXT |]. eapply gateway_protected_effect;
        [exact (proj2 SIDE) |exact ACCESS |exact FRAME |intros; unfold gateway_native_no_output; tauto].
    + split; [apply gateway_protected_access; exact ACCESS |].
      split; [apply gateway_protected_frame; exact FRAME |exact QUIET].
  - intros saved before world result after next observed SIDE OPERATION.
    destruct (gateway_restore_thread_operation _ _ _ _ _ _ runtime saved before world result after next observed
      (proj1 SIDE) OPERATION) as [NEXT [ACCESS [FRAME QUIET]]].
    split.
    + split; [exact NEXT |]. eapply gateway_protected_effect;
        [exact (proj2 SIDE) |exact ACCESS |exact FRAME |intros; unfold gateway_native_no_output; tauto].
    + split; [apply gateway_protected_access; exact ACCESS |].
      split; [apply gateway_protected_frame; exact FRAME |exact QUIET].
  - intros mode before world result after next observed SIDE OPERATION.
    destruct (gateway_errno_location_operation _ _ _ _ _ _ runtime mode before world result after next observed
      (proj1 SIDE) OPERATION) as [object [offset [RESULT [POINTER [LOAD [FOREIGN [UNSTABLE [NEXT [ACCESS [FRAME QUIET]]]]]]]]]].
    exists object, offset; split; [exact RESULT |]. split; [exact POINTER |]. split; [exact LOAD |]. split.
    + intro OWNED; apply FOREIGN; exact (proj1 OWNED).
    + split; [exact UNSTABLE |]. split; [eapply protected_quiet; eassumption |].
      split; [apply gateway_protected_access; exact ACCESS |].
      split; [apply gateway_protected_frame; exact FRAME |exact QUIET].
  - intros before world object offset result after next observed SIDE OWNED POINTER OPERATION.
    destruct (gateway_clock_operation _ _ _ _ _ _ runtime before world object offset result after next observed
      (proj1 SIDE) (proj1 OWNED) POINTER OPERATION)
      as [status [RESULT [TIME [NEXT [ACCESS [PERMISSIONS [FRAME QUIET]]]]]]].
    exists status; split; [exact RESULT |]. split; [exact TIME |]. split.
    + eapply protected_written; [exact SIDE |exact NEXT |exact ACCESS |exact FRAME |exact OWNED |exact POINTER |lia |].
      intros candidate position [SAME RANGE]; exact SAME.
    + split; [apply gateway_protected_access; exact ACCESS |]. split; [exact PERMISSIONS |].
      split; [apply gateway_protected_frame; exact FRAME |exact QUIET].
  - intros saved before world object offset result after next observed SIDE OWNED POINTER OPERATION.
    destruct (gateway_poll_operation _ _ _ _ _ _ runtime saved before world object offset result after next observed
      (proj1 SIDE) (proj1 OWNED) POINTER OPERATION)
      as [status [RESULT [NEXT [ACCESS [PERMISSIONS [FRAME QUIET]]]]]].
    exists status; split; [exact RESULT |]. split.
    + eapply protected_written; [exact SIDE |exact NEXT |exact ACCESS |exact FRAME |exact OWNED |exact POINTER |lia |].
      intros candidate position [SAME RANGE]; exact SAME.
    + split; [apply gateway_protected_access; exact ACCESS |]. split; [exact PERMISSIONS |].
      split; [apply gateway_protected_frame; exact FRAME |exact QUIET].
  - intros mode before world descriptor object offset amount result after next observed SIDE OWNED BOUND POINTER OPERATION.
    assert (ORIGINAL : native world object \/ forall position,
      Ptrofs.unsigned offset <= position < Ptrofs.unsigned offset + amount -> stable world object position).
    { destruct OWNED as [PRIVATE |READONLY]; [left; exact (proj1 PRIVATE) |right; exact READONLY]. }
    destruct (gateway_send_operation _ _ _ _ _ _ runtime mode before world descriptor object offset amount result after next observed
      (proj1 SIDE) ORIGINAL BOUND POINTER OPERATION)
      as [count [bytes [BOUND_COUNT [RESULT [SIZE [BYTES [EVENT [NEXT [ACCESS FRAME]]]]]]]]].
    exists count, bytes; split; [exact BOUND_COUNT |]. split; [exact RESULT |]. split; [exact SIZE |].
    split; [exact BYTES |]. split; [exact EVENT |]. split; [eapply protected_quiet; eassumption |].
    split; [apply gateway_protected_access; exact ACCESS |apply gateway_protected_frame; exact FRAME].
  - intros saved before world descriptor object offset amount result after next observed SIDE OWNED BOUND POINTER OPERATION.
    destruct (gateway_receive_operation _ _ _ _ _ _ runtime saved before world descriptor object offset amount result after next observed
      (proj1 SIDE) (proj1 OWNED) BOUND POINTER OPERATION)
      as [count [bytes [BOUND_COUNT [RESULT [SIZE [BYTES [EVENT [NEXT [ACCESS [PERMISSIONS FRAME]]]]]]]]]].
    exists count, bytes; split; [exact BOUND_COUNT |]. split; [exact RESULT |]. split; [exact SIZE |].
    split; [exact BYTES |]. split; [exact EVENT |]. split.
    + eapply protected_written; [exact SIDE |exact NEXT |exact ACCESS |exact FRAME |exact OWNED |exact POINTER |lia |].
      intros candidate position [SAME RANGE]; exact SAME.
    + split; [apply gateway_protected_access; exact ACCESS |]. split; [exact PERMISSIONS |].
      apply gateway_protected_frame; exact FRAME.
  - intros before world result after next observed SIDE OPERATION.
    destruct (gateway_check_signals_operation _ _ _ _ _ _ runtime before world result after next observed
      (proj1 SIDE) OPERATION) as [status [RESULT [SUCCESS QUIET]]].
    exists status; split; [exact RESULT |]. split; [|exact QUIET].
    intro ZERO; destruct (SUCCESS ZERO) as [NEXT [ACCESS FRAME]].
    split; [eapply protected_quiet; eassumption |].
    split; [apply gateway_protected_access; exact ACCESS |apply gateway_protected_frame; exact FRAME].
  - intros mode before world pointer result after next observed SIDE OPERATION.
    destruct (gateway_volatile_int_load _ _ _ _ _ _ runtime mode before world pointer result after next observed
      (proj1 SIDE) OPERATION) as [RESULT [NEXT [ACCESS [FRAME QUIET]]]].
    split; [exact RESULT |]. split; [eapply protected_quiet; eassumption |].
    split; [apply gateway_protected_access; exact ACCESS |].
    split; [apply gateway_protected_frame; exact FRAME |exact QUIET].
Qed.
End ProtectedThreads.
