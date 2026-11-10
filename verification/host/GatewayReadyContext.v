(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Readiness retains its actual poll local through thread phases. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Integers AST Values Memory.
From HostGateway Require Import GatewayMachine GatewayReadySource GatewayStreamInterface GatewayReadContext
  GatewayReadMemory GatewayThreadRuntime GatewayBufferReference GatewayTransferRuntime
  GatewayScopedBufferRuntime GatewayReadonlyOperations GatewayOperations GatewayCancellationMemory.
Open Scope Z_scope.

Section ReadyContext.
Context {World Event} (backend : gateway_backend World Event)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context (stream_block : block) (stream_offset : ptrofs) (initial : gateway_stream_values)
    (data_block : block) (data_offset : ptrofs) (amount : Z) (readonly : block -> Z -> Prop).
Variables (reference : mem) (owner : World).

Definition gateway_ready_slice item mode current memory world : Prop :=
    gateway_read_context native_private stable_readonly discipline mode stream_block stream_offset current
      data_block data_offset amount readonly memory world /\ gateway_stream_transport_after initial current /\
    native_private world item /\ Mem.range_perm memory item 0 8 Cur Freeable /\
    (forall position, ~ gateway_buffer_scope stream_block data_block readonly item position) /\
    gateway_buffer_reference readonly stream_block data_block reference memory /\
    gateway_native_reference native_private reference owner memory world.

Definition gateway_ready_context item mode memory world : Prop :=
  exists current, gateway_ready_slice item mode current memory world.

Lemma gateway_ready_item_live item mode memory world :
  gateway_ready_context item mode memory world -> Mem.valid_block memory item.
Proof.
  intros (current & INPUT & TRANSPORT & PRIVATE & PERMISSIONS & REST).
  eapply Mem.perm_valid_block; apply (PERMISSIONS 0); lia.
Qed.

Lemma gateway_ready_slice_no_output item first last current before world after next :
  gateway_ready_slice item first current before world -> discipline last after next ->
  gateway_access_retained native_private stable_readonly before world next ->
  gateway_native_frame native_private stable_readonly gateway_native_no_output world before after ->
  gateway_ready_slice item last current after next.
Proof.
  intros CONTEXT SIDE ACCESS FRAME.
  destruct CONTEXT as (INPUT & TRANSPORT & PRIVATE & PERMISSIONS & SEPARATE & BUFFER & NATIVE).
  assert (LIVE : Mem.valid_block before item) by
    (eapply Mem.perm_valid_block; apply (PERMISSIONS 0); lia).
  split.
  - eapply gateway_read_context_rethread; eassumption.
  - split; [exact TRANSPORT |]. split.
    + apply (proj1 ACCESS); assumption.
    + split.
      * intros position RANGE; eapply Mem.perm_unchanged_on; [exact FRAME | |apply PERMISSIONS; exact RANGE].
        split; [left; exact PRIVATE | unfold gateway_native_no_output; tauto].
      * split; [exact SEPARATE |]. split.
        -- eapply gateway_buffer_reference_transitive; [exact BUFFER |]. split.
           ++ eapply gateway_read_context_readonly_frame; eassumption.
           ++ eapply gateway_context_buffer_permissions; eassumption.
        -- eapply gateway_native_reference_transitive; [exact NATIVE |].
           eapply gateway_native_reference_operation; eassumption.
Qed.

Lemma gateway_ready_no_output item first last before world after next :
  gateway_ready_context item first before world -> discipline last after next ->
  gateway_access_retained native_private stable_readonly before world next ->
  gateway_native_frame native_private stable_readonly gateway_native_no_output world before after ->
  gateway_ready_context item last after next.
Proof.
  intros [current CONTEXT] SIDE ACCESS FRAME; exists current.
  eapply gateway_ready_slice_no_output; eassumption.
Qed.

Lemma gateway_ready_slice_ambient item mode current :
  gateway_runtime_discipline backend (gateway_ready_slice item mode current).
Proof.
  intros before world after next INPUT INTERFERENCE.
  destruct (gateway_thread_ambient _ _ _ _ _ _ runtime mode _ _ _ _ (proj1 (proj1 INPUT)) INTERFERENCE)
    as [SIDE [ACCESS FRAME]].
  eapply gateway_ready_slice_no_output; eassumption.
Qed.

Lemma gateway_ready_context_ambient item mode :
  gateway_runtime_discipline backend (gateway_ready_context item mode).
Proof.
  intros before world after next CONTEXT INTERFERENCE.
  destruct CONTEXT as (current & INPUT & TRANSPORT & PRIVATE & PERMISSIONS & SEPARATE & BUFFER & NATIVE).
  destruct (gateway_thread_ambient _ _ _ _ _ _ runtime mode _ _ _ _ (proj1 INPUT) INTERFERENCE)
    as [SIDE [ACCESS FRAME]].
  eapply gateway_ready_no_output; [|exact SIDE|exact ACCESS|exact FRAME].
  exists current; split; [exact INPUT |]. split; [exact TRANSPORT |]. split; [exact PRIVATE |].
  split; [exact PERMISSIONS |]. split; [exact SEPARATE |]. split; assumption.
Qed.

End ReadyContext.
