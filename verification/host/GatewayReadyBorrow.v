(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Nested source helpers preserve the readiness poll allocation. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Integers AST Values Memory.
From HostGateway Require Import GatewayMachine GatewayReadyContext GatewayStreamInterface GatewayReadContext
  GatewayThreadRuntime GatewayBufferReference GatewayScopedBufferRuntime GatewayLocalBorrow GatewayCancellationMemory.
Open Scope Z_scope.

Section ReadyBorrow.
Context {World Event} (backend : gateway_backend World Event)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context (stream_block : block) (stream_offset : ptrofs) (initial : gateway_stream_values)
    (data_block : block) (data_offset : ptrofs) (amount : Z) (readonly : block -> Z -> Prop).
Variables (reference : mem) (owner : World).
Local Definition slice := gateway_ready_slice native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly reference owner.

Lemma gateway_ready_borrow_input item current memory world :
  slice item None current memory world ->
  gateway_read_context native_private stable_readonly discipline None stream_block stream_offset current
    data_block data_offset amount (gateway_local_readonly readonly item 8) memory world.
Proof.
  intros (INPUT & TRANSPORT & PRIVATE & PERMISSIONS & SEPARATE & BUFFER & NATIVE).
  eapply gateway_read_context_local; [exact runtime | exact INPUT | exact PRIVATE | | | |].
  - eapply Mem.perm_valid_block; apply (PERMISSIONS 0); lia.
  - intros position RANGE; eapply Mem.perm_implies; [apply PERMISSIONS; exact RANGE | constructor].
  - intro SAME; subst item; apply (SEPARATE 0); left; reflexivity.
  - intro SAME; subst item; apply (SEPARATE 0); right; left; reflexivity.
Qed.

Theorem gateway_ready_borrow_recovered item current final before world after next :
  slice item None current before world ->
  gateway_read_context native_private stable_readonly discipline None stream_block stream_offset final
    data_block data_offset amount (gateway_local_readonly readonly item 8) after next ->
  gateway_stream_transport_after current final ->
  gateway_buffer_reference (gateway_local_readonly readonly item 8) stream_block data_block before after ->
  gateway_native_reference native_private before world after next ->
  slice item None final after next.
Proof.
  intros (INPUT & TRANSPORT & PRIVATE & PERMISSIONS & SEPARATE & BUFFER & NATIVE)
    BORROWED CHANGE [FRAME BUFFER_PERMISSIONS] OWNERSHIP.
  assert (LIVE : Mem.valid_block before item) by
    (eapply Mem.perm_valid_block; apply (PERMISSIONS 0); lia).
  split.
  - eapply gateway_local_readonly_restrict; exact BORROWED.
  - split.
    + eapply gateway_stream_transport_transitive; eassumption.
    + split.
      * exact (proj2 (OWNERSHIP item LIVE PRIVATE)).
      * split.
        -- intros position RANGE.
           apply (proj1 (gateway_local_permissions_retained readonly item 8 before after FRAME LIVE
             position Cur Freeable RANGE)); apply PERMISSIONS; exact RANGE.
        -- split; [exact SEPARATE |]. split.
           ++ eapply gateway_buffer_reference_transitive; [exact BUFFER |]. split; [|exact BUFFER_PERMISSIONS].
              eapply Mem.unchanged_on_implies; [exact FRAME |]. intros object position HERE VALID; left; exact HERE.
           ++ eapply gateway_native_reference_transitive; eassumption.
Qed.

End ReadyBorrow.
