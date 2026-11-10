(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Poll and local stores affect only the actual owned item. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory.
From HostGateway Require Import GatewayMachine GatewayReadyContext GatewayStreamInterface GatewayReadContext
  GatewayReadRegions GatewayReadMemory GatewayThreadRuntime GatewayBufferReference GatewayScopedBufferRuntime.
Open Scope Z_scope.

Section ReadyMemory.
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
Local Definition region := gateway_buffer_scope stream_block data_block readonly.

Theorem gateway_ready_item_output item mode current before world after next output :
  slice item mode current before world -> discipline mode after next ->
  gateway_access_retained native_private stable_readonly before world next ->
  gateway_native_permissions before after item Ptrofs.zero 8 ->
  (forall object position, output object position -> object = item) ->
  gateway_native_frame native_private stable_readonly output world before after ->
  slice item mode current after next.
Proof.
  intros (INPUT & TRANSPORT & PRIVATE & PERMISSIONS & SEPARATE & BUFFER & NATIVE)
    SIDE ACCESS ITEM_PERMISSIONS OUTPUT FRAME.
  assert (LIVE : Mem.valid_block before item) by
    (eapply Mem.perm_valid_block; apply (PERMISSIONS 0); lia).
  assert (PROTECTED : Mem.unchanged_on region before after).
  { eapply gateway_native_frame_restrict; [exact FRAME | |].
    - intros object position [STREAM | [DATA | READONLY]].
      + subst object; left; exact (proj1 (proj2 INPUT)).
      + subst object; left; exact (proj1 (proj2 (proj2 INPUT))).
      + right; apply (proj1 (proj2 (proj2 (proj2 INPUT)))); exact READONLY.
    - intros object position HERE CHANGED; pose proof (OUTPUT object position CHANGED) as SAME; subst object.
      exact (SEPARATE position HERE). }
  split.
  - eapply gateway_read_context_region_preserved; [exact INPUT | exact SIDE | exact ACCESS |].
    eapply Mem.unchanged_on_implies; [exact PROTECTED |].
    intros object position HERE VALID; eapply gateway_buffer_scope_region; exact HERE.
  - split; [exact TRANSPORT |]. split.
    + apply (proj1 ACCESS); assumption.
    + split.
      * intros position RANGE; apply (proj1 (ITEM_PERMISSIONS position Cur Freeable ltac:(cbn; exact RANGE))).
        apply PERMISSIONS; exact RANGE.
      * split; [exact SEPARATE |]. split.
        -- eapply gateway_buffer_reference_transitive; [exact BUFFER |]. split.
           ++ eapply Mem.unchanged_on_implies; [exact PROTECTED |]. intros object position HERE VALID; right; right; exact HERE.
           ++ intros object [STREAM | DATA] position kind permission; subst object;
                apply (Mem.unchanged_on_perm _ _ _ PROTECTED _ position kind permission).
              ** left; reflexivity.
              ** eapply gateway_read_stream_live; exact (proj2 (proj2 (proj2 (proj2 INPUT)))).
              ** right; left; reflexivity.
              ** exact (gateway_read_data_live _ _ _ _ _ _ _ _ (proj2 (proj2 (proj2 (proj2 INPUT))))).
        -- eapply gateway_native_reference_transitive; [exact NATIVE |].
           eapply gateway_native_reference_operation; eassumption.
Qed.

Theorem gateway_ready_local_store item mode current before world after chunk offset value :
  slice item mode current before world ->
  Mem.store chunk before item offset value = Some after -> slice item mode current after world.
Proof.
  intros READY STORE.
  pose proof (proj1 (proj2 (proj2 READY))) as PRIVATE.
  eapply gateway_ready_item_output with (output := fun object _ => object = item).
  - exact READY.
  - eapply gateway_thread_native_store; [exact runtime | exact (proj1 (proj1 READY)) | exact PRIVATE | exact STORE].
  - split; intros; assumption.
  - intros position kind permission RANGE; split;
      [eapply Mem.perm_store_1 | eapply Mem.perm_store_2]; exact STORE.
  - intros; assumption.
  - eapply Mem.store_unchanged_on; [exact STORE |].
    intros position RANGE [CAPABILITY DIFFERENT]; apply DIFFERENT; reflexivity.
Qed.

End ReadyMemory.
