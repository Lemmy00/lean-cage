(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Individual SDK operations retain the actual owned readiness record. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Events Clight.
From HostGateway Require Import GatewayMachine GatewayReadyContext GatewayReadyMemory GatewayRuntime
  GatewayRuntimeABI GatewayThreadRuntime GatewayStreamInterface GatewayReadContext GatewayOperations
  GatewayPrimitiveCalls GatewayTransferMath.
Import ListNotations.
Open Scope Z_scope.

Section ReadyOperations.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context (stream_block : block) (stream_offset : ptrofs) (initial : gateway_stream_values)
    (data_block : block) (data_offset : ptrofs) (amount : Z) (readonly : block -> Z -> Prop).
Variables (reference : mem) (owner : World).
Local Definition slice := gateway_ready_slice native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly reference owner.
Local Lemma ambient item mode current : gateway_runtime_discipline backend (slice item mode current).
Proof. apply gateway_ready_slice_ambient with (io := io) (thread_errno := thread_errno); exact runtime. Qed.

Theorem actual_ready_save_operation item current before world events saved after next :
  slice item None current before world ->
  gateway_steps backend ge
    (gateway_live (Callstate gateway_save_thread_definition [] Kstop before) world) events
    (gateway_live (Returnstate saved Kstop after) next) ->
  (exists object offset, saved = Vptr object offset) /\
  slice item (Some saved) current after next /\
  gateway_received_bytes io (stream_descriptor initial) events = [].
Proof.
  intros READY RUN.
  set (output := fun result memory current_world =>
    (exists object offset, result = Vptr object offset) /\ slice item (Some result) current memory current_world).
  assert (POST : forall memory current_world result changed future observed,
    slice item None current memory current_world ->
    gateway_runtime_operation backend gateway_save_thread_definition [] memory current_world result changed future observed ->
    output result changed future /\ io observed = None).
  { intros memory current_world result changed future observed INPUT OPERATION.
    destruct (gateway_save_thread_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ (proj1 (proj1 INPUT)) OPERATION)
      as (POINTER & SIDE & ACCESS & FRAME & IO).
    split; [split; [exact POINTER |] | exact IO].
    eapply gateway_ready_slice_no_output; eassumption. }
  destruct (gateway_actual_primitive_context backend ge _ _ _ _ [] (slice item None current) output
    (ambient item None current)
    ltac:(intros result memory current_world changed future [POINTER INPUT] INTERFERENCE;
      split; [exact POINTER | eapply ambient; eassumption])
    ltac:(intros; apply (proj1 (POST _ _ _ _ _ _ H H0))) before world events saved after next READY RUN)
    as (prefix & suffix & called & called_world & changed & changed_world & observed & EVENTS & PENDING &
      PREFIX & CALLED & OPERATION & OUTPUT & SUFFIX & FINAL).
  destruct FINAL as [POINTER INPUT]; split; [exact POINTER |]. split; [exact INPUT |].
  rewrite (gateway_external_received_projection backend ge io events saved after next prefix suffix changed changed_world
    observed (stream_descriptor initial) EVENTS PENDING SUFFIX).
  unfold gateway_received_event; rewrite (proj2 (POST _ _ _ _ _ _ CALLED OPERATION)); reflexivity.
Qed.

Theorem actual_ready_poll_operation item current saved before world events returned after next :
  slice item (Some saved) current before world ->
  gateway_steps backend ge
    (gateway_live (Callstate gateway_poll_definition [Vptr item Ptrofs.zero; Vlong Int64.one; Vint (Int.repr 100)]
      Kstop before) world) events (gateway_live (Returnstate returned Kstop after) next) ->
  (exists status, returned = Vint status) /\ slice item (Some saved) current after next /\
  gateway_received_bytes io (stream_descriptor initial) events = [].
Proof.
  intros READY RUN.
  set (output := fun result memory current_world =>
    (exists status, result = Vint status) /\ slice item (Some saved) current memory current_world).
  assert (POST : forall memory current_world result changed future observed,
    slice item (Some saved) current memory current_world ->
    gateway_runtime_operation backend gateway_poll_definition
      [Vptr item Ptrofs.zero; Vlong Int64.one; Vint (Int.repr 100)]
      memory current_world result changed future observed -> output result changed future /\ io observed = None).
  { intros memory current_world result changed future observed INPUT OPERATION.
    assert (POINTER : gateway_native_pointer memory item Ptrofs.zero 8 Writable).
    { split; [lia |]. split; [vm_compute; discriminate |]. split.
      - eapply Mem.perm_valid_block; apply (proj1 (proj2 (proj2 (proj2 INPUT))) 0); lia.
      - intros position RANGE; eapply Mem.perm_implies;
          [apply (proj1 (proj2 (proj2 (proj2 INPUT)))); exact RANGE | constructor]. }
    destruct (gateway_poll_operation _ _ _ _ _ _ runtime saved memory current_world item Ptrofs.zero result changed future
      observed (proj1 (proj1 INPUT)) (proj1 (proj2 (proj2 INPUT))) POINTER OPERATION)
      as (status & VALUE & SIDE & ACCESS & PERMISSIONS & FRAME & IO).
    split; [split; [exists status; exact VALUE |] | exact IO].
    eapply gateway_ready_item_output; [exact INPUT | exact SIDE | exact ACCESS | exact PERMISSIONS | | exact FRAME].
    intros object position [SAME RANGE]; exact SAME. }
  destruct (gateway_actual_primitive_context backend ge _ _ _ _ _ (slice item (Some saved) current) output
    (ambient item (Some saved) current)
    ltac:(intros result memory current_world changed future [TYPE INPUT] INTERFERENCE;
      split; [exact TYPE | eapply ambient; eassumption])
    ltac:(intros; apply (proj1 (POST _ _ _ _ _ _ H H0))) before world events returned after next READY RUN)
    as (prefix & suffix & called & called_world & changed & changed_world & observed & EVENTS & PENDING &
      PREFIX & CALLED & OPERATION & OUTPUT & SUFFIX & FINAL).
  destruct FINAL as [TYPE INPUT]; split; [exact TYPE |]. split; [exact INPUT |].
  rewrite (gateway_external_received_projection backend ge io events returned after next prefix suffix changed changed_world
    observed (stream_descriptor initial) EVENTS PENDING SUFFIX).
  unfold gateway_received_event; rewrite (proj2 (POST _ _ _ _ _ _ CALLED OPERATION)); reflexivity.
Qed.

End ReadyOperations.
