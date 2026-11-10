(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual control send retains the same caller buffers. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Events Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayCancellation GatewayCancellationRuntime
  GatewayCancellationSend GatewayCancellationBuffers GatewayThreadRuntime GatewayStreamInterface
  GatewayReadContext GatewayRuntime GatewayRuntimeABI GatewayOperations GatewayReadonly GatewayPrimitiveCalls.
Import ListNotations.
Open Scope Z_scope.

Section CancellationSendBuffers.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context (stream_block : block) (stream_offset : ptrofs) (initial : gateway_stream_values)
    (data_block : block) (data_offset : ptrofs) (amount : Z) (readonly : block -> Z -> Prop).
Variables (reference : mem) (owner : World).
Local Definition command_context := cancellation_command_context native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly.
Local Definition history := control_buffer_history native_private stream_block data_block readonly reference owner.

Definition control_send_buffer_context command memory world : Prop :=
  command_context command memory world /\ history memory world.

Lemma control_send_buffer_ambient command : gateway_runtime_discipline backend (control_send_buffer_context command).
Proof.
  intros before world after next [CONTEXT HISTORY] INTERFERENCE; split.
  - eapply cancellation_command_ambient; [exact runtime | exact CONTEXT | exact INTERFERENCE].
  - destruct (gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _
      (proj1 (proj1 (proj1 CONTEXT))) INTERFERENCE) as [SIDE [ACCESS FRAME]].
    eapply control_buffer_history_operation; [exact (proj1 (proj1 CONTEXT)) | exact ACCESS | exact FRAME | exact HISTORY].
Qed.

Lemma control_command_frame command before world after next :
  command_context command before world -> discipline None after next ->
  gateway_access_retained native_private stable_readonly before world next ->
  gateway_native_frame native_private stable_readonly gateway_native_no_output world before after ->
  command_context command after next.
Proof.
  intros [CONTEXT BYTE] SIDE ACCESS FRAME; split.
  - eapply control_context_preserved; eassumption.
  - eapply Mem.loadbytes_unchanged_on; [exact FRAME | | exact BYTE].
    intros position RANGE; split.
    + left; exact (proj1 (proj2 CONTEXT)).
    + unfold gateway_native_no_output; tauto.
Qed.

Theorem actual_cancellation_send_buffers command before world events returned after next :
  control_send_buffer_context command before world ->
  gateway_steps backend ge
    (gateway_live (Callstate gateway_send_definition
      [Vint (stream_control initial); Vptr command Ptrofs.zero; Vlong Int64.one;
        Vint (Int.repr 16384)] Kstop before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists count,
    -1 <= count <= 1 /\ returned = Vlong (Int64.repr count) /\
    control_send_buffer_context command after next /\
    gateway_received_bytes io (stream_descriptor initial) events = [].
Proof.
  intros READY RUN.
  destruct (gateway_external_operation_of_run backend ge _ _ _ _ _
    before world events returned after next RUN)
    as (prefix & suffix & called & called_world & changed & changed_world & observed &
      EVENTS & PENDING & PREFIX & OPERATION & SUFFIX).
  assert (CALLED : control_send_buffer_context command called called_world).
  { eapply gateway_pending_run_ready with (source := Callstate gateway_send_definition
      [Vint (stream_control initial); Vptr command Ptrofs.zero; Vlong Int64.one;
        Vint (Int.repr 16384)] Kstop before);
      [apply control_send_buffer_ambient | exact READY | exact PENDING | exact PREFIX]. }
  destruct CALLED as [CONTEXT HISTORY].
  destruct (gateway_send_operation _ _ _ _ _ _ runtime None called called_world
    (stream_control initial) command Ptrofs.zero 1 returned changed changed_world observed
    (proj1 (proj1 (proj1 CONTEXT))) (or_introl (proj1 (proj2 (proj1 CONTEXT)))) ltac:(lia)
    (cancellation_command_pointer native_private stable_readonly discipline stream_block stream_offset initial
      data_block data_offset amount readonly command called called_world CONTEXT) OPERATION)
    as (count & bytes & COUNT & RETURNED & LENGTH & LOAD & IO & SIDE & ACCESS & FRAME).
  assert (CHANGED : control_send_buffer_context command changed changed_world).
  { split.
    - eapply control_command_frame; eassumption.
    - eapply control_buffer_history_operation; [exact (proj1 (proj1 CONTEXT)) | exact ACCESS | exact FRAME | exact HISTORY]. }
  assert (FINAL : control_send_buffer_context command after next).
  { eapply gateway_readonly_run_side with (source := Returnstate returned Kstop changed);
      [apply control_send_buffer_ambient | exact I | exact CHANGED | exact SUFFIX]. }
  exists count; split; [exact COUNT |]. split; [exact RETURNED |]. split; [exact FINAL |].
  rewrite (gateway_external_received_projection backend ge io events returned after next
    prefix suffix changed changed_world observed (stream_descriptor initial) EVENTS PENDING SUFFIX).
  unfold gateway_received_event; rewrite IO; reflexivity.
Qed.

End CancellationSendBuffers.
