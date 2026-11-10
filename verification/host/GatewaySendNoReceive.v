(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: The actual sender leaves response-channel bytes unread. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayRuntimeABI GatewayBindings
  GatewayStreamInterface GatewayStreamLayout GatewayReadyInterface GatewayReadyActual GatewayReadContext
  GatewaySendInterface GatewaySendNoReceiveCount GatewaySendSource GatewayReadMemory GatewayBufferReference
  GatewayTransferZero GatewayPrimitiveCalls.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_send_no_receive_source {World Event} (backend : gateway_backend World Event) ge
    (io : Event -> option gateway_native_io) (native : World -> block -> Prop)
    (stable : World -> block -> Z -> Prop) (side : mem -> World -> Prop) : Prop :=
  forall before world stream_block stream_offset initial pointer amount readonly events after next,
    side before world -> native world stream_block ->
    (forall object position, readonly object position -> stable world object position) ->
    gateway_send_inputs before stream_block stream_offset initial readonly ->
    0 <= amount <= Int64.max_unsigned -> gateway_payload_cells readonly pointer amount ->
    stream_descriptor initial <> stream_control initial ->
    gateway_steps backend ge
      (gateway_live (Callstate (Internal f_host_transfer)
        [Vptr stream_block stream_offset; pointer; Vlong (Int64.repr amount); Vint Int.one] Kstop before) world)
      events (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) ->
    gateway_received_bytes io (stream_descriptor initial) events = [].

Section NoReceive.
Context {World Event} (backend : gateway_backend World Event) io native stable discipline thread_errno
  (runtime : gateway_thread_runtime backend io native stable discipline thread_errno).
Variable ge : Clight.genv.
Context (ready_source : gateway_ready_source_producer backend ge io native stable (discipline None)).
Variables ready_symbol save_symbol send_symbol errno_symbol restore_symbol : block.
Hypotheses
  (READY_SYMBOL : Genv.find_symbol ge _host_ready = Some ready_symbol)
  (READY_FUNCTION : Genv.find_funct_ptr ge ready_symbol = Some (Internal f_host_ready))
  (SAVE_SYMBOL : Genv.find_symbol ge _PyEval_SaveThread = Some save_symbol)
  (SAVE_FUNCTION : Genv.find_funct_ptr ge save_symbol = Some gateway_save_thread_definition)
  (SEND_SYMBOL : Genv.find_symbol ge _send = Some send_symbol)
  (SEND_FUNCTION : Genv.find_funct_ptr ge send_symbol = Some gateway_send_definition)
  (ERRNO_SYMBOL : Genv.find_symbol ge ___errno_location = Some errno_symbol)
  (ERRNO_FUNCTION : Genv.find_funct_ptr ge errno_symbol = Some gateway_errno_location_definition)
  (RESTORE_SYMBOL : Genv.find_symbol ge _PyEval_RestoreThread = Some restore_symbol)
  (RESTORE_FUNCTION : Genv.find_funct_ptr ge restore_symbol = Some gateway_restore_thread_definition)
  (DESCRIPTOR : stream_member_layout ge _descriptor 0).

Theorem gateway_send_no_receive_of_ready :
  gateway_send_no_receive_source backend ge io native stable (discipline None).
Proof.
  intros before world stream_block stream_offset initial pointer amount readonly events after next
    SIDE PRIVATE STABLE INPUT AMOUNT PAYLOAD SEPARATE RUN.
  assert (RAW : gateway_read_context native stable discipline None stream_block stream_offset initial
    stream_block stream_offset 0 readonly before world).
  { split; [exact SIDE |]. split; [exact PRIVATE |]. split; [exact PRIVATE |]. split; assumption. }
  destruct (Z.eq_dec amount 0) as [ZERO |NONZERO].
  - subst amount.
    set (context := gateway_owned_buffer_context native stable discipline stream_block stream_block
      stream_offset stream_offset initial 0 readonly before world None).
    assert (INITIAL : context before world).
    { split; [exact RAW |]. split; [apply gateway_buffer_reference_refl |apply gateway_native_reference_refl]. }
    destruct (gateway_actual_empty_transfer backend ge context
      (gateway_owned_buffer_context_ambient backend io native stable discipline thread_errno runtime stream_block stream_block
        stream_offset stream_offset initial 0 readonly before world None)
      (Vptr stream_block stream_offset) pointer Int.one before world events (Vint Int.zero) after next INITIAL RUN)
      as [VALUE [FINAL QUIET]].
    apply gateway_quiet_received_empty; exact QUIET.
  - destruct PAYLOAD as [ZERO |[object [offset [POINTER [BOUND COVER]]]]]; [contradiction |subst pointer].
    destruct (actual_send_no_receive_transfer backend io native stable discipline thread_errno runtime ge ready_source
      stream_block object stream_offset readonly ready_symbol save_symbol send_symbol errno_symbol restore_symbol
      READY_SYMBOL READY_FUNCTION SAVE_SYMBOL SAVE_FUNCTION SEND_SYMBOL SEND_FUNCTION ERRNO_SYMBOL ERRNO_FUNCTION
      RESTORE_SYMBOL RESTORE_FUNCTION DESCRIPTOR events initial offset amount before world after next
      AMOUNT COVER BOUND SEPARATE RAW RUN) as [EMPTY FINAL]; exact EMPTY.
Qed.
End NoReceive.

Theorem gateway_actual_send_no_receive {World Event} (backend : gateway_backend World Event) io
    native stable discipline thread_errno (runtime : gateway_thread_runtime backend io native stable discipline thread_errno) :
  gateway_send_no_receive_source backend (Clight.globalenv prog) io native stable (discipline None).
Proof.
  pose proof (proj1 (Forall_forall _ _) actual_gateway_transfer_functions) as TABLE.
  destruct (TABLE (_host_ready, Internal f_host_ready) ltac:(cbn; tauto)) as (ready_symbol & READY_SYMBOL & READY_FUNCTION).
  destruct (TABLE (_PyEval_SaveThread, gateway_save_thread_definition) ltac:(cbn; tauto)) as (save_symbol & SAVE_SYMBOL & SAVE_FUNCTION).
  destruct (TABLE (___errno_location, gateway_errno_location_definition) ltac:(cbn; tauto)) as (errno_symbol & ERRNO_SYMBOL & ERRNO_FUNCTION).
  destruct (TABLE (_PyEval_RestoreThread, gateway_restore_thread_definition) ltac:(cbn; tauto)) as (restore_symbol & RESTORE_SYMBOL & RESTORE_FUNCTION).
  pose proof (proj1 (Forall_forall _ _) actual_gateway_runtime_functions) as RUNTIME.
  destruct (RUNTIME (_send, gateway_send_definition) ltac:(cbn; tauto)) as (send_symbol & SEND_SYMBOL & SEND_FUNCTION).
  destruct actual_stream_layout as [DESCRIPTOR REST].
  exact (gateway_send_no_receive_of_ready backend io native stable discipline thread_errno runtime (Clight.globalenv prog)
    (gateway_actual_ready_producer backend io native stable discipline thread_errno runtime)
    ready_symbol save_symbol send_symbol errno_symbol restore_symbol READY_SYMBOL READY_FUNCTION SAVE_SYMBOL SAVE_FUNCTION
    SEND_SYMBOL SEND_FUNCTION ERRNO_SYMBOL ERRNO_FUNCTION RESTORE_SYMBOL RESTORE_FUNCTION DESCRIPTOR).
Qed.
