(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Readiness consumes the actual control and clock source receipts. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayReadyContext GatewayReadyBorrow
  GatewayClock GatewayClockComplete GatewayCancellationComplete GatewayCancellationSuffix GatewayCancellationMemory
  GatewayCancellationEntryBuffers GatewayScopedBufferRuntime GatewayThreadRuntime GatewayStreamInterface
  GatewayStreamLayout GatewayRuntimeABI GatewayReadContext GatewayLocalBorrow GatewayBufferReference.
Import ListNotations.

Section ReadyHelpers.
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

Theorem actual_control_ready_context item current before world events returned after next send_symbol errno_symbol :
  stream_member_layout ge _control 4 -> stream_member_layout ge _cancellation_sent 8 ->
  Genv.find_symbol ge _send = Some send_symbol ->
  Genv.find_funct_ptr ge send_symbol = Some gateway_send_definition ->
  Genv.find_symbol ge ___errno_location = Some errno_symbol ->
  Genv.find_funct_ptr ge errno_symbol = Some gateway_errno_location_definition ->
  slice item None current before world ->
  gateway_steps backend ge
    (gateway_live (Callstate (Internal f_host_control) [Vptr stream_block stream_offset] Kstop before) world)
    events (gateway_live (Returnstate returned Kstop after) next) ->
  exists final, slice item None final after next /\
    gateway_received_bytes io (stream_descriptor initial) events = [].
Proof.
  intros CONTROL CANCEL SEND_SYMBOL SEND_FUNCTION ERRNO_SYMBOL ERRNO_FUNCTION READY RUN.
  pose proof (gateway_ready_borrow_input backend io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner item current before world READY)
    as BORROWED.
  assert (START : control_entry_read_context native_private stable_readonly discipline
    stream_block stream_offset current data_block data_offset amount (gateway_local_readonly readonly item 8)
    before world before world).
  { split; [exact BORROWED |]. split; [apply gateway_buffer_reference_refl | apply gateway_native_reference_refl]. }
  destruct (actual_control_complete backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset current data_block data_offset amount (gateway_local_readonly readonly item 8)
    before world send_symbol errno_symbol CONTROL CANCEL SEND_SYMBOL SEND_FUNCTION ERRNO_SYMBOL ERRNO_FUNCTION
    before world events returned after next START RUN) as [[final [INPUT CHANGE]] [[BUFFER NATIVE] EMPTY]].
  exists final; split.
  - eapply gateway_ready_borrow_recovered; [exact READY | exact INPUT | exact CHANGE | exact BUFFER | exact NATIVE].
  - rewrite <- (proj1 (proj1 (proj2 READY))); exact EMPTY.
Qed.

Theorem actual_clock_ready_context item current before world events returned after next clock_symbol :
  sizeof (genv_cenv ge) clock_sample_type = 16 ->
  Genv.find_symbol ge _clock_gettime = Some clock_symbol ->
  Genv.find_funct_ptr ge clock_symbol = Some clock_gettime_definition ->
  slice item None current before world ->
  gateway_steps backend ge (gateway_live (Callstate (Internal f_host_now) [] Kstop before) world)
    events (gateway_live (Returnstate returned Kstop after) next) ->
  slice item None current after next /\ gateway_received_bytes io (stream_descriptor initial) events = [].
Proof.
  intros SIZE SYMBOL FUNCTION READY RUN.
  pose proof (gateway_ready_borrow_input backend io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner item current before world READY)
    as BORROWED.
  assert (START : gateway_scoped_buffer_history native_private stable_readonly discipline
    stream_block stream_offset current data_block data_offset amount (gateway_local_readonly readonly item 8)
    before world before world).
  { split; [exact BORROWED |]. split; [apply gateway_buffer_reference_refl | apply gateway_native_reference_refl]. }
  destruct (actual_clock_complete backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset current data_block data_offset amount (gateway_local_readonly readonly item 8)
    before world before world events returned after next clock_symbol SIZE SYMBOL FUNCTION START RUN)
    as [[INPUT [BUFFER NATIVE]] EMPTY].
  split.
  - eapply gateway_ready_borrow_recovered; [exact READY | exact INPUT | apply gateway_stream_transport_reflexive |
      exact BUFFER | exact NATIVE].
  - rewrite <- (proj1 (proj1 (proj2 READY))); exact EMPTY.
Qed.

End ReadyHelpers.
