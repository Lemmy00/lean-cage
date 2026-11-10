(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: The same actual readiness iteration executes control before clock. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayReadySource GatewayReadyCalls
  GatewayReadyContext GatewayReadyHelpers GatewayReadonly GatewayTransferCalls GatewayReturnTypes
  GatewayGuardReturn GatewayStreamInterface GatewayStreamLayout GatewayRuntimeABI GatewayReadContext
  GatewayThreadRuntime GatewayPrimitiveCalls GatewayTransferMath GatewayOperations GatewayContexts.
Import ListNotations.

Section ReadyControl.
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
Variables control_symbol send_symbol errno_symbol clock_helper_symbol : block.
Hypotheses
  (CONTROL_SYMBOL : Genv.find_symbol ge _host_control = Some control_symbol)
  (CONTROL_FUNCTION : Genv.find_funct_ptr ge control_symbol = Some (Internal f_host_control))
  (CONTROL : stream_member_layout ge _control 4)
  (CANCEL : stream_member_layout ge _cancellation_sent 8)
  (SEND_SYMBOL : Genv.find_symbol ge _send = Some send_symbol)
  (SEND_FUNCTION : Genv.find_funct_ptr ge send_symbol = Some gateway_send_definition)
  (ERRNO_SYMBOL : Genv.find_symbol ge ___errno_location = Some errno_symbol)
  (ERRNO_FUNCTION : Genv.find_funct_ptr ge errno_symbol = Some gateway_errno_location_definition)
  (CLOCK_SYMBOL : Genv.find_symbol ge _host_now = Some clock_helper_symbol)
  (CLOCK_FUNCTION : Genv.find_funct_ptr ge clock_helper_symbol = Some (Internal f_host_now)).

Theorem actual_ready_control_before_clock item current temporaries before world events after next :
  temporaries ! _stream = Some (Vptr stream_block stream_offset) ->
  slice item None current before world ->
  gateway_steps backend ge
    (gateway_live (State f_host_ready (fn_body f_host_ready) Kstop (ready_environment item) temporaries before) world)
    events (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) ->
  exists prefix suffix final memory called_world,
    events = prefix ++ suffix /\
    gateway_steps backend ge
      (gateway_live (State f_host_ready (fn_body f_host_ready) Kstop (ready_environment item) temporaries before) world)
      prefix (gateway_live (Callstate (Internal f_host_now) []
        (ready_clock_cont item (PTree.set _t'1 (Vint Int.zero) temporaries)) memory) called_world) /\
    slice item None final memory called_world /\
    gateway_received_bytes io (stream_descriptor initial) prefix = [] /\
    gateway_steps backend ge
      (gateway_live (Callstate (Internal f_host_now) []
        (ready_clock_cont item (PTree.set _t'1 (Vint Int.zero) temporaries)) memory) called_world)
      suffix (gateway_live (Returnstate (Vint Int.zero) Kstop after) next).
Proof.
  intros STREAM READY RUN.
  assert (AMBIENT : gateway_runtime_discipline backend (slice item None current)).
  { apply gateway_ready_slice_ambient with (io := io) (thread_errno := thread_errno); exact runtime. }
  destruct (gateway_retained_callback_execution backend ge (slice item None current) AMBIENT
    (State f_host_ready (fn_body f_host_ready) Kstop (ready_environment item) temporaries before)
    world events (Vint Int.zero) after next (Internal f_host_control) [Vptr stream_block stream_offset]
    (ready_control_cont item temporaries)
    ltac:(reflexivity) ltac:(cbn [ready_control_cont gateway_cont_weight]; lia) READY
    (actual_ready_loop_control_path ge item temporaries stream_block stream_offset before control_symbol
      STREAM CONTROL_SYMBOL CONTROL_FUNCTION) RUN)
    as (p & operation & caller & called & called_world & result & changed & changed_world & EVENTS & QUIET &
      PREFIX & CALLED & OPERATION & CALLER).
  pose proof (gateway_actual_int_return backend ge f_host_control _ _ _ _ _ _ _
    actual_host_control_return_profile OPERATION) as TYPE.
  assert (ZERO : result = Vint Int.zero).
  { eapply gateway_successful_checked_result with (function := f_host_ready) (identifier := _t'1)
      (following := Kseq ready_after_control ready_iteration_cont);
      [reflexivity | reflexivity | exact TYPE | exact CALLER]. }
  subst result.
  destruct (actual_control_ready_context backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner
    item current called called_world operation (Vint Int.zero) changed changed_world send_symbol errno_symbol
    CONTROL CANCEL SEND_SYMBOL SEND_FUNCTION ERRNO_SYMBOL ERRNO_FUNCTION CALLED OPERATION)
    as [final [UPDATED EMPTY]].
  assert (AMBIENT_FINAL : gateway_runtime_discipline backend (slice item None final)).
  { apply gateway_ready_slice_ambient with (io := io) (thread_errno := thread_errno); exact runtime. }
  destruct (gateway_retained_call_ready_cut backend ge (slice item None final) AMBIENT_FINAL
    (Internal f_host_now) [] (ready_clock_cont item (PTree.set _t'1 (Vint Int.zero) temporaries))
    (Returnstate (Vint Int.zero) (ready_control_cont item temporaries) changed) changed_world caller
    (Vint Int.zero) after next
    (actual_ready_zero_control_clock_path ge item temporaries changed clock_helper_symbol CLOCK_SYMBOL CLOCK_FUNCTION)
    UPDATED CALLER)
    as (p2 & suffix & memory & clock_world & CALLER_EVENTS & QUIET2 & PREFIX2 & CLOCK_READY & REST).
  exists (p ++ operation ++ p2), suffix, final, memory, clock_world.
  split; [rewrite EVENTS, CALLER_EVENTS; repeat rewrite <- app_assoc; reflexivity |].
  split.
  - rewrite app_assoc. eapply gateway_steps_append; [|exact PREFIX2].
    eapply gateway_call_body_prefix; [reflexivity | exact PREFIX | exact OPERATION].
  - split; [exact CLOCK_READY |]. split; [|exact REST].
    repeat rewrite gateway_received_bytes_append.
    rewrite (gateway_quiet_received_empty io (stream_descriptor initial) p QUIET), EMPTY,
      (gateway_quiet_received_empty io (stream_descriptor initial) p2 QUIET2); reflexivity.
Qed.

End ReadyControl.
