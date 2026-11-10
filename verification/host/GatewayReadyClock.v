(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Readiness uses its same clock call before poll initialization. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewaySource GatewayReadySource GatewayReadyCalls
  GatewayReadyContext GatewayReadyHelpers GatewayReadyTimeout GatewayClock GatewayReadonly GatewayControlPaths
  GatewayOperations GatewayContexts GatewayStreamInterface GatewayReadContext GatewayThreadRuntime
  GatewayPrimitiveCalls GatewayTransferMath GatewayTransferCalls.
Import ListNotations.

Section ReadyClock.
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

Theorem actual_ready_clock_before_item item current temporaries before world events after next clock_symbol :
  sizeof (genv_cenv ge) clock_sample_type = 16 ->
  Genv.find_symbol ge _clock_gettime = Some clock_symbol ->
  Genv.find_funct_ptr ge clock_symbol = Some clock_gettime_definition ->
  temporaries ! _stream = Some (Vptr stream_block stream_offset) ->
  slice item None current before world ->
  gateway_steps backend ge
    (gateway_live (Callstate (Internal f_host_now) [] (ready_clock_cont item temporaries) before) world)
    events (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) ->
  exists prefix suffix final_temporaries memory called_world,
    events = prefix ++ suffix /\
    gateway_received_bytes io (stream_descriptor initial) prefix = [] /\
    final_temporaries ! _stream = Some (Vptr stream_block stream_offset) /\
    slice item None current memory called_world /\
    gateway_steps backend ge
      (gateway_live (Callstate (Internal f_host_now) [] (ready_clock_cont item temporaries) before) world)
      prefix (gateway_live (State f_host_ready Sskip ready_after_timeout_cont
        (ready_environment item) final_temporaries memory) called_world) /\
    gateway_steps backend ge
      (gateway_live (State f_host_ready Sskip ready_after_timeout_cont
        (ready_environment item) final_temporaries memory) called_world)
      suffix (gateway_live (Returnstate (Vint Int.zero) Kstop after) next).
Proof.
  intros SIZE SYMBOL FUNCTION STREAM READY RUN.
  destruct (gateway_return_cut backend ge (Internal f_host_now) [] (ready_clock_cont item temporaries)
    before world events (Returnstate (Vint Int.zero) Kstop after) next ltac:(reflexivity)
    ltac:(cbn [ready_clock_cont gateway_continuation gateway_cont_weight]; lia) RUN)
    as (operation & caller & result & changed & changed_world & EVENTS & OPERATION & CALLER).
  destruct (actual_clock_ready_context backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner
    item current before world operation result changed changed_world clock_symbol SIZE SYMBOL FUNCTION READY OPERATION)
    as [UPDATED EMPTY].
  assert (AMBIENT : gateway_runtime_discipline backend (slice item None current)).
  { apply gateway_ready_slice_ambient with (io := io) (thread_errno := thread_errno); exact runtime. }
  destruct (gateway_prefix_side_cut backend ge (slice item None current) AMBIENT _ _
    (actual_ready_clock_guard_prefix ge item temporaries result changed)
    changed changed_world caller (Vint Int.zero) after next UPDATED CALLER)
    as (prelude & guard & guard_memory & guard_world & CALLER_EVENTS & QUIET & PREFIX & GUARD_READY & GUARD).
  assert (STREAM_GUARD : (ready_clock_values temporaries result) ! _stream = Some (Vptr stream_block stream_offset)).
  { unfold ready_clock_values; rewrite !PTree.gso by discriminate; exact STREAM. }
  destruct (actual_ready_timeout_passed backend ge io (stream_descriptor initial) (slice item None current) AMBIENT
    item (ready_clock_values temporaries result) (Vptr stream_block stream_offset)
    guard_memory guard_world guard after next STREAM_GUARD GUARD_READY GUARD)
    as (passed & suffix & final_temporaries & memory & called_world & GUARD_EVENTS & PASSED_EMPTY &
      FINAL_STREAM & FINAL_READY & PASSED & REST).
  exists (operation ++ prelude ++ passed), suffix, final_temporaries, memory, called_world.
  split; [rewrite EVENTS, CALLER_EVENTS, GUARD_EVENTS; repeat rewrite <- app_assoc; reflexivity |].
  split.
  - repeat rewrite gateway_received_bytes_append.
    rewrite EMPTY, (gateway_quiet_received_empty io (stream_descriptor initial) prelude QUIET), PASSED_EMPTY; reflexivity.
  - split; [exact FINAL_STREAM |]. split; [exact FINAL_READY |]. split; [|exact REST].
    eapply gateway_steps_append.
    + exact (gateway_plug_steps backend ge
        (gateway_live (Callstate (Internal f_host_now) [] Kstop before) world) operation
        (gateway_live (Returnstate result Kstop changed) changed_world)
        (ready_clock_cont item temporaries) ltac:(reflexivity) OPERATION).
    + eapply gateway_steps_append; [exact PREFIX | exact PASSED].
Qed.

End ReadyClock.
