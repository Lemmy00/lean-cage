(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Compose the actual clock source and its separated scope. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine StoreSteps ClightSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayClock GatewayClockRuntime GatewayClockBuffers
  GatewayClockBufferOperation GatewayThreadRuntime GatewayStreamInterface GatewayScopedBufferRuntime
  GatewayLocalRuntime GatewayScopedMemory GatewayReadContext GatewayBufferReference GatewayReadonly
  GatewayRuntimeCuts GatewayOperations GatewayFrames GatewayPrimitiveCalls GatewayGuardObservation
  GatewayTransferMath GatewayContexts.
Import ListNotations.

Section ClockComplete.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context (stream_block : block) (stream_offset : ptrofs) (initial : gateway_stream_values)
    (data_block : block) (data_offset : ptrofs) (amount : Z) (readonly : block -> Z -> Prop).
Variables (reference : mem) (owner : World).
Local Definition region := gateway_buffer_scope stream_block data_block readonly.
Local Definition history := gateway_scoped_buffer_history native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly reference owner.
Local Definition ready := clock_buffer_ready native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly reference owner.

Lemma clock_buffer_environment_avoids sample memory world :
  ready sample memory world -> gateway_environment_avoids region (clock_environment sample).
Proof.
  intros [SAMPLE [HISTORY SEPARATE]] identifier object ty position LOOK HERE.
  unfold clock_environment in LOOK.
  destruct (peq identifier _sample) as [SAME | DIFFERENT].
  - subst identifier; rewrite PTree.gss in LOOK; inversion LOOK; subst.
    exact (SEPARATE position HERE).
  - rewrite PTree.gso in LOOK by exact DIFFERENT; rewrite PTree.gempty in LOOK; discriminate.
Qed.

Theorem actual_clock_after_api_buffers sample status before world events returned after next :
  ready sample before world ->
  gateway_steps backend ge
    (gateway_live (Returnstate (Vint status) (clock_api_cont sample Kstop) before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  history after next /\ gateway_received_bytes io (stream_descriptor initial) events = [].
Proof.
  intros READY RUN.
  destruct (gateway_uniform_edge_side_cut backend ge (ready sample)
    (clock_buffer_ambient _ _ _ _ _ _ runtime _ _ _ _ _ _ _ reference owner sample)
    (Returnstate (Vint status) (clock_api_cont sample Kstop) before)
    (State f_host_now Sskip clock_return_cont (clock_environment sample) (clock_returned_temporaries status) before)
    before world events returned after next ltac:(cbn; tauto)
    ltac:(intro memory; apply unchanged_store_edge, edge_returnstate) READY RUN)
    as (pending & rest & memory & current & EVENTS & AMBIENT & PREFIX & CALLED & SUFFIX).
  assert (LOCAL : gateway_local_readonly_source native_private current
    (State f_host_now Sskip clock_return_cont (clock_environment sample) (clock_returned_temporaries status) memory)).
  { cbn [gateway_local_readonly_source gateway_readonly_statement]; split; [reflexivity |].
    split; [exact actual_clock_after_api_readonly |]. eapply clock_ready_environment; exact (proj1 CALLED). }
  assert (SCOPED : gateway_scoped_readonly region
    (State f_host_now Sskip clock_return_cont (clock_environment sample) (clock_returned_temporaries status) memory)).
  { cbn [gateway_scoped_readonly gateway_readonly_statement]; split; [reflexivity |].
    split; [exact actual_clock_after_api_readonly |]. eapply clock_buffer_environment_avoids; exact CALLED. }
  destruct (gateway_scoped_buffer_return backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner
    (State f_host_now Sskip clock_return_cont (clock_environment sample) (clock_returned_temporaries status) memory)
    current rest returned after next (stream_descriptor initial) LOCAL SCOPED (proj1 (proj2 CALLED)) SUFFIX)
    as [FINAL EMPTY].
  split; [exact FINAL |]. rewrite EVENTS, gateway_received_bytes_append, gateway_received_source_cons.
  assert (PENDING_EMPTY : gateway_received_bytes io (stream_descriptor initial) pending = []).
  { apply gateway_quiet_received_empty; eapply Forall_impl; [|exact AMBIENT]. intros event SAME; right; exact SAME. }
  rewrite PENDING_EMPTY, EMPTY; reflexivity.
Qed.

Theorem actual_clock_complete before world events returned after next symbol :
  sizeof (genv_cenv ge) clock_sample_type = 16 ->
  Genv.find_symbol ge _clock_gettime = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some clock_gettime_definition ->
  history before world ->
  gateway_steps backend ge (gateway_live (Callstate (Internal f_host_now) [] Kstop before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  history after next /\ gateway_received_bytes io (stream_descriptor initial) events = [].
Proof.
  intros SIZE SYMBOL FUNCTION READY RUN.
  destruct (actual_clock_buffer_call backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner
    before world events returned after next symbol SIZE SYMBOL FUNCTION READY RUN)
    as (prefix & suffix & sample & memory & current & EVENTS & EMPTY & CALLED & PREFIX & SUFFIX).
  destruct (gateway_return_cut backend ge clock_gettime_definition [Vint Int.one; Vptr sample Ptrofs.zero]
    (clock_api_cont sample Kstop) memory current suffix (Returnstate returned Kstop after) next ltac:(reflexivity)
    ltac:(cbn [clock_api_cont gateway_continuation gateway_cont_weight]; lia) SUFFIX)
    as (api_events & caller_events & value & changed & changed_world & SUFFIX_EVENTS & API & CALLER).
  destruct (actual_clock_api_buffers backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly reference owner
    sample memory current api_events value changed changed_world CALLED API)
    as [status [VALUE [AFTER API_EMPTY]]]; subst value.
  destruct (actual_clock_after_api_buffers sample status changed changed_world caller_events returned after next AFTER CALLER)
    as [FINAL CALLER_EMPTY].
  split; [exact FINAL |].
  rewrite EVENTS, SUFFIX_EVENTS, !gateway_received_bytes_append, EMPTY, API_EMPTY, CALLER_EMPTY; reflexivity.
Qed.

End ClockComplete.
