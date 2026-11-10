(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: A real clock primitive preserves separated caller regions. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayClock GatewayClockRuntime GatewayClockBuffers
  GatewayThreadRuntime GatewayStreamInterface GatewayReadContext GatewayReadMemory GatewayReadRegions
  GatewayScopedBufferRuntime GatewayBufferReference GatewayRuntime GatewayRuntimeABI GatewayOperations
  GatewayReadonly GatewayPrimitiveCalls.
Import ListNotations.
Open Scope Z_scope.

Section ClockBufferOperation.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context (stream_block : block) (stream_offset : ptrofs) (initial : gateway_stream_values)
    (data_block : block) (data_offset : ptrofs) (amount : Z) (readonly : block -> Z -> Prop).
Variables (reference : mem) (owner : World).
Local Definition region := gateway_buffer_scope stream_block data_block readonly.
Local Definition ready := clock_buffer_ready native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly reference owner.

Lemma clock_output_scope_frame sample before world after output :
  ready sample before world ->
  (forall object position, output object position -> object = sample) ->
  gateway_native_frame native_private stable_readonly output world before after ->
  Mem.unchanged_on region before after.
Proof.
  intros [SAMPLE [[INPUT HISTORY] SEPARATE]] OUTPUT FRAME.
  eapply gateway_native_frame_restrict; [exact FRAME | |].
  - intros object position [STREAM | [DATA | READONLY]].
    + subst object; left; exact (proj1 (proj2 INPUT)).
    + subst object; left; exact (proj1 (proj2 (proj2 INPUT))).
    + right; apply (proj1 (proj2 (proj2 (proj2 INPUT)))); exact READONLY.
  - intros object position HERE WRITTEN.
    pose proof (OUTPUT object position WRITTEN) as SAME; subst object.
    exact (SEPARATE position HERE).
Qed.

Theorem clock_buffer_primitive sample before world returned after next observed :
  ready sample before world ->
  gateway_runtime_operation backend clock_gettime_definition [Vint Int.one; Vptr sample Ptrofs.zero]
    before world returned after next observed ->
  exists status, returned = Vint status /\ ready sample after next /\ io observed = None.
Proof.
  intros READY OPERATION.
  destruct READY as [SAMPLE [HISTORY SEPARATE]].
  destruct (gateway_clock_operation _ _ _ _ _ _ runtime before world sample Ptrofs.zero returned after next observed
    (proj1 SAMPLE) (proj1 (proj2 SAMPLE))
    (clock_sample_ready_pointer native_private discipline sample before world SAMPLE) OPERATION)
    as (status & RETURNED & VALUES & SIDE & ACCESS & PERMISSIONS & FRAME & IO).
  assert (SCOPE : Mem.unchanged_on region before after).
  { eapply clock_output_scope_frame; [split; [exact SAMPLE | split; assumption] | |exact FRAME].
    intros object position [SAME RANGE]; exact SAME. }
  assert (INPUT : gateway_read_context native_private stable_readonly discipline None stream_block stream_offset initial
    data_block data_offset amount readonly after next).
  { eapply gateway_read_context_region_preserved; [exact (proj1 HISTORY) | exact SIDE | exact ACCESS |].
    eapply Mem.unchanged_on_implies; [exact SCOPE |].
    intros object position HERE LIVE; eapply gateway_buffer_scope_region; exact HERE. }
  exists status; split; [exact RETURNED |]. split; [|exact IO]. split.
  - split; [exact SIDE |]. split.
    + apply (proj1 ACCESS); [eapply clock_sample_ready_valid; exact SAMPLE | exact (proj1 (proj2 SAMPLE))].
    + intros position RANGE; apply (proj1 (PERMISSIONS position Cur Freeable ltac:(cbn; exact RANGE))).
      apply (proj2 (proj2 SAMPLE)); exact RANGE.
  - split; [|exact SEPARATE]. split; [exact INPUT |]. split.
    + eapply gateway_buffer_reference_transitive; [exact (proj1 (proj2 HISTORY)) |]. split.
      * eapply Mem.unchanged_on_implies; [exact SCOPE |]. intros object position HERE LIVE; right; right; exact HERE.
      * intros object [STREAM | DATA] position kind permission; subst object;
          apply (Mem.unchanged_on_perm _ _ _ SCOPE _ position kind permission).
        -- left; reflexivity.
        -- eapply gateway_read_stream_live; exact (proj2 (proj2 (proj2 (proj2 (proj1 HISTORY))))).
        -- right; left; reflexivity.
        -- exact (gateway_read_data_live _ _ _ _ _ _ _ _ (proj2 (proj2 (proj2 (proj2 (proj1 HISTORY)))))).
    + eapply gateway_native_reference_transitive; [exact (proj2 (proj2 HISTORY)) |].
      eapply gateway_native_reference_operation; [exact ACCESS | exact FRAME].
Qed.

Theorem actual_clock_api_buffers sample before world events returned after next :
  ready sample before world ->
  gateway_steps backend ge
    (gateway_live (Callstate clock_gettime_definition [Vint Int.one; Vptr sample Ptrofs.zero] Kstop before) world)
    events (gateway_live (Returnstate returned Kstop after) next) ->
  exists status, returned = Vint status /\ ready sample after next /\
    gateway_received_bytes io (stream_descriptor initial) events = [].
Proof.
  intros READY RUN.
  destruct (gateway_external_operation_of_run backend ge _ _ _ _ _ before world events returned after next RUN)
    as (prefix & suffix & called & called_world & changed & changed_world & observed &
      EVENTS & PENDING & PREFIX & OPERATION & SUFFIX).
  assert (CALLED : ready sample called called_world).
  { eapply gateway_pending_run_ready with
      (source := Callstate clock_gettime_definition [Vint Int.one; Vptr sample Ptrofs.zero] Kstop before);
      [eapply clock_buffer_ambient; exact runtime | exact READY | exact PENDING | exact PREFIX]. }
  destruct (clock_buffer_primitive sample called called_world returned changed changed_world observed CALLED OPERATION)
    as [status [RETURNED [CHANGED IO]]].
  exists status; split; [exact RETURNED |]. split.
  - eapply gateway_readonly_run_side with (source := Returnstate returned Kstop changed);
      [eapply clock_buffer_ambient; exact runtime | exact I | exact CHANGED | exact SUFFIX].
  - rewrite (gateway_external_received_projection backend ge io events returned after next prefix suffix
      changed changed_world observed (stream_descriptor initial) EVENTS PENDING SUFFIX).
    unfold gateway_received_event; rewrite IO; reflexivity.
Qed.

End ClockBufferOperation.
