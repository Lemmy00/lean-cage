(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Signal failure never supplies a normal readiness continuation. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Events Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewaySource GatewayReadySource GatewayReadyPhases GatewayReadyRestoreCalls
  GatewayReadyContext GatewayRuntime GatewayRuntimeABI GatewayThreadRuntime GatewayReadContext GatewayStreamInterface
  GatewayOperations GatewayPrimitiveCalls GatewayTransferMath GatewayGuardReturn GatewayReturns.
Import ListNotations.

Section ReadySignals.
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

Theorem actual_ready_signals_operation item current before world events returned after next :
  slice item None current before world ->
  gateway_steps backend ge (gateway_live (Callstate gateway_check_signals_definition [] Kstop before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  (exists status, returned = Vint status) /\
  (returned = Vint Int.zero -> slice item None current after next) /\
  gateway_received_bytes io (stream_descriptor initial) events = [].
Proof.
  intros READY RUN.
  set (output := fun result memory current_world =>
    (exists status, result = Vint status) /\ (result = Vint Int.zero -> slice item None current memory current_world)).
  assert (POST : forall memory current_world result changed future observed,
    slice item None current memory current_world ->
    gateway_runtime_operation backend gateway_check_signals_definition []
      memory current_world result changed future observed -> output result changed future /\ io observed = None).
  { intros memory current_world result changed future observed INPUT OPERATION.
    destruct (gateway_check_signals_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ (proj1 (proj1 INPUT)) OPERATION)
      as (status & VALUE & NORMAL & IO).
    split; [split; [exists status; exact VALUE |] | exact IO].
    intro ZERO; assert (status = Int.zero) by congruence.
    destruct (NORMAL H) as (SIDE & ACCESS & FRAME).
    eapply gateway_ready_slice_no_output; eassumption. }
  destruct (gateway_actual_primitive_context backend ge _ _ _ _ [] (slice item None current) output
    (ambient item None current)
    ltac:(intros result memory current_world changed future [TYPE NORMAL] INTERFERENCE;
      split; [exact TYPE | intro ZERO; eapply ambient; [apply NORMAL; exact ZERO | exact INTERFERENCE]])
    ltac:(intros; apply (proj1 (POST _ _ _ _ _ _ H H0))) before world events returned after next READY RUN)
    as (prefix & suffix & called & called_world & changed & changed_world & observed & EVENTS & PENDING &
      PREFIX & CALLED & OPERATION & OUTPUT & SUFFIX & FINAL).
  destruct FINAL as [TYPE NORMAL]; split; [exact TYPE |]. split; [exact NORMAL |].
  rewrite (gateway_external_received_projection backend ge io events returned after next prefix suffix changed changed_world
    observed (stream_descriptor initial) EVENTS PENDING SUFFIX).
  unfold gateway_received_event; rewrite (proj2 (POST _ _ _ _ _ _ CALLED OPERATION)); reflexivity.
Qed.

Theorem actual_ready_checked_signals_zero item temporaries status before world events after next :
  gateway_steps backend ge
    (gateway_live (Returnstate (Vint status) (ready_signals_cont item temporaries) before) world) events
    (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) -> status = Int.zero.
Proof.
  intro RUN; destruct (Int.eq_dec status Int.zero) as [ZERO | NONZERO]; [exact ZERO |].
  pose proof (gateway_constant_path_actual backend ge _ _ world events (Vint Int.zero) after next
    (gateway_failed_result_path ge f_host_ready (ready_environment item) temporaries _t'7
      (Kseq ready_after_signals ready_iteration_cont) status before ltac:(reflexivity) ltac:(reflexivity) NONZERO)
    RUN) as BAD; discriminate BAD.
Qed.

End ReadySignals.
