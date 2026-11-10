(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: The actual readiness return releases only its own poll allocation. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayReadySource GatewayReadyContext GatewayReadContext
  GatewayReadRegions GatewayReadMemory GatewayThreadRuntime GatewayStreamInterface GatewayBufferReference
  GatewayScopeBufferReference GatewayScopedBufferRuntime GatewayInstructions GatewayCalls GatewayReadonly
  GatewayOperations GatewayPrimitiveCalls GatewayGuardObservation GatewayTransferMath.
Import ListNotations.
Open Scope Z_scope.

Section ReadyReturn.
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
Local Definition result current := gateway_owned_buffer_context native_private stable_readonly discipline
  stream_block data_block stream_offset data_offset current amount readonly reference owner None.

Lemma actual_ready_local_free item current before world after :
  slice item None current before world -> Mem.free before item 0 8 = Some after -> result current after world.
Proof.
  intros (INPUT & TRANSPORT & PRIVATE & PERMISSIONS & SEPARATE & BUFFER & NATIVE) FREE.
  assert (FRAME : Mem.unchanged_on
    (gateway_read_region stream_block stream_offset data_block data_offset amount readonly) before after).
  { eapply Mem.free_unchanged_on; [exact FREE |].
    intros position RANGE HERE; apply (SEPARATE position).
    eapply gateway_buffer_scope_region; exact HERE. }
  assert (FIRST : item <> stream_block) by (intro SAME; apply (SEPARATE 0); left; exact SAME).
  assert (SECOND : item <> data_block) by (intro SAME; apply (SEPARATE 0); right; left; exact SAME).
  split.
  - eapply gateway_read_context_region_preserved; [exact INPUT | | |exact FRAME].
    + eapply gateway_thread_native_free; [exact runtime | exact (proj1 INPUT) | exact PRIVATE | exact FREE].
    + split; intros; assumption.
  - destruct (gateway_scope_free_buffer native_private readonly stream_block data_block before after world item 0 8 FREE
      ltac:(intros position HERE; apply (SEPARATE position); right; right; exact HERE) FIRST SECOND
      (gateway_read_stream_live _ _ _ _ _ _ _ _ (proj2 (proj2 (proj2 (proj2 INPUT)))) )
      (gateway_read_data_live _ _ _ _ _ _ _ _ (proj2 (proj2 (proj2 (proj2 INPUT)))))) as [FBUFFER FNATIVE].
    split.
    + eapply gateway_buffer_reference_transitive; eassumption.
    + eapply gateway_native_reference_transitive; eassumption.
Qed.

Lemma actual_ready_scope_free item current before world after :
  sizeof (genv_cenv ge) ready_item_type = 8 -> slice item None current before world ->
  Mem.free_list before (blocks_of_env ge (ready_environment item)) = Some after -> result current after world.
Proof.
  intros SIZE READY FREE.
  change (Mem.free_list before [(item, 0, sizeof (genv_cenv ge) ready_item_type)] = Some after) in FREE.
  rewrite SIZE in FREE; cbn in FREE.
  destruct (Mem.free before item 0 8) as [changed |] eqn:ACTUAL; [|discriminate].
  inversion FREE; subst changed; eapply actual_ready_local_free; eassumption.
Qed.

Theorem actual_ready_return_buffers expression continuation item current temporaries
    before world events returned after next :
  sizeof (genv_cenv ge) ready_item_type = 8 -> call_cont continuation = Kstop ->
  slice item None current before world ->
  gateway_steps backend ge
    (gateway_live (State f_host_ready (Sreturn expression) continuation (ready_environment item) temporaries before) world)
    events (gateway_live (Returnstate returned Kstop after) next) ->
  result current after next /\ gateway_received_bytes io (stream_descriptor initial) events = [].
Proof.
  intros SIZE STOP READY RUN.
  destruct (gateway_source_instruction_occurrence backend ge f_host_ready (Sreturn expression) continuation
    (ready_environment item) temporaries before world events returned after next ltac:(cbn; tauto) RUN)
    as (prefix & suffix & memory & called_world & trace & target & EVENTS & AMBIENT & PREFIX & REAL & SUFFIX).
  assert (CALLED : slice item None current memory called_world).
  { eapply gateway_ambient_run_ready with
      (source := State f_host_ready (Sreturn expression) continuation (ready_environment item) temporaries before);
      [eapply gateway_ready_slice_ambient; exact runtime |exact READY |exact AMBIENT |exact PREFIX]. }
  inversion REAL; subst;
    try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
  all: rewrite STOP in SUFFIX.
  all: match goal with FREE : Mem.free_list ?start (blocks_of_env ge (ready_environment ?actual_item)) = Some ?freed |- _ =>
    pose proof (actual_ready_scope_free actual_item current start called_world freed SIZE CALLED FREE) as FREED end.
  all: assert (FINAL : result current after next) by
    (match type of SUFFIX with gateway_steps _ _ (gateway_live ?actual_source ?actual_world) _ _ =>
      eapply gateway_readonly_run_side with (source := actual_source) (world := actual_world);
        [eapply gateway_owned_buffer_context_ambient; exact runtime |exact I |exact FREED |exact SUFFIX] end).
  all: split; [exact FINAL |].
  all: rewrite gateway_received_bytes_append, gateway_received_source_cons.
  all: assert (EMPTY : gateway_received_bytes io (stream_descriptor initial) prefix = []) by
    (apply gateway_quiet_received_empty; eapply Forall_impl; [|exact AMBIENT]; intros event SAME; right; exact SAME).
  all: rewrite EMPTY; cbn [app].
  all: apply gateway_quiet_received_empty; eapply Forall_impl;
    [intros event SAME; right; exact SAME | eapply gateway_terminal_return_ambient; exact SUFFIX].
Qed.

End ReadyReturn.
