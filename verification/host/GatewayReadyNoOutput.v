(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Actual no-output SDK calls preserve the owned poll local and buffers. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Events Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayReadyContext GatewayRuntime GatewayRuntimeABI GatewayThreadRuntime
  GatewayStreamInterface GatewayReadContext GatewayOperations GatewayPrimitiveCalls GatewayTransferMath.
Import ListNotations.

Section ReadyNoOutput.
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

Theorem actual_ready_no_output_operation external types result_type convention arguments first
    (last : val -> option val) (property : val -> Prop)
    (operation : forall memory current result changed future observed,
      discipline first memory current ->
      gateway_runtime_operation backend (External external types result_type convention) arguments
        memory current result changed future observed ->
      property result /\ discipline (last result) changed future /\
      gateway_access_retained native_private stable_readonly memory current future /\
      gateway_native_frame native_private stable_readonly gateway_native_no_output current memory changed /\ io observed = None)
    item current before world events returned after next :
  slice item first current before world ->
  gateway_steps backend ge
    (gateway_live (Callstate (External external types result_type convention) arguments Kstop before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  property returned /\ slice item (last returned) current after next /\
  gateway_received_bytes io (stream_descriptor initial) events = [].
Proof.
  intros READY RUN.
  set (output := fun result memory current_world => property result /\ slice item (last result) current memory current_world).
  assert (POST : forall memory current_world result changed future observed,
    slice item first current memory current_world ->
    gateway_runtime_operation backend (External external types result_type convention) arguments
      memory current_world result changed future observed -> output result changed future /\ io observed = None).
  { intros memory current_world result changed future observed INPUT OPERATION.
    destruct (operation _ _ _ _ _ _ (proj1 (proj1 INPUT)) OPERATION) as (PROPERTY & SIDE & ACCESS & FRAME & IO).
    split; [split; [exact PROPERTY |] | exact IO].
    eapply gateway_ready_slice_no_output; eassumption. }
  destruct (gateway_actual_primitive_context backend ge external types result_type convention arguments
    (slice item first current) output (ambient item first current)
    ltac:(intros result memory current_world changed future [PROPERTY INPUT] INTERFERENCE;
      split; [exact PROPERTY | eapply ambient; eassumption])
    ltac:(intros; apply (proj1 (POST _ _ _ _ _ _ H H0))) before world events returned after next READY RUN)
    as (prefix & suffix & called & called_world & changed & changed_world & observed & EVENTS & PENDING &
      PREFIX & CALLED & OPERATION & OUTPUT & SUFFIX & FINAL).
  destruct FINAL as [PROPERTY INPUT]; split; [exact PROPERTY |]. split; [exact INPUT |].
  rewrite (gateway_external_received_projection backend ge io events returned after next prefix suffix changed changed_world
    observed (stream_descriptor initial) EVENTS PENDING SUFFIX).
  unfold gateway_received_event; rewrite (proj2 (POST _ _ _ _ _ _ CALLED OPERATION)); reflexivity.
Qed.

Theorem actual_ready_errno_operation item current mode before world events returned after next :
  slice item mode current before world ->
  gateway_steps backend ge (gateway_live (Callstate gateway_errno_location_definition [] Kstop before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  (exists object offset, returned = Vptr object offset) /\ slice item mode current after next /\
  gateway_received_bytes io (stream_descriptor initial) events = [].
Proof.
  intros READY RUN.
  eapply actual_ready_no_output_operation with (first := mode) (last := fun _ => mode)
    (property := fun result => exists object offset, result = Vptr object offset); [|exact READY | exact RUN].
  intros memory current_world result changed future observed SIDE OPERATION.
  destruct (gateway_errno_location_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ SIDE OPERATION)
    as (object & offset & VALUE & POINTER & LOAD & NOT_NATIVE & NOT_STABLE & AFTER & ACCESS & FRAME & IO).
  split; [exists object, offset; exact VALUE |]. split; [exact AFTER |]. split; [exact ACCESS |]. split; assumption.
Qed.

Theorem actual_ready_restore_operation item current saved before world events returned after next :
  slice item (Some saved) current before world ->
  gateway_steps backend ge (gateway_live (Callstate gateway_restore_thread_definition [saved] Kstop before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  slice item None current after next /\ gateway_received_bytes io (stream_descriptor initial) events = [].
Proof.
  intros READY RUN.
  assert (RESULT : True /\ slice item None current after next /\
    gateway_received_bytes io (stream_descriptor initial) events = []).
  { eapply actual_ready_no_output_operation with (first := Some saved) (last := fun _ => None)
      (property := fun _ => True); [|exact READY | exact RUN].
    intros memory current_world result changed future observed SIDE OPERATION.
    destruct (gateway_restore_thread_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ SIDE OPERATION)
      as (AFTER & ACCESS & FRAME & IO).
    split; [exact I |]. split; [exact AFTER |]. split; [exact ACCESS |]. split; assumption. }
  exact (proj2 RESULT).
Qed.

End ReadyNoOutput.
