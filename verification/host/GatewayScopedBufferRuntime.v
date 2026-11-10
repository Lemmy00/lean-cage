(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Real readonly local scopes retain coupled caller state. *)
From Stdlib Require Import ZArith List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayReadonly GatewayLocalRuntime GatewayScopedMemory
  GatewayBufferReference GatewayThreadRuntime GatewayReadContext GatewayReadMemory GatewayReadRegions
  GatewayStreamInterface GatewayOperations GatewayFrames GatewayContexts.
Import ListNotations.

Definition gateway_buffer_scope first second (readonly : block -> Z -> Prop) object position : Prop :=
  object = first \/ object = second \/ readonly object position.

Section ScopedBufferRuntime.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> Integers.int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context (stream_block : block) (stream_offset : Integers.ptrofs) (initial : gateway_stream_values)
    (data_block : block) (data_offset : Integers.ptrofs) (amount : Z) (readonly : block -> Z -> Prop).
Variables (reference : mem) (owner : World).
Local Definition region := gateway_buffer_scope stream_block data_block readonly.
Local Definition read_context := gateway_read_context native_private stable_readonly discipline None
  stream_block stream_offset initial data_block data_offset amount readonly.

Definition gateway_scoped_buffer_history memory world : Prop :=
  read_context memory world /\ gateway_buffer_reference readonly stream_block data_block reference memory /\
  gateway_native_reference native_private reference owner memory world.

Lemma gateway_buffer_scope_live memory world :
  read_context memory world -> gateway_region_live region memory.
Proof.
  intros CONTEXT object position [STREAM | [DATA | READONLY]].
  - subst object; eapply gateway_read_stream_live; exact (proj2 (proj2 (proj2 (proj2 CONTEXT)))).
  - subst object; exact (gateway_read_data_live _ _ _ _ _ _ _ _ (proj2 (proj2 (proj2 (proj2 CONTEXT))))).
  - exact (gateway_read_readonly_live _ _ _ _ _ _ _ _ (proj2 (proj2 (proj2 (proj2 CONTEXT)))) object position READONLY).
Qed.

Lemma gateway_buffer_scope_region object position :
  gateway_read_region stream_block stream_offset data_block data_offset amount readonly object position ->
  region object position.
Proof.
  intros [[SAME RANGE] | [[SAME RANGE] | READONLY]];
    [left | right; left | right; right]; assumption.
Qed.

Lemma gateway_scoped_buffer_source_history before world after :
  gateway_scoped_buffer_history before world -> discipline None after world ->
  Mem.unchanged_on region before after -> gateway_scoped_buffer_history after world.
Proof.
  intros [CONTEXT [BUFFER NATIVE]] SIDE FRAME; split.
  - eapply gateway_read_context_region_preserved; [exact CONTEXT | exact SIDE | |].
    + split; intros; assumption.
    + eapply Mem.unchanged_on_implies; [exact FRAME |].
      intros object position HERE LIVE; apply gateway_buffer_scope_region; exact HERE.
  - split.
    + eapply gateway_buffer_reference_transitive; [exact BUFFER |]. split.
      * eapply Mem.unchanged_on_implies; [exact FRAME |]. intros object position HERE LIVE; right; right; exact HERE.
      * intros object [STREAM | DATA] position kind permission; subst object;
          apply (Mem.unchanged_on_perm _ _ _ FRAME _ position kind permission).
        -- left; reflexivity.
        -- eapply gateway_read_stream_live; exact (proj2 (proj2 (proj2 (proj2 CONTEXT)))).
        -- right; left; reflexivity.
        -- exact (gateway_read_data_live _ _ _ _ _ _ _ _ (proj2 (proj2 (proj2 (proj2 CONTEXT))))).
    + eapply gateway_native_reference_transitive; [exact NATIVE |].
      intros object LIVE PRIVATE; split; [eapply Mem.valid_block_unchanged_on; eassumption | exact PRIVATE].
Qed.

Definition gateway_scoped_buffer_runtime (state : gateway_state World) : Prop :=
  match state with
  | gateway_live source world =>
    gateway_local_readonly_source native_private world source /\ gateway_scoped_readonly region source /\
    gateway_scoped_buffer_history (memory_of source) world
  | gateway_dead _ _ => True
  end.

Lemma gateway_scoped_buffer_internal source world trace target :
  gateway_scoped_buffer_runtime (gateway_live source world) ->
  step2 ge source trace target -> gateway_scoped_buffer_runtime (gateway_live target world).
Proof.
  intros [LOCAL [SCOPED HISTORY]] STEP.
  destruct (gateway_local_readonly_source_step backend io native_private stable_readonly discipline thread_errno runtime
    ge None source world trace target LOCAL (proj1 (proj1 HISTORY)) STEP) as [AFTER SIDE].
  destruct (gateway_scoped_readonly_source_step ge region source trace target SCOPED
    (gateway_buffer_scope_live _ _ (proj1 HISTORY)) STEP) as [SCOPE FRAME].
  split; [exact AFTER |]. split; [exact SCOPE |]. eapply gateway_scoped_buffer_source_history; eassumption.
Qed.

Lemma gateway_scoped_buffer_ambient source world after next :
  gateway_scoped_buffer_runtime (gateway_live source world) ->
  gateway_interference backend (memory_of source) world after next ->
  gateway_scoped_buffer_runtime (gateway_live (gateway_replace_memory source after) next).
Proof.
  intros [LOCAL [SCOPED HISTORY]] INTERFERENCE.
  destruct (gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ (proj1 (proj1 HISTORY)) INTERFERENCE)
    as [SIDE [ACCESS FRAME]].
  split.
  - eapply gateway_local_readonly_ambient; eassumption.
  - split; [apply gateway_scoped_readonly_replace; exact SCOPED |].
    rewrite gateway_replace_memory_of.
    exact (gateway_owned_buffer_context_ambient backend io native_private stable_readonly discipline thread_errno runtime
      stream_block data_block stream_offset data_offset initial amount readonly reference owner None
      _ _ _ _ HISTORY INTERFERENCE).
Qed.

Lemma gateway_scoped_buffer_step source world event target descriptor :
  gateway_scoped_buffer_runtime (gateway_live source world) ->
  gateway_step backend ge (gateway_live source world) event target ->
  gateway_scoped_buffer_runtime target /\ gateway_received_event io descriptor event = [].
Proof.
  intros READY STEP.
  assert (INTERNAL : ~ gateway_at_primitive source).
  { eapply gateway_local_readonly_not_primitive; exact (proj1 READY). }
  inversion STEP; subst.
  - split; [eapply gateway_scoped_buffer_internal; eassumption | reflexivity].
  - exfalso; apply INTERNAL; exact I.
  - exfalso; apply INTERNAL; exact I.
  - split; [eapply gateway_scoped_buffer_ambient; eassumption | reflexivity].
  - contradiction.
  - split; [exact I | reflexivity].
  - exfalso; apply INTERNAL; exact I.
  - exfalso; apply INTERNAL; exact I.
Qed.

Theorem gateway_scoped_buffer_prefix source world events target descriptor :
  gateway_scoped_buffer_runtime (gateway_live source world) ->
  gateway_steps backend ge (gateway_live source world) events target ->
  gateway_scoped_buffer_runtime target /\ gateway_received_bytes io descriptor events = [].
Proof.
  intros READY RUN; remember (gateway_live source world) as first eqn:INITIAL.
  revert source world INITIAL READY.
  induction RUN; intros source world INITIAL READY; subst.
  - split; [exact READY | reflexivity].
  - destruct (gateway_scoped_buffer_step source world observed middle descriptor READY H) as [NEXT EMPTY].
    destruct middle as [following current | memory current].
    + destruct (IHRUN following current eq_refl NEXT) as [FINAL REST].
      split; [exact FINAL |]. change (gateway_received_event io descriptor observed ++
        gateway_received_bytes io descriptor rest = []); rewrite EMPTY, REST; reflexivity.
    + destruct (gateway_dead_steps _ _ _ _ _ _ RUN) as [EMPTY_REST DEAD]; subst.
      split; [exact I |]. change (gateway_received_event io descriptor observed ++ [] = []); rewrite EMPTY; reflexivity.
Qed.

Theorem gateway_scoped_buffer_return source world events returned after next descriptor :
  gateway_local_readonly_source native_private world source -> gateway_scoped_readonly region source ->
  gateway_scoped_buffer_history (memory_of source) world ->
  gateway_steps backend ge (gateway_live source world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  gateway_scoped_buffer_history after next /\ gateway_received_bytes io descriptor events = [].
Proof.
  intros LOCAL SCOPED HISTORY RUN.
  destruct (gateway_scoped_buffer_prefix source world events (gateway_live (Returnstate returned Kstop after) next)
    descriptor (conj LOCAL (conj SCOPED HISTORY)) RUN) as [[AFTER [SCOPE FINAL]] EMPTY].
  split; assumption.
Qed.

End ScopedBufferRuntime.
