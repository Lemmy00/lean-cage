(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: The source cancellation suffix exposes each actual memory effect. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayCancellation GatewayCancellationRuntime
  GatewayCancellationMemory GatewayCancellationSuffix GatewayThreadRuntime GatewayStreamInterface
  GatewayStreamLayout GatewayRuntime GatewayRuntimeABI GatewayReadContext GatewayReadMemory GatewayOperations
  GatewayContexts GatewayBufferReference GatewayReadonlyOperations GatewayFrames.
Import ListNotations.
Open Scope Z_scope.

Inductive control_tail_memory_effect ge command stream_block stream_offset : mem -> mem -> Prop :=
  | control_tail_unchanged : forall memory,
      control_tail_memory_effect ge command stream_block stream_offset memory memory
  | control_tail_marked : forall before after,
      Mem.store Mint32 before stream_block (Ptrofs.unsigned stream_offset + 8) (Vint Int.one) = Some after ->
      control_tail_memory_effect ge command stream_block stream_offset before after
  | control_tail_freed : forall before after,
      Mem.free_list before (blocks_of_env ge (control_environment command)) = Some after ->
      control_tail_memory_effect ge command stream_block stream_offset before after.

Section CancellationFrames.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context (stream_block : block) (stream_offset : ptrofs) (initial : gateway_stream_values)
    (data_block : block) (data_offset : ptrofs) (amount : Z) (readonly : block -> Z -> Prop).
Local Definition active := control_tail_active native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly.
Local Definition live_context := control_tail_runtime native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly.

Lemma actual_control_tail_memory_effect command source world trace target :
  stream_member_layout ge _cancellation_sent 8 ->
  live_context command (gateway_live source world) -> internal_state source ->
  step2 ge source trace target ->
  control_tail_memory_effect ge command stream_block stream_offset (memory_of source) (memory_of target).
Proof.
  intros LAYOUT [PROFILE READY] INTERNAL STEP.
  destruct source as [function body continuation environment temporaries before |
    definition arguments continuation before | returned continuation before].
  - destruct PROFILE as [FN [ENV [STREAM [BODY CONT]]]]; subst function environment.
    change (active command before world) in READY.
    destruct body; cbn [control_tail_statement] in BODY; try contradiction.
    all: try solve [inversion STEP; subst;
      first [apply control_tail_unchanged | apply control_tail_freed; assumption]].
    match type of BODY with Sassign ?left ?right = control_cancel_assignment =>
      inversion BODY; subst left right end.
    destruct READY as [current [CONTEXT TRANSPORT]].
    pose proof (proj2 (proj2 (proj2 (proj2 (proj1 CONTEXT))))) as RAW.
    destruct (gateway_cancel_store_exists _ _ _ _ _ _ _ _ RAW) as [changed STORE].
    destruct (actual_control_cancel_edge ge command temporaries before stream_block stream_offset
      changed continuation STREAM LAYOUT (gateway_read_stream_bounds _ _ _ _ _ _ _ _ RAW) STORE)
      as [IN [REAL UNIQUE]].
    destruct (UNIQUE _ _ STEP) as [TRACE SAME]; subst trace target.
    apply control_tail_marked; exact STORE.
  - destruct PROFILE as [DEFINITION _]; subst definition; contradiction.
  - inversion STEP; subst; constructor.
Qed.

Lemma control_tail_current_read_context command source world :
  live_context command (gateway_live source world) ->
  exists current,
    gateway_read_context native_private stable_readonly discipline None stream_block stream_offset current
      data_block data_offset amount readonly (memory_of source) world.
Proof.
  intros [PROFILE READY].
  destruct source as [function body continuation environment temporaries memory |
    definition arguments continuation memory | value continuation memory]; cbn in READY.
  - destruct READY as [current [CONTEXT TRANSPORT]]; exists current; exact (proj1 CONTEXT).
  - destruct READY as [current [CONTEXT TRANSPORT]]; exists current; exact (proj1 CONTEXT).
  - destruct continuation; cbn in READY;
      destruct READY as [current [CONTEXT TRANSPORT]]; exists current; try exact CONTEXT; exact (proj1 CONTEXT).
Qed.

Lemma control_tail_internal_active command source world trace target :
  live_context command (gateway_live source world) -> internal_state source ->
  step2 ge source trace target -> active command (memory_of source) world.
Proof.
  intros [PROFILE READY] INTERNAL STEP.
  destruct source as [function body continuation environment temporaries memory |
    definition arguments continuation memory | value continuation memory].
  - exact READY.
  - destruct PROFILE as [DEFINITION _]; subst definition; contradiction.
  - destruct continuation; cbn in READY; try exact READY; inversion STEP.
Qed.

(* These are source-local transport rules, not a premise about any helper's
   result. Instantiations prove each rule from the concrete primitive frame. *)
Record control_tail_extra_contract command (extra : mem -> World -> Prop) : Prop := {
  control_tail_extra_mark : forall before world after,
    active command before world -> extra before world ->
    Mem.store Mint32 before stream_block (Ptrofs.unsigned stream_offset + 8) (Vint Int.one) = Some after ->
    extra after world;
  control_tail_extra_free : forall before world after,
    active command before world -> extra before world ->
    Mem.free_list before (blocks_of_env ge (control_environment command)) = Some after -> extra after world;
  control_tail_extra_ambient : forall current before world after next,
    gateway_read_context native_private stable_readonly discipline None stream_block stream_offset current
      data_block data_offset amount readonly before world -> extra before world ->
    gateway_interference backend before world after next -> extra after next;
  control_tail_extra_errno : forall before world returned after next observed,
    active command before world -> extra before world ->
    gateway_runtime_operation backend gateway_errno_location_definition [] before world returned after next observed ->
    extra after next
}.

Definition control_tail_extra_runtime command (extra : mem -> World -> Prop) (state : gateway_state World) : Prop :=
  match state with
  | gateway_live source world => live_context command state /\ extra (memory_of source) world
  | gateway_dead _ _ => True
  end.

Lemma actual_control_tail_extra_step command extra (rules : control_tail_extra_contract command extra)
    source world event target symbol :
  stream_member_layout ge _cancellation_sent 8 ->
  Genv.find_symbol ge ___errno_location = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_errno_location_definition ->
  control_tail_extra_runtime command extra (gateway_live source world) ->
  gateway_step backend ge (gateway_live source world) event target ->
  control_tail_extra_runtime command extra target.
Proof.
  intros LAYOUT SYMBOL FUNCTION [CONTEXT EXTRA] STEP.
  pose proof (proj1 (control_tail_step backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly command source world event target symbol
    LAYOUT SYMBOL FUNCTION CONTEXT STEP)) as NEXT.
  inversion STEP; subst; cbn [control_tail_extra_runtime]; try exact I.
  - split; [exact NEXT |].
    match goal with REAL : step2 _ _ _ _ |- _ =>
      pose proof (actual_control_tail_memory_effect command _ _ _ _ LAYOUT CONTEXT ltac:(assumption) REAL) as EFFECT;
      pose proof (control_tail_internal_active command _ _ _ _ CONTEXT ltac:(assumption) REAL) as ACTIVE end.
    inversion EFFECT; subst.
    + exact EXTRA.
    + eapply control_tail_extra_mark; [exact rules | exact ACTIVE | exact EXTRA | eassumption].
    + eapply control_tail_extra_free; [exact rules | exact ACTIVE | exact EXTRA | eassumption].
  - split; [exact NEXT |]. destruct CONTEXT as [[DEFINITION [ARGUMENTS CALLBACK]] READY]; subst.
    inversion DEFINITION; subst.
    eapply control_tail_extra_errno; [exact rules | exact READY | exact EXTRA |].
    unfold gateway_runtime_operation, gateway_errno_location_definition; eassumption.
  - destruct CONTEXT as [[FN [ENV [STREAM [BODY CONT]]]] READY]; contradiction.
  - split; [exact NEXT |].
    destruct (control_tail_current_read_context command source world CONTEXT) as [current INPUT].
    rewrite gateway_replace_memory_of.
    eapply control_tail_extra_ambient; [exact rules | exact INPUT | exact EXTRA | eassumption].
  - split; assumption.
Qed.

Theorem actual_control_tail_extra_prefix command extra (rules : control_tail_extra_contract command extra)
    source world events target symbol :
  stream_member_layout ge _cancellation_sent 8 ->
  Genv.find_symbol ge ___errno_location = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_errno_location_definition ->
  control_tail_extra_runtime command extra (gateway_live source world) ->
  gateway_steps backend ge (gateway_live source world) events target ->
  control_tail_extra_runtime command extra target.
Proof.
  intros LAYOUT SYMBOL FUNCTION READY RUN.
  remember (gateway_live source world) as first eqn:INITIAL; revert source world INITIAL READY.
  induction RUN; intros source world INITIAL READY; subst; [exact READY |].
  pose proof (actual_control_tail_extra_step command extra rules source world observed middle symbol
    LAYOUT SYMBOL FUNCTION READY H) as NEXT.
  destruct middle as [following current | memory current].
  - eapply IHRUN; [reflexivity | exact NEXT].
  - destruct (gateway_dead_steps _ _ _ _ _ _ RUN) as [EMPTY DEAD]; subst; exact I.
Qed.

End CancellationFrames.
