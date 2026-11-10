(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Actual source stack allocation/free transports runtime roots. *)
From Stdlib Require Import ZArith List Bool.
From compcert Require Import Coqlib Maps AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayReadonly GatewayThreadRuntime GatewayStreamInterface
  GatewayPure GatewayFrames GatewayCallPath GatewayOperations.
Import ListNotations.

Section LocalRuntime.
Context {World Event} (backend : gateway_backend World Event)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> Integers.int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).

Definition gateway_native_environment (world : World) (memory : mem) (environment : env) : Prop :=
  forall identifier object ty, environment ! identifier = Some (object, ty) ->
    Mem.valid_block memory object /\ native_private world object.

Lemma gateway_native_environment_empty world memory : gateway_native_environment world memory empty_env.
Proof. intros identifier object ty LOOK; rewrite PTree.gempty in LOOK; discriminate. Qed.

Lemma gateway_native_free_list mode before world blocks after :
  discipline mode before world ->
  (forall object low high, In (object, low, high) blocks -> native_private world object) ->
  Mem.free_list before blocks = Some after -> discipline mode after world.
Proof.
  revert before; induction blocks as [|[[object low] high] rest IH]; intros before SIDE PRIVATE FREE.
  - cbn in FREE; inversion FREE; subst; exact SIDE.
  - cbn in FREE; destruct (Mem.free before object low high) as [middle |] eqn:HEAD; [| discriminate].
    apply IH with (before := middle).
    + eapply gateway_thread_native_free; [exact runtime | exact SIDE | | exact HEAD].
      apply (PRIVATE object low high); left; reflexivity.
    + intros other from to MEMBER; apply (PRIVATE other from to); right; exact MEMBER.
    + exact FREE.
Qed.

Lemma gateway_native_alloc_variables ge mode initial before variables environment after world :
  alloc_variables ge initial before variables environment after ->
  discipline mode before world -> gateway_native_environment world before initial ->
  discipline mode after world /\ gateway_native_environment world after environment.
Proof.
  intro ALLOC; induction ALLOC; intros SIDE PRIVATE.
  - split; assumption.
  - apply IHALLOC.
    + eapply gateway_thread_native_alloc; [exact runtime | exact SIDE | eassumption].
    + intros identifier object other LOOK.
      destruct (peq identifier id) as [SAME | DIFFERENT].
      * subst identifier; rewrite PTree.gss in LOOK; inversion LOOK; subst.
        split.
        -- eapply Mem.valid_new_block; eassumption.
        -- eapply gateway_thread_fresh_native; [exact runtime | exact SIDE |].
           eapply Mem.fresh_block_alloc; eassumption.
      * rewrite PTree.gso in LOOK by exact DIFFERENT.
        destruct (PRIVATE _ _ _ LOOK) as [VALID NATIVE]; split; [| exact NATIVE].
        eapply Mem.valid_block_alloc; eassumption.
Qed.

Lemma gateway_native_environment_free_blocks ge world memory environment object low high :
  gateway_native_environment world memory environment ->
  In (object, low, high) (blocks_of_env ge environment) -> native_private world object.
Proof.
  intros PRIVATE MEMBER; unfold blocks_of_env in MEMBER.
  apply in_map_iff in MEMBER.
  destruct MEMBER as [[identifier [actual ty]] [SAME ELEMENT]]; cbn in SAME; inversion SAME; subst.
  pose proof (PTree.elements_complete _ _ _ ELEMENT) as LOOK.
  exact (proj2 (PRIVATE _ _ _ LOOK)).
Qed.

Definition gateway_local_readonly_source (world : World) (source : Clight.state) : Prop :=
  match source with
  | State function body continuation environment _ memory =>
    gateway_readonly_statement body = true /\ gateway_readonly_cont continuation = true /\
    gateway_native_environment world memory environment
  | Callstate (Internal function) _ Kstop _ => gateway_readonly_statement (fn_body function) = true
  | Returnstate _ Kstop _ => True
  | _ => False
  end.

Lemma gateway_local_readonly_call_cont continuation :
  gateway_readonly_cont continuation = true -> call_cont continuation = Kstop.
Proof. apply gateway_readonly_call_cont. Qed.

Lemma gateway_local_readonly_source_step ge mode source world trace after :
  gateway_local_readonly_source world source -> discipline mode (memory_of source) world ->
  step2 ge source trace after ->
  gateway_local_readonly_source world after /\ discipline mode (memory_of after) world.
Proof.
  destruct source as [function body continuation environment temporaries memory |
    definition arguments continuation memory | value continuation memory]; intros PROFILE SIDE STEP.
  - change (discipline mode memory world) in SIDE.
    destruct PROFILE as [BODY [CONTINUATION PRIVATE]].
    inversion STEP; subst; cbn [gateway_readonly_statement] in BODY;
      cbn [gateway_readonly_cont] in CONTINUATION; try discriminate.
    all: repeat rewrite andb_true_iff in *.
    all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
    all: try match goal with FREE : Mem.free_list ?original (blocks_of_env ?globals ?locals) = Some ?changed |- _ =>
      assert (SIDE_AFTER : discipline mode changed world) by
        (eapply gateway_native_free_list; [exact SIDE | | exact FREE];
         intros object low high MEMBER; eapply gateway_native_environment_free_blocks; eassumption)
      end.
    all: try match goal with CONT : gateway_readonly_cont ?kont = true |- context [call_cont ?kont] =>
      rewrite (gateway_local_readonly_call_cont kont CONT) end.
    all: cbn [gateway_local_readonly_source gateway_readonly_statement gateway_readonly_cont memory_of].
    all: repeat rewrite andb_true_iff.
    all: try destruct b.
    all: try (intuition; fail).
    all: try match goal with CALL : is_call_cont ?kont |- _ =>
      destruct kont; cbn in *; intuition discriminate end.
    all: intuition.
  - destruct definition; [| contradiction].
    destruct continuation; cbn in PROFILE; try contradiction.
    inversion STEP; subst.
    match goal with ENTRY : function_entry2 _ _ _ _ _ _ _ |- _ => inversion ENTRY; subst end.
    match goal with ALLOC : alloc_variables ge empty_env ?original _ _ _ |- _ =>
      destruct (gateway_native_alloc_variables ge mode _ _ _ _ _ world ALLOC SIDE
        (gateway_native_environment_empty world _)) as [EXTENDED PRIVATE] end.
    cbn [gateway_local_readonly_source memory_of]; intuition.
  - destruct continuation; cbn in PROFILE; try contradiction; inversion STEP.
Qed.

Lemma gateway_local_readonly_not_primitive source world :
  gateway_local_readonly_source world source -> ~ gateway_at_primitive source.
Proof.
  destruct source as [function body continuation environment temporaries memory |
    definition arguments continuation memory | value continuation memory]; cbn.
  - destruct body; cbn; intros GOOD PRIMITIVE; try contradiction; intuition discriminate.
  - destruct definition; cbn; [destruct continuation |]; tauto.
  - destruct continuation; cbn; tauto.
Qed.

Lemma gateway_local_environment_retained before world after next environment :
  gateway_native_environment world before environment ->
  gateway_access_retained native_private stable_readonly before world next ->
  gateway_native_frame native_private stable_readonly gateway_native_no_output world before after ->
  gateway_native_environment next after environment.
Proof.
  intros PRIVATE [NATIVE STABLE] FRAME identifier object ty LOOK.
  destruct (PRIVATE _ _ _ LOOK) as [VALID OWNED]; split.
  - eapply Mem.valid_block_unchanged_on; [exact FRAME | exact VALID].
  - apply NATIVE; assumption.
Qed.

Lemma gateway_local_runtime_discipline mode environment :
  gateway_runtime_discipline backend (fun memory world =>
    discipline mode memory world /\ gateway_native_environment world memory environment).
Proof.
  intros before world after next [SIDE PRIVATE] INTERFERENCE.
  destruct (gateway_thread_ambient _ _ _ _ _ _ runtime mode _ _ _ _ SIDE INTERFERENCE)
    as [SIDE_AFTER [RETAINED FRAME]].
  split; [exact SIDE_AFTER | eapply gateway_local_environment_retained; eassumption].
Qed.

Lemma gateway_local_readonly_ambient source world after next :
  gateway_local_readonly_source world source ->
  gateway_access_retained native_private stable_readonly (memory_of source) world next ->
  gateway_native_frame native_private stable_readonly gateway_native_no_output world (memory_of source) after ->
  gateway_local_readonly_source next (gateway_replace_memory source after).
Proof.
  destruct source as [function body continuation environment temporaries memory |
    definition arguments continuation memory | value continuation memory]; cbn.
  - intros [BODY [CONT PRIVATE]] RETAINED FRAME; split; [exact BODY |].
    split; [exact CONT | eapply gateway_local_environment_retained; eassumption].
  - destruct definition; destruct continuation; cbn; tauto.
  - destruct continuation; cbn; tauto.
Qed.

Definition gateway_local_runtime mode (state : gateway_state World) : Prop :=
  match state with
  | gateway_live source world => gateway_local_readonly_source world source /\
    discipline mode (memory_of source) world
  | gateway_dead _ _ => True
  end.

Lemma gateway_local_runtime_step ge mode before event after :
  gateway_local_runtime mode before -> gateway_step backend ge before event after ->
  gateway_local_runtime mode after.
Proof.
  intros GOOD STEP; destruct before as [source world | memory world].
  - destruct GOOD as [PROFILE SIDE].
    destruct (gateway_nonprimitive_step backend ge _ _ _ _
      (gateway_local_readonly_not_primitive _ _ PROFILE) STEP)
      as [[trace [target [EVENT [REAL TARGET]]]] |
        [[changed [next [EVENT [INTERFERENCE TARGET]]]] | [EVENT TARGET]]]; subst.
    + eapply gateway_local_readonly_source_step; eassumption.
    + destruct (gateway_thread_ambient _ _ _ _ _ _ runtime mode _ _ _ _ SIDE INTERFERENCE)
        as [SIDE_AFTER [RETAINED FRAME]].
      split; [eapply gateway_local_readonly_ambient; eassumption |].
      rewrite gateway_replace_memory_of; exact SIDE_AFTER.
    + exact I.
  - inversion STEP.
Qed.

(* §FS-host-boundary.caller: Source-only local scopes preserve real interpreter ownership. *)
Theorem gateway_local_readonly_run_side ge mode source world events returned after next :
  gateway_local_readonly_source world source -> discipline mode (memory_of source) world ->
  gateway_steps backend ge (gateway_live source world) events
    (gateway_live (Returnstate returned Kstop after) next) -> discipline mode after next.
Proof.
  intros PROFILE SIDE RUN.
  assert (INITIAL : gateway_local_runtime mode (gateway_live source world)) by (split; assumption).
  assert (FINAL : gateway_local_runtime mode (gateway_live (Returnstate returned Kstop after) next)).
  { revert INITIAL; induction RUN; intro GOOD; [exact GOOD |].
    apply IHRUN; eapply gateway_local_runtime_step; eassumption. }
  exact (proj2 FINAL).
Qed.

End LocalRuntime.
