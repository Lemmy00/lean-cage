(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Native local scopes preserve pre-existing caller memory. *)
From Stdlib Require Import ZArith List Bool.
From compcert Require Import Coqlib Maps AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayReadonly GatewayPure GatewayCallPath GatewayFrames.
Import ListNotations.

Definition gateway_region_live (protected : block -> Z -> Prop) (memory : mem) : Prop :=
  forall object position, protected object position -> Mem.valid_block memory object.

Definition gateway_environment_avoids (protected : block -> Z -> Prop) (environment : env) : Prop :=
  forall identifier object ty position, environment ! identifier = Some (object, ty) ->
    ~ protected object position.

Lemma gateway_environment_empty_avoids protected : gateway_environment_avoids protected empty_env.
Proof. intros identifier object ty position LOOK; rewrite PTree.gempty in LOOK; discriminate. Qed.

Lemma gateway_scope_allocation ge protected initial before variables environment after :
  alloc_variables ge initial before variables environment after ->
  gateway_region_live protected before -> gateway_environment_avoids protected initial ->
  gateway_environment_avoids protected environment /\ Mem.unchanged_on protected before after.
Proof.
  intro ALLOC; induction ALLOC; intros LIVE AVOIDS.
  - split; [exact AVOIDS | apply Mem.unchanged_on_refl].
  - assert (FRAME : Mem.unchanged_on protected m m1) by (eapply Mem.alloc_unchanged_on; eassumption).
    assert (MIDDLE_LIVE : gateway_region_live protected m1).
    { intros object position PROTECTED; eapply Mem.valid_block_unchanged_on;
        [exact FRAME | apply (LIVE object position); exact PROTECTED]. }
    assert (MIDDLE_AVOIDS : gateway_environment_avoids protected (PTree.set id (b1, ty) e)).
    { intros identifier object other position LOOK PROTECTED.
      destruct (peq identifier id) as [SAME | DIFFERENT].
      - subst identifier; rewrite PTree.gss in LOOK; inversion LOOK; subst.
        match goal with FRESH_ALLOC : Mem.alloc _ _ _ = (_, _) |- _ =>
          apply (Mem.fresh_block_alloc _ _ _ _ _ FRESH_ALLOC) end.
        apply (LIVE object position); exact PROTECTED.
      - rewrite PTree.gso in LOOK by exact DIFFERENT; eapply AVOIDS; eassumption. }
    destruct (IHALLOC MIDDLE_LIVE MIDDLE_AVOIDS) as [FINAL AFTER].
    split; [exact FINAL | eapply Mem.unchanged_on_trans; eassumption].
Qed.

Lemma gateway_scope_free_list protected before blocks after :
  Mem.free_list before blocks = Some after ->
  (forall object low high position, In (object, low, high) blocks -> ~ protected object position) ->
  Mem.unchanged_on protected before after.
Proof.
  revert before; induction blocks as [|[[object low] high] rest IH]; intros before FREE AVOIDS.
  - cbn in FREE; inversion FREE; subst; apply Mem.unchanged_on_refl.
  - cbn in FREE; destruct (Mem.free before object low high) as [middle |] eqn:HEAD; [| discriminate].
    eapply Mem.unchanged_on_trans with (m2 := middle).
    + eapply Mem.free_unchanged_on; [exact HEAD |].
      intros position RANGE; eapply AVOIDS; left; reflexivity.
    + apply IH; [exact FREE |].
      intros other from to position MEMBER; apply (AVOIDS other from to position); right; exact MEMBER.
Qed.

Lemma gateway_environment_avoids_free ge protected environment before after :
  gateway_environment_avoids protected environment ->
  Mem.free_list before (blocks_of_env ge environment) = Some after ->
  Mem.unchanged_on protected before after.
Proof.
  intros AVOIDS FREE; eapply gateway_scope_free_list; [exact FREE |].
  intros object low high position MEMBER; unfold blocks_of_env in MEMBER.
  apply in_map_iff in MEMBER.
  destruct MEMBER as [[identifier [actual ty]] [SAME ELEMENT]]; cbn in SAME; inversion SAME; subst.
  eapply AVOIDS; eapply PTree.elements_complete; exact ELEMENT.
Qed.

Definition gateway_scoped_readonly (protected : block -> Z -> Prop) (source : Clight.state) : Prop :=
  match source with
  | State _ body continuation environment _ _ =>
    gateway_readonly_statement body = true /\ gateway_readonly_cont continuation = true /\
    gateway_environment_avoids protected environment
  | Callstate (Internal function) _ Kstop _ => gateway_readonly_statement (fn_body function) = true
  | Returnstate _ Kstop _ => True
  | _ => False
  end.

Lemma gateway_scoped_readonly_not_primitive protected source :
  gateway_scoped_readonly protected source -> ~ gateway_at_primitive source.
Proof.
  destruct source as [function body continuation environment temporaries memory |
    definition arguments continuation memory | value continuation memory]; cbn.
  - destruct body; cbn; intros GOOD PRIMITIVE; try contradiction; intuition discriminate.
  - destruct definition; cbn; [destruct continuation |]; tauto.
  - destruct continuation; cbn; tauto.
Qed.

Lemma gateway_scoped_readonly_replace protected source memory :
  gateway_scoped_readonly protected source -> gateway_scoped_readonly protected (gateway_replace_memory source memory).
Proof.
  destruct source as [function body continuation environment temporaries original |
    definition arguments continuation original | value continuation original].
  - cbn; tauto.
  - destruct definition; destruct continuation; cbn; tauto.
  - destruct continuation; cbn; tauto.
Qed.

Lemma gateway_scoped_readonly_source_step ge protected source trace after :
  gateway_scoped_readonly protected source -> gateway_region_live protected (memory_of source) ->
  step2 ge source trace after ->
  gateway_scoped_readonly protected after /\ Mem.unchanged_on protected (memory_of source) (memory_of after).
Proof.
  destruct source as [function body continuation environment temporaries memory |
    definition arguments continuation memory | value continuation memory]; intros PROFILE LIVE STEP.
  - destruct PROFILE as [BODY [CONTINUATION AVOIDS]].
    inversion STEP; subst; cbn [gateway_readonly_statement] in BODY;
      cbn [gateway_readonly_cont] in CONTINUATION; try discriminate.
    all: repeat rewrite andb_true_iff in *.
    all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
    all: try match goal with FREE : Mem.free_list ?original (blocks_of_env ?globals ?locals) = Some ?changed |- _ =>
      assert (FRAME : Mem.unchanged_on protected original changed) by
        (eapply gateway_environment_avoids_free; [exact AVOIDS | exact FREE]) end.
    all: try match goal with CONT : gateway_readonly_cont ?kont = true |- context [call_cont ?kont] =>
      rewrite (gateway_readonly_call_cont kont CONT) end.
    all: cbn [gateway_scoped_readonly gateway_readonly_statement gateway_readonly_cont memory_of].
    all: repeat rewrite andb_true_iff.
    all: try destruct b.
    all: try (intuition; fail).
    all: try match goal with CALL : is_call_cont ?kont |- _ =>
      destruct kont; cbn in *; intuition discriminate end.
    all: intuition auto using Mem.unchanged_on_refl.
  - destruct definition; [| contradiction].
    destruct continuation; cbn in PROFILE; try contradiction.
    inversion STEP; subst.
    match goal with ENTRY : function_entry2 _ _ _ _ _ _ _ |- _ => inversion ENTRY; subst end.
    match goal with ALLOC : alloc_variables ge empty_env ?original _ _ _ |- _ =>
      destruct (gateway_scope_allocation ge protected _ _ _ _ _ ALLOC LIVE
        (gateway_environment_empty_avoids protected)) as [AVOIDS FRAME] end.
    cbn [gateway_scoped_readonly memory_of]; intuition.
  - destruct continuation; cbn in PROFILE; try contradiction; inversion STEP.
Qed.

Definition gateway_scoped_memory_state {World} protected (active : World -> Prop) initial
    (state : gateway_state World) : Prop :=
  match state with
  | gateway_live source world => active world /\ gateway_scoped_readonly protected source /\
    gateway_region_live protected (memory_of source) /\
    Mem.unchanged_on protected initial (memory_of source)
  | gateway_dead _ _ => True
  end.

Lemma gateway_scoped_memory_step {World Event} (backend : gateway_backend World Event) ge
    protected active (private : gateway_private_contract backend protected active)
    initial before event after :
  gateway_scoped_memory_state protected active initial before -> gateway_step backend ge before event after ->
  gateway_scoped_memory_state protected active initial after.
Proof.
  intros GOOD STEP; destruct before as [source world | memory world].
  - destruct GOOD as [ACTIVE [PROFILE [LIVE FRAME]]].
    destruct (gateway_nonprimitive_step backend ge _ _ _ _
      (gateway_scoped_readonly_not_primitive _ _ PROFILE) STEP)
      as [[trace [target [EVENT [REAL TARGET]]]] |
        [[changed [next [EVENT [INTERFERENCE TARGET]]]] | [EVENT TARGET]]]; subst.
    + destruct (gateway_scoped_readonly_source_step _ _ _ _ _ PROFILE LIVE REAL) as [NEXT STEP_FRAME].
      split; [exact ACTIVE |]. split; [exact NEXT |]. split.
      * intros object position PROTECTED; eapply Mem.valid_block_unchanged_on;
          [exact STEP_FRAME | apply (LIVE object position); exact PROTECTED].
      * eapply Mem.unchanged_on_trans; eassumption.
    + destruct (gateway_private_ambient _ _ _ private _ _ _ _ ACTIVE INTERFERENCE) as [NEXT STEP_FRAME].
      split; [exact NEXT |]. split; [apply gateway_scoped_readonly_replace; exact PROFILE |].
      rewrite gateway_replace_memory_of; split.
      * intros object position PROTECTED; eapply Mem.valid_block_unchanged_on;
          [exact STEP_FRAME | apply (LIVE object position); exact PROTECTED].
      * eapply Mem.unchanged_on_trans; eassumption.
    + exact I.
  - inversion STEP.
Qed.

(* §FS-host-boundary.caller: Fresh native scopes do not borrow or free existing caller cells. *)
Theorem gateway_scoped_memory_prefix {World Event} (backend : gateway_backend World Event) ge
    protected active (private : gateway_private_contract backend protected active)
    source world events target :
  active world -> gateway_scoped_readonly protected source ->
  gateway_region_live protected (memory_of source) ->
  gateway_steps backend ge (gateway_live source world) events target ->
  gateway_scoped_memory_state protected active (memory_of source) target.
Proof.
  intros ACTIVE PROFILE LIVE RUN.
  assert (INITIAL : gateway_scoped_memory_state protected active (memory_of source)
    (gateway_live source world)).
  { split; [exact ACTIVE |]. split; [exact PROFILE |].
    split; [exact LIVE | apply Mem.unchanged_on_refl]. }
  revert INITIAL; induction RUN; intro GOOD; [exact GOOD |].
  apply IHRUN; eapply gateway_scoped_memory_step; eassumption.
Qed.

Theorem gateway_scoped_memory_return {World Event} (backend : gateway_backend World Event) ge
    protected active (private : gateway_private_contract backend protected active)
    source world events returned after next :
  active world -> gateway_scoped_readonly protected source ->
  gateway_region_live protected (memory_of source) ->
  gateway_steps backend ge (gateway_live source world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  active next /\ Mem.unchanged_on protected (memory_of source) after.
Proof.
  intros ACTIVE PROFILE LIVE RUN.
  destruct (gateway_scoped_memory_prefix _ _ _ _ private _ _ _ _ ACTIVE PROFILE LIVE RUN)
    as [NEXT [_ [_ FRAME]]]; split; assumption.
Qed.
