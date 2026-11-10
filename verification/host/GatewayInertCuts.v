(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Exact pure source prefixes stop before their next effect. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps AST Values Memory Events Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayOperations GatewayFrames GatewayContexts
  GatewayStreamInterface GatewayPure GatewayCallPath.
Import ListNotations.

Fixpoint gateway_inert_statement parameter body : Prop :=
  match body with
  | Sskip => True
  | Sset identifier _ => identifier <> parameter
  | Ssequence first second | Sifthenelse _ first second =>
    gateway_inert_statement parameter first /\ gateway_inert_statement parameter second
  | _ => False
  end.

Inductive gateway_inert_cont parameter boundary : cont -> Prop :=
  | gateway_inert_boundary : gateway_inert_cont parameter boundary boundary
  | gateway_inert_sequence : forall body rest,
      gateway_inert_statement parameter body -> gateway_inert_cont parameter boundary rest ->
      gateway_inert_cont parameter boundary (Kseq body rest).

Definition gateway_inert_source parameter value boundary function environment source : Prop :=
  match source with
  | State actual body continuation locals temporaries _ =>
    actual = function /\ locals = environment /\ temporaries ! parameter = Some value /\
    gateway_inert_statement parameter body /\ gateway_inert_cont parameter boundary continuation
  | _ => False
  end.

Definition gateway_inert_at_boundary boundary source : Prop :=
  match source with State _ Sskip continuation _ _ _ => continuation = boundary | _ => False end.

Lemma gateway_inert_no_call_cont parameter tail outer continuation :
  gateway_inert_cont parameter (Kseq tail outer) continuation -> ~ is_call_cont continuation.
Proof. intro PROFILE; induction PROFILE; cbn; tauto. Qed.

Lemma gateway_inert_stop_or_continue parameter value tail outer function environment source :
  ~ gateway_inert_statement parameter tail ->
  gateway_inert_source parameter value (Kseq tail outer) function environment source ->
  gateway_inert_at_boundary (Kseq tail outer) source \/ ~ gateway_inert_at_boundary (Kseq tail outer) source.
Proof.
  destruct source as [actual body continuation locals temporaries memory |
    definition arguments continuation memory | returned continuation memory]; intros OPAQUE PROFILE; try contradiction.
  destruct PROFILE as [FUNCTION [ENV [PARAMETER [BODY CONT]]]].
  destruct body; cbn [gateway_inert_at_boundary]; try (right; tauto).
  inversion CONT; subst.
  - left; reflexivity.
  - right; intro SAME; inversion SAME; subst; contradiction.
Qed.

Lemma gateway_inert_internal ge parameter value tail outer function environment source trace target :
  gateway_inert_source parameter value (Kseq tail outer) function environment source ->
  ~ gateway_inert_at_boundary (Kseq tail outer) source ->
  step2 ge source trace target ->
  gateway_inert_source parameter value (Kseq tail outer) function environment target /\
    memory_of target = memory_of source.
Proof.
  destruct source as [actual body continuation locals temporaries memory |
    definition arguments continuation memory | returned continuation memory]; intros PROFILE BOUNDARY STEP; try contradiction.
  destruct PROFILE as [FUNCTION [ENV [PARAMETER [BODY CONT]]]]; subst actual locals.
  inversion STEP; subst; cbn [gateway_inert_statement] in BODY; try contradiction.
  all: try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
  all: try match goal with BAD : gateway_inert_cont _ (Kseq _ _) (Kloop1 _ _ _) |- _ => inversion BAD end.
  all: try match goal with BAD : gateway_inert_cont _ (Kseq _ _) (Kloop2 _ _ _) |- _ => inversion BAD end.
  all: try match goal with BAD : gateway_inert_cont _ (Kseq _ _) (Kswitch _) |- _ => inversion BAD end.
  all: try match goal with CALL : is_call_cont ?kont |- _ =>
    exfalso; eapply gateway_inert_no_call_cont; [exact CONT | exact CALL] end.
  - split; [cbn; repeat split; try assumption; try reflexivity | reflexivity].
    rewrite PTree.gso; [exact PARAMETER | congruence].
  - destruct BODY as [FIRST SECOND]; split; [|reflexivity].
    cbn; repeat split; try assumption; try reflexivity. apply gateway_inert_sequence; assumption.
  - inversion CONT; subst.
    + exfalso; apply BOUNDARY; reflexivity.
    + split; [cbn; repeat split; try reflexivity; assumption | reflexivity].
  - destruct BODY as [FIRST SECOND]; destruct b; split;
      try reflexivity; cbn; repeat split; try reflexivity; assumption.
Qed.

Lemma gateway_inert_replace parameter value boundary function environment source memory :
  gateway_inert_source parameter value boundary function environment source ->
  gateway_inert_source parameter value boundary function environment (gateway_replace_memory source memory).
Proof. destruct source; cbn; tauto. Qed.

Lemma gateway_inert_nonprimitive parameter value boundary function environment source :
  gateway_inert_source parameter value boundary function environment source -> ~ gateway_at_primitive source.
Proof.
  destruct source as [actual body continuation locals temporaries memory |
    definition arguments continuation memory | returned continuation memory]; cbn; intros PROFILE; try contradiction.
  destruct PROFILE as [FUNCTION [ENV [PARAMETER [BODY CONT]]]]; destruct body; cbn in *; tauto.
Qed.

Theorem gateway_inert_boundary_cut {World Event} (backend : gateway_backend World Event) ge
    (io : Event -> option gateway_native_io) descriptor ready (discipline : gateway_runtime_discipline backend ready)
    parameter value tail outer function environment source world events returned after next :
  ~ gateway_inert_statement parameter tail ->
  gateway_inert_source parameter value (Kseq tail outer) function environment source ->
  ready (memory_of source) world ->
  gateway_steps backend ge (gateway_live source world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix temporaries memory current,
    events = prefix ++ suffix /\ gateway_received_bytes io descriptor prefix = [] /\
    temporaries ! parameter = Some value /\ ready memory current /\
    gateway_steps backend ge (gateway_live source world) prefix
      (gateway_live (State function Sskip (Kseq tail outer) environment temporaries memory) current) /\
    gateway_steps backend ge
      (gateway_live (State function Sskip (Kseq tail outer) environment temporaries memory) current) suffix
      (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intro OPAQUE; revert source world.
  induction events as [|event rest IH]; intros source world PROFILE READY RUN.
  - inversion RUN; subst; contradiction.
  - destruct (gateway_inert_stop_or_continue parameter value tail outer function environment source OPAQUE PROFILE)
      as [BOUNDARY | CONTINUE].
    + destruct source as [actual body continuation locals temporaries memory |
        definition arguments continuation memory | value0 continuation memory]; try contradiction.
      destruct body; cbn in BOUNDARY; try contradiction; subst continuation.
      destruct PROFILE as [FN [ENV [PARAMETER [BODY CONT]]]]; subst actual locals.
      exists [], (event :: rest), temporaries, memory, world; cbn.
      split; [reflexivity |]. split; [reflexivity |]. split; [exact PARAMETER |].
      split; [exact READY |]. split; [constructor | exact RUN].
    + inversion RUN as [|first observed middle remaining last HEAD TAIL]; subst.
      destruct (gateway_nonprimitive_step backend ge _ _ _ _ (gateway_inert_nonprimitive _ _ _ _ _ _ PROFILE) HEAD)
        as [[trace [following [EVENT [REAL TARGET]]]] |
          [[changed [current [EVENT [INTERFERENCE TARGET]]]] | [EVENT TARGET]]]; subst.
      * destruct (gateway_inert_internal ge _ _ _ _ _ _ _ _ _ PROFILE CONTINUE REAL) as [FOLLOWING MEMORY].
        destruct (IH following world FOLLOWING ltac:(rewrite MEMORY; exact READY) TAIL)
          as (prefix & suffix & temporaries & memory & current & EVENTS & EMPTY & PARAMETER & REACHED & PREFIX & SUFFIX).
        exists (gateway_source trace :: prefix), suffix, temporaries, memory, current.
        split; [cbn; congruence |]. split; [exact EMPTY |]. split; [exact PARAMETER |].
        split; [exact REACHED |]. split; [econstructor; [exact HEAD | exact PREFIX] | exact SUFFIX].
      * destruct (IH (gateway_replace_memory source changed) current
          (gateway_inert_replace _ _ _ _ _ _ _ PROFILE)
          ltac:(rewrite gateway_replace_memory_of; eapply discipline; eassumption) TAIL)
          as (prefix & suffix & temporaries & memory & reached_world & EVENTS & EMPTY & PARAMETER & REACHED & PREFIX & SUFFIX).
        exists (gateway_ambient :: prefix), suffix, temporaries, memory, reached_world.
        split; [cbn; congruence |]. split; [exact EMPTY |]. split; [exact PARAMETER |].
        split; [exact REACHED |]. split; [econstructor; [exact HEAD | exact PREFIX] | exact SUFFIX].
      * destruct (gateway_dead_steps _ _ _ _ _ _ TAIL) as [_ BAD]; discriminate.
Qed.
