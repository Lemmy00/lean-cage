(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Pure native control retains arbitrary interleaving and loss. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine ClightSteps StoreSteps.
From HostGateway Require Import GatewayMachine GatewayContexts.
Import ListNotations.

Lemma gateway_memory_replace_twice source first second :
  gateway_replace_memory(gateway_replace_memory source first)second=gateway_replace_memory source second.
Proof. destruct source;reflexivity. Qed.
Lemma gateway_memory_replace_identity source :
  gateway_replace_memory source(memory_of source)=source.
Proof. destruct source;reflexivity. Qed.
Lemma gateway_memory_replace_primitive source memory :
  gateway_at_primitive(gateway_replace_memory source memory)<->gateway_at_primitive source.
Proof. destruct source;reflexivity. Qed.

Inductive gateway_pure_path(ge:Clight.genv):Clight.state->val->Prop:=
| gateway_pure_return:forall value memory,
    gateway_pure_path ge(Returnstate value Kstop memory)value
| gateway_pure_next:forall first next value,
    ~gateway_at_primitive first ->
    (forall memory,store_edge ge(gateway_replace_memory first memory)(gateway_replace_memory next memory))->
    gateway_pure_path ge next value ->gateway_pure_path ge first value.

Lemma gateway_pure_path_replace ge source value memory :
  gateway_pure_path ge source value ->
  gateway_pure_path ge(gateway_replace_memory source memory)value.
Proof.
  intro SCRIPT;induction SCRIPT;cbn.
  - constructor.
  - eapply gateway_pure_next with(next:=gateway_replace_memory next memory).
    + intro PRIMITIVE;apply H.
      exact((proj1(gateway_memory_replace_primitive first memory))PRIMITIVE).
    + intro another;rewrite !gateway_memory_replace_twice;apply H0.
    + exact IHSCRIPT.
Qed.

Definition gateway_pure_state {World} ge result(state:gateway_state World):Prop:=
  match state with
  |gateway_live source _=>gateway_pure_path ge source result
  |gateway_dead _ _=>True
  end.

Lemma gateway_pure_step_preserves {World Event}(backend:gateway_backend World Event)ge
    before event after result :
  gateway_pure_state ge result before ->gateway_step backend ge before event after ->
  gateway_pure_state ge result after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn in *;try exact I.
  - inversion GOOD;subst.
    + match goal with REAL:step2 _ (Returnstate _ Kstop _)_ _|-_=>inversion REAL end.
    + match goal with EDGES:forall memory,store_edge _ _ _|-_=>
        destruct(EDGES(memory_of source))as[_[_ UNIQUE]]end.
      rewrite gateway_memory_replace_identity in UNIQUE.
      match goal with REAL:step2 _ source _ _|-_=>
        destruct(UNIQUE _ _ REAL)as[EVENT TARGET];subst end.
      apply gateway_pure_path_replace;assumption.
  - inversion GOOD;subst.
    match goal with NOT:~gateway_at_primitive _|-_=>exfalso;apply NOT;exact I end.
  - inversion GOOD;subst.
    match goal with NOT:~gateway_at_primitive _|-_=>exfalso;apply NOT;exact I end.
  - apply gateway_pure_path_replace;exact GOOD.
  - inversion GOOD;subst;[contradiction|contradiction].
Qed.

Theorem gateway_pure_path_return {World Event}(backend:gateway_backend World Event)ge
    source result before world events actual after final_world :
  gateway_pure_path ge source result ->
  gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)events
    (gateway_live(Returnstate actual Kstop after)final_world) ->actual=result.
Proof.
  intros SCRIPT RUN.
  assert(INITIAL:gateway_pure_state ge result
    (gateway_live(gateway_replace_memory source before)world)).
  { apply gateway_pure_path_replace;exact SCRIPT. }
  assert(FINAL:gateway_pure_state ge result
    (gateway_live(Returnstate actual Kstop after)final_world)).
  { revert INITIAL;induction RUN;intro GOOD;[exact GOOD|].
    apply IHRUN;eapply gateway_pure_step_preserves;eassumption. }
  cbn in FINAL;inversion FINAL;subst;[reflexivity|].
  match goal with EDGES:forall memory,store_edge _ _ _|-_=>
    destruct(EDGES after)as[_[REAL _]]end.
  cbn in REAL;inversion REAL.
Qed.
