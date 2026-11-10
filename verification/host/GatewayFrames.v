(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Private-region source proofs retain ambient mutations and loss. *)
From Stdlib Require Import List ZArith.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine ClightSteps StoreSteps.
From HostGateway Require Import GatewayMachine GatewayPure.
Import ListNotations.

Definition gateway_region_closed (protected:block->Z->Prop)(property:mem->Prop) : Prop :=
  forall before after, property before -> Mem.unchanged_on protected before after -> property after.

Record gateway_private_contract {World Event}(backend:gateway_backend World Event)
    (protected:block->Z->Prop)(active:World->Prop) : Prop := {
  gateway_private_ambient : forall before world after next,
    active world -> gateway_interference backend before world after next ->
    active next /\ Mem.unchanged_on protected before after
}.

Inductive gateway_framed_path (ge:Clight.genv)(protected:block->Z->Prop) :
    (mem->Prop)->Clight.state->val->(mem->Prop)->Prop :=
| gateway_framed_return : forall property value memory result,
    gateway_region_closed protected property ->
    (forall memory,property memory->result memory) ->
    gateway_framed_path ge protected property(Returnstate value Kstop memory)value result
| gateway_framed_next : forall property source next middle value result,
    gateway_region_closed protected property -> ~gateway_at_primitive source ->
    (forall memory,property memory -> exists after,
      store_edge ge(gateway_replace_memory source memory)(gateway_replace_memory next after) /\ middle after) ->
    gateway_framed_path ge protected middle next value result ->
    gateway_framed_path ge protected property source value result.

Lemma gateway_replace_memory_of source memory : memory_of(gateway_replace_memory source memory)=memory.
Proof. destruct source;reflexivity. Qed.

Lemma gateway_framed_same ge protected property source next value result :
  gateway_region_closed protected property -> ~gateway_at_primitive source ->
  (forall memory,property memory -> store_edge ge(gateway_replace_memory source memory)
    (gateway_replace_memory next memory)) ->
  gateway_framed_path ge protected property next value result ->
  gateway_framed_path ge protected property source value result.
Proof.
  intros CLOSED INTERNAL STEP REST.
  eapply gateway_framed_next with(next:=next)(middle:=property);[exact CLOSED|exact INTERNAL| |exact REST].
  intros memory GOOD;exists memory;auto.
Qed.

Lemma gateway_framed_post ge protected property source value first second :
  gateway_framed_path ge protected property source value first ->
  (forall memory,first memory->second memory) ->
  gateway_framed_path ge protected property source value second.
Proof.
  intros SCRIPT POST;induction SCRIPT.
  - constructor;[exact H|intros another GOOD;apply POST;auto].
  - eapply gateway_framed_next with(next:=next)(middle:=middle);eauto.
Qed.

Lemma gateway_framed_replace ge protected property source value result memory :
  gateway_framed_path ge protected property source value result ->
  gateway_framed_path ge protected property(gateway_replace_memory source memory)value result.
Proof.
  intro SCRIPT;induction SCRIPT;cbn.
  - constructor;assumption.
  - eapply gateway_framed_next with(next:=gateway_replace_memory next memory)(middle:=middle).
    + exact H.
    + intro PRIMITIVE;apply H0.
      exact((proj1(gateway_memory_replace_primitive source memory))PRIMITIVE).
    + intros another GOOD;rewrite gateway_memory_replace_twice.
      destruct(H1 another GOOD)as[after[EDGE POST]].
      exists after;rewrite gateway_memory_replace_twice;auto.
    + exact IHSCRIPT.
Qed.

Definition gateway_framed_state {World} ge protected(active:World->Prop) value result
    (state:gateway_state World) : Prop :=
  match state with
  | gateway_live source world => active world /\ exists property,
      property(memory_of source) /\ gateway_framed_path ge protected property source value result
  | gateway_dead _ _ => True
  end.

Lemma gateway_framed_step {World Event}(backend:gateway_backend World Event)ge protected active
    (law:gateway_private_contract backend protected active) before event after value result :
  gateway_framed_state ge protected active value result before -> gateway_step backend ge before event after ->
  gateway_framed_state ge protected active value result after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn in *;try exact I.
  - destruct GOOD as[ACTIVE[property[PROPERTY SCRIPT]]].
    inversion SCRIPT;subst.
    + match goal with REAL:step2 _ (Returnstate _ Kstop _)_ _|-_=>inversion REAL end.
    + match goal with EDGES:forall memory,property memory->_|-_=>
        destruct(EDGES(memory_of source)PROPERTY)as[changed[[IN[REAL UNIQUE]]POST]]end.
      rewrite gateway_memory_replace_identity in UNIQUE.
      match goal with ACTUAL:step2 _ source _ _|-_=>
        destruct(UNIQUE _ _ ACTUAL)as[EVENT TARGET];subst end.
      split;[exact ACTIVE|]. exists middle;rewrite gateway_replace_memory_of;split;[exact POST|].
      apply gateway_framed_replace;assumption.
  - destruct GOOD as[ACTIVE[property[PROPERTY SCRIPT]]];inversion SCRIPT;subst.
    match goal with NOT:~gateway_at_primitive _|-_=>exfalso;apply NOT;exact I end.
  - destruct GOOD as[ACTIVE[property[PROPERTY SCRIPT]]];inversion SCRIPT;subst.
    match goal with NOT:~gateway_at_primitive _|-_=>exfalso;apply NOT;exact I end.
  - destruct GOOD as[ACTIVE[property[PROPERTY SCRIPT]]].
    destruct(gateway_private_ambient _ _ _ law _ _ _ _ ACTIVE H)as[NEXT FRAME].
    split;[exact NEXT|]. exists property;split.
    + rewrite gateway_replace_memory_of.
      inversion SCRIPT;subst;
        match goal with CLOSED:gateway_region_closed protected property|-_=>
          exact(CLOSED _ _ PROPERTY FRAME)end.
    + apply gateway_framed_replace;exact SCRIPT.
  - destruct GOOD as[ACTIVE[property[PROPERTY SCRIPT]]];inversion SCRIPT;subst;[contradiction|contradiction].
Qed.

Theorem gateway_framed_prefix {World Event}(backend:gateway_backend World Event)ge protected active
    (law:gateway_private_contract backend protected active) property source value result
    memory world events target :
  active world -> property memory -> gateway_framed_path ge protected property source value result ->
  gateway_steps backend ge(gateway_live(gateway_replace_memory source memory)world)events target ->
  gateway_framed_state ge protected active value result target.
Proof.
  intros ACTIVE PROPERTY SCRIPT RUN.
  assert(INITIAL:gateway_framed_state ge protected active value result
    (gateway_live(gateway_replace_memory source memory)world)).
  { split;[exact ACTIVE|]. exists property;rewrite gateway_replace_memory_of;split;[exact PROPERTY|].
    apply gateway_framed_replace;exact SCRIPT. }
  revert INITIAL;induction RUN;intro GOOD;[exact GOOD|].
  apply IHRUN;eapply gateway_framed_step;eassumption.
Qed.

(* §FS-host-boundary.caller: The final bytes and value come from the same actual wider execution. *)
Theorem gateway_framed_return_exact {World Event}(backend:gateway_backend World Event)ge protected active
    (law:gateway_private_contract backend protected active) property source value result
    memory world events actual after final_world :
  active world -> property memory -> gateway_framed_path ge protected property source value result ->
  gateway_steps backend ge(gateway_live(gateway_replace_memory source memory)world)events
    (gateway_live(Returnstate actual Kstop after)final_world) ->
  actual=value /\ result after /\ active final_world.
Proof.
  intros ACTIVE PROPERTY SCRIPT RUN.
  pose proof(gateway_framed_prefix backend ge protected active law property source value result
    memory world events _ ACTIVE PROPERTY SCRIPT RUN)as FINAL.
  destruct FINAL as[NEXT[property0[PROPERTY0 SCRIPT0]]].
  inversion SCRIPT0;subst.
  - auto.
  - match goal with EDGES:forall memory,property0 memory->_|-_=>
      destruct(EDGES after PROPERTY0)as[changed[[_[REAL _]]POST]]end.
    cbn in REAL;inversion REAL.
Qed.

(* §FS-host-boundary.caller: The source certificate constructs useful executions as well as prefixes. *)
Theorem gateway_framed_execution {World Event}(backend:gateway_backend World Event)ge protected
    property source value result :
  gateway_framed_path ge protected property source value result ->
  forall memory world,property memory -> exists events after,
    gateway_steps backend ge(gateway_live(gateway_replace_memory source memory)world)events
      (gateway_live(Returnstate value Kstop after)world) /\ result after.
Proof.
  intro SCRIPT;induction SCRIPT;intros initial world PROPERTY.
  - exists [],initial;split;[constructor|auto].
  - destruct(H1 initial PROPERTY)as[changed[[INTERNAL[STEP UNIQUE]]MIDDLE]].
    destruct(IHSCRIPT changed world MIDDLE)as[events[after[REST POST]]].
    exists(gateway_source E0::events),after;split;[|exact POST].
    econstructor;[eapply gateway_internal;eassumption|exact REST].
Qed.
