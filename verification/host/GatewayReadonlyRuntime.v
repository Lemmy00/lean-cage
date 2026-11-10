(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import List ZArith.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayPure GatewayFrames
  GatewayCallPath GatewayReadonly.
Import ListNotations.

(* §AR-host-boundary.interfaces: Runtime readiness depends on this memory and this world together. *)
Record gateway_coupled_private_contract {World Event}(backend:gateway_backend World Event)
    (protected:block->BinNums.Z->Prop)(side:mem->World->Prop):Prop:={
  gateway_coupled_ambient:forall before world after next,
    side before world ->gateway_interference backend before world after next ->
    side after next /\Mem.unchanged_on protected before after
}.

Definition gateway_framed_coupled_state {World}ge protected(side:mem->World->Prop)expected result
    (state:gateway_state World):Prop:=
  match state with
  |gateway_live source world=>side(memory_of source)world /\gateway_readonly_state source /\
    exists property,property(memory_of source) /\gateway_framed_path ge protected property source expected result
  |gateway_dead _ _=>True end.

Lemma gateway_framed_coupled_step {World Event}(backend:gateway_backend World Event)ge protected side
    (law:gateway_coupled_private_contract backend protected side)expected result before event after :
  gateway_framed_coupled_state ge protected side expected result before ->
  gateway_step backend ge before event after ->
  gateway_framed_coupled_state ge protected side expected result after.
Proof.
  intros GOOD STEP;destruct before as[source world|memory world];[|inversion STEP].
  destruct GOOD as[SIDE[PROFILE[property[PROPERTY SCRIPT]]]].
  destruct(gateway_nonprimitive_step backend ge _ _ _ _
    (gateway_readonly_not_primitive _ PROFILE)STEP)
    as[[trace[following[EVENT[REAL TARGET]]]]|
      [[changed[following_world[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
  - destruct(gateway_readonly_source_step _ _ _ _ PROFILE REAL)as[NEXT_PROFILE MEMORY].
    inversion SCRIPT;subst.
    + inversion REAL.
    + destruct(H1(memory_of source)PROPERTY)as[changed[[PRIVATE[CANON UNIQUE]]POST]].
      rewrite gateway_memory_replace_identity in PRIVATE,CANON,UNIQUE.
      destruct(UNIQUE _ _ REAL)as[ZERO SAME];subst.
      split;[rewrite MEMORY;exact SIDE|]. split;[exact NEXT_PROFILE|].
      exists middle;rewrite gateway_replace_memory_of;split;[exact POST|].
      apply gateway_framed_replace;assumption.
  - destruct(gateway_coupled_ambient _ _ _ law _ _ _ _ SIDE INTERFERENCE)as[NEXT FRAME].
    split;[rewrite gateway_replace_memory_of;exact NEXT|].
    split;[apply gateway_readonly_replace;exact PROFILE|].
    exists property;split.
    + rewrite gateway_replace_memory_of.
      inversion SCRIPT;subst;
        match goal with CLOSED:gateway_region_closed protected property|-_=>
          exact(CLOSED _ _ PROPERTY FRAME)end.
    + apply gateway_framed_replace;exact SCRIPT.
  - exact I.
Qed.

Theorem gateway_framed_coupled_return_exact {World Event}(backend:gateway_backend World Event)ge protected side
    (law:gateway_coupled_private_contract backend protected side)property source expected result
    world events actual after next :
  side(memory_of source)world ->gateway_readonly_state source ->property(memory_of source) ->
  gateway_framed_path ge protected property source expected result ->
  gateway_steps backend ge(gateway_live source world)events
    (gateway_live(Returnstate actual Kstop after)next) ->
  actual=expected /\result after /\side after next.
Proof.
  intros SIDE PROFILE PROPERTY SCRIPT RUN.
  assert(INITIAL:gateway_framed_coupled_state ge protected side expected result(gateway_live source world)).
  { split;[exact SIDE|]. split;[exact PROFILE|]. exists property;split;assumption. }
  assert(FINAL:gateway_framed_coupled_state ge protected side expected result
    (gateway_live(Returnstate actual Kstop after)next)).
  { revert INITIAL;induction RUN;intro GOOD;[exact GOOD|].
    apply IHRUN;eapply gateway_framed_coupled_step;eassumption. }
  destruct FINAL as[NEXT[RETURNED[property0[PROPERTY0 SCRIPT0]]]].
  inversion SCRIPT0;subst.
  - repeat split;auto.
  - destruct(H1 after PROPERTY0)as[changed[[_[REAL _]]POST]];cbn in REAL;inversion REAL.
Qed.
