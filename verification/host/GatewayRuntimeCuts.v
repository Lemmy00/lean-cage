(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Couple one actual memory-preserving source edge with its runtime state. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayCallPath GatewayFrames
  GatewayOperations GatewayPure.
Import ListNotations.

Theorem gateway_uniform_edge_side_cut {World Event} (backend : gateway_backend World Event) ge
    ready (discipline : gateway_runtime_discipline backend ready) source target
    before world events returned after next :
  ~ gateway_at_primitive source ->
  (forall memory, store_edge ge (gateway_replace_memory source memory)
    (gateway_replace_memory target memory)) ->
  ready before world ->
  gateway_steps backend ge (gateway_live (gateway_replace_memory source before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists pending rest memory current,
    events = pending ++ gateway_source E0 :: rest /\
    Forall (fun event => event = gateway_ambient) pending /\
    gateway_steps backend ge (gateway_live (gateway_replace_memory source before) world) pending
      (gateway_live (gateway_replace_memory source memory) current) /\
    ready memory current /\
    gateway_steps backend ge (gateway_live (gateway_replace_memory target memory) current) rest
      (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intros INTERNAL EDGES; revert before world.
  induction events as [|event rest IH]; intros before world READY RUN.
  - inversion RUN; subst.
    destruct (EDGES before) as [IN [REAL UNIQUE]].
    match goal with SAME : gateway_replace_memory source before = Returnstate _ _ _ |- _ =>
      rewrite SAME in REAL; inversion REAL end.
  - inversion RUN as [|first observed middle remaining last HEAD TAIL]; subst.
    assert (NONPRIMITIVE : ~ gateway_at_primitive (gateway_replace_memory source before)).
    { intro BAD; apply INTERNAL; exact ((proj1 (gateway_memory_replace_primitive source before)) BAD). }
    destruct (gateway_nonprimitive_step backend ge _ _ _ _ NONPRIMITIVE HEAD)
      as [[trace [following [EVENT [REAL TARGET]]]] |
        [[changed [current [EVENT [INTERFERENCE TARGET]]]] | [EVENT TARGET]]]; subst.
    + destruct (EDGES before) as [IN [CANON UNIQUE]].
      destruct (UNIQUE _ _ REAL) as [TRACE SAME]; subst.
      exists [], rest, before, world; cbn.
      split; [reflexivity |]. split; [constructor |]. split; [constructor |]. split; assumption.
    + rewrite gateway_replace_memory_of in INTERFERENCE.
      rewrite gateway_memory_replace_twice in TAIL.
      destruct (IH changed current (discipline _ _ _ _ READY INTERFERENCE) TAIL)
        as [pending [suffix [memory [called [EVENTS [AMBIENT [PREFIX [CALLED SUFFIX]]]]]]]].
      exists (gateway_ambient :: pending), suffix, memory, called.
      split; [cbn; congruence |]. split; [constructor; [reflexivity | exact AMBIENT] |]. split.
      * econstructor; [apply gateway_interleaved; rewrite gateway_replace_memory_of; exact INTERFERENCE |].
        rewrite gateway_memory_replace_twice; exact PREFIX.
      * split; assumption.
    + destruct (gateway_dead_steps _ _ _ _ _ _ TAIL) as [_ BAD]; discriminate.
Qed.
