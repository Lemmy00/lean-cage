(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Compose actual memory-preserving control fragments at their
   source boundary. *)
From Stdlib Require Import List.
From compcert Require Import Values Memory Clight Events.
Require Import StoreSteps.
From HostGateway Require Import GatewayMachine GatewayPure GatewayCallPath GatewayReadonly GatewayRuntimeCuts GatewayOperations.
Import ListNotations.

Inductive gateway_retained_prefix (ge:Clight.genv)(target:Clight.state):Clight.state->Prop:=
|gateway_prefix_reached:forall memory,
  gateway_retained_prefix ge target(gateway_replace_memory target memory)
|gateway_prefix_next:forall source next,
  ~gateway_at_primitive source ->
  (forall memory,store_edge ge(gateway_replace_memory source memory)(gateway_replace_memory next memory)) ->
  gateway_retained_prefix ge target next ->gateway_retained_prefix ge target source.

Lemma gateway_prefix_before_call ge target source definition arguments continuation :
  gateway_retained_prefix ge target source ->gateway_retained_call_path ge definition arguments continuation target ->
  gateway_retained_call_path ge definition arguments continuation source.
Proof.
  intros PREFIX CALL;induction PREFIX.
  - apply gateway_retained_replace;exact CALL.
  - eapply gateway_retained_next;[exact H|exact H0|exact IHPREFIX].
Qed.

Theorem gateway_prefix_side_cut {World Event}(backend:gateway_backend World Event)ge ready
    (discipline:gateway_runtime_discipline backend ready)target source :
  gateway_retained_prefix ge target source ->
  forall before world events returned after next,
    ready before world ->
    gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)events
      (gateway_live(Returnstate returned Kstop after)next) ->
    exists prefix suffix memory current,
      events=prefix++suffix /\Forall gateway_quiet_event prefix /\
      gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)prefix
        (gateway_live(gateway_replace_memory target memory)current) /\ready memory current /\
      gateway_steps backend ge(gateway_live(gateway_replace_memory target memory)current)suffix
        (gateway_live(Returnstate returned Kstop after)next).
Proof.
  intro PREFIX;induction PREFIX as[memory|source middle INTERNAL EDGES REST IH];
    intros before world events returned after final_world READY RUN.
  - rewrite gateway_memory_replace_twice in RUN|-*.
    exists[],events,before,world;cbn;split;[reflexivity|]. split;[constructor|].
    split;[constructor|]. split;assumption.
  - destruct(gateway_uniform_edge_side_cut backend ge ready discipline source middle
      before world events returned after final_world INTERNAL EDGES READY RUN)
      as[pending[rest[memory[current[EVENTS1[AMBIENT[PENDING[READY1 REST1]]]]]]]].
    destruct(IH memory current rest returned after final_world READY1 REST1)
      as[prefix[suffix[selected[final[EVENTS2[QUIET[SELECTED[READY2 SUFFIX]]]]]]]].
    exists(pending++gateway_source E0::prefix),suffix,selected,final.
    split.
    + rewrite EVENTS1,EVENTS2;repeat rewrite <-app_assoc;cbn[app];reflexivity.
    + split.
      * apply Forall_app;split.
        -- eapply Forall_impl;[|exact AMBIENT]. intros event SAME;right;exact SAME.
        -- constructor;[left;reflexivity|exact QUIET].
      * split.
        -- eapply gateway_steps_append;[exact PENDING|].
           destruct(EDGES memory)as[IN[REAL UNIQUE]].
           econstructor;[apply gateway_internal;[exact IN|exact REAL]|exact SELECTED].
        -- split;assumption.
Qed.

Lemma gateway_prefix_before_return ge target source value :
  gateway_retained_prefix ge target source ->gateway_pure_path ge target value ->gateway_pure_path ge source value.
Proof.
  intros PREFIX RETURN;induction PREFIX.
  - apply gateway_pure_path_replace;exact RETURN.
  - eapply gateway_pure_next;[exact H|exact H0|exact IHPREFIX].
Qed.
