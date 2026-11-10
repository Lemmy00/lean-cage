(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Actual memory-changing source prefixes retain their exact intermediate states. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewayMachine GatewayFrames GatewayOperations GatewayContexts GatewayCallPath
  GatewayFramedRuntime GatewayPure GatewayStreamInterface GatewayReadonly GatewayCalls.
Import ListNotations.

Definition gateway_instruction_boundary (source : Clight.state) : Prop :=
  match source with State _ _ _ _ _ _ => False | _ => True end.

(* The final state can be the selected spawn call. No eventual method return is
   required, including when the parent later fails or loses its observation. *)
Theorem gateway_source_instruction_before_boundary {World Event} (backend : gateway_backend World Event) ge
    function statement continuation environment temporaries before world events terminal next :
  gateway_instruction_boundary terminal ->
  ~ gateway_at_primitive (State function statement continuation environment temporaries before) ->
  gateway_steps backend ge (gateway_live (State function statement continuation environment temporaries before) world)
    events (gateway_live terminal next) ->
  exists prefix suffix memory current trace target,
    events = prefix ++ gateway_source trace :: suffix /\
    Forall (fun event => event = gateway_ambient) prefix /\
    gateway_steps backend ge (gateway_live (State function statement continuation environment temporaries before) world)
      prefix (gateway_live (State function statement continuation environment temporaries memory) current) /\
    step2 ge (State function statement continuation environment temporaries memory) trace target /\
    gateway_steps backend ge (gateway_live target current) suffix (gateway_live terminal next).
Proof.
  intros BOUNDARY; revert before world.
  induction events as [|event rest IH]; intros before world INTERNAL RUN.
  - inversion RUN; subst; contradiction.
  - inversion RUN as [|first observed middle remaining last HEAD TAIL]; subst.
    destruct (gateway_nonprimitive_step backend ge _ _ _ _ INTERNAL HEAD)
      as [[trace [target [EVENT [REAL TARGET]]]] |
        [[changed [current [EVENT [INTERFERENCE TARGET]]]] | [EVENT TARGET]]]; subst.
    + exists [], rest, before, world, trace, target; cbn.
      split; [reflexivity |]. split; [constructor |]. split; [constructor |]. split; assumption.
    + cbn [gateway_replace_memory] in TAIL.
      destruct (IH changed current INTERNAL TAIL)
        as (prefix & suffix & memory & called & trace & target & EVENTS & AMBIENT & PREFIX & REAL & SUFFIX).
      exists (gateway_ambient :: prefix), suffix, memory, called, trace, target.
      split; [cbn; congruence |]. split; [constructor; [reflexivity | exact AMBIENT] |]. split.
      * econstructor; [apply gateway_interleaved; exact INTERFERENCE | exact PREFIX].
      * split; assumption.
    + destruct (gateway_dead_steps _ _ _ _ _ _ TAIL) as [_ BAD]; discriminate.
Qed.

Inductive gateway_memory_prefix {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (target : Clight.state) (post : mem -> World -> Prop) : (mem -> World -> Prop) -> Clight.state -> Prop :=
| gateway_memory_reached : forall memory,
    gateway_memory_prefix backend ge target post post (gateway_replace_memory target memory)
| gateway_memory_next : forall property function statement continuation environment temporaries memory following middle,
    gateway_ambient_closed backend property ->
    ~ gateway_at_primitive (State function statement continuation environment temporaries memory) ->
    (forall before world, property before world -> exists after,
      store_edge ge (State function statement continuation environment temporaries before)
        (gateway_replace_memory following after) /\ middle after world) ->
    gateway_memory_prefix backend ge target post middle following ->
    gateway_memory_prefix backend ge target post property
      (State function statement continuation environment temporaries memory).

Lemma gateway_memory_identity {World Event} (backend : gateway_backend World Event) ge target post :
  gateway_memory_prefix backend ge target post post target.
Proof.
  pose proof (gateway_memory_reached backend ge target post (memory_of target)) as SCRIPT.
  rewrite gateway_memory_replace_identity in SCRIPT; exact SCRIPT.
Qed.

Lemma gateway_memory_prefix_replace {World Event} (backend : gateway_backend World Event) ge target post
    property source memory :
  gateway_memory_prefix backend ge target post property source ->
  gateway_memory_prefix backend ge target post property (gateway_replace_memory source memory).
Proof.
  intro SCRIPT; inversion SCRIPT; subst; cbn [gateway_replace_memory].
  - rewrite gateway_memory_replace_twice; exact (gateway_memory_reached backend ge target _ memory).
  - eapply gateway_memory_next; eassumption.
Qed.

Lemma gateway_memory_prefix_compose {World Event} (backend : gateway_backend World Event) ge
    middle mid target post property source :
  gateway_memory_prefix backend ge middle mid property source ->
  gateway_memory_prefix backend ge target post mid middle ->
  gateway_memory_prefix backend ge target post property source.
Proof.
  intro FIRST; induction FIRST; intro LAST.
  - apply gateway_memory_prefix_replace; exact LAST.
  - eapply gateway_memory_next; try eassumption.
    apply IHFIRST; exact LAST.
Qed.

Theorem gateway_memory_prefix_cut {World Event} (backend : gateway_backend World Event) ge target post
    property source before world events terminal next :
  gateway_memory_prefix backend ge target post property source ->
  gateway_instruction_boundary terminal -> property before world ->
  gateway_steps backend ge (gateway_live (gateway_replace_memory source before) world) events (gateway_live terminal next) ->
  exists prefix suffix memory current,
    events = prefix ++ suffix /\ Forall gateway_quiet_event prefix /\
    gateway_steps backend ge (gateway_live (gateway_replace_memory source before) world) prefix
      (gateway_live (gateway_replace_memory target memory) current) /\ post memory current /\
    gateway_steps backend ge (gateway_live (gateway_replace_memory target memory) current) suffix
      (gateway_live terminal next).
Proof.
  intro SCRIPT; revert before world events terminal next.
  induction SCRIPT as [template | property function statement continuation environment temporaries template
      following middle CLOSED INTERNAL EDGES REST IH]; intros before world events terminal next BOUNDARY READY RUN.
  - rewrite gateway_memory_replace_twice in RUN |- *.
    exists [], events, before, world; cbn.
    split; [reflexivity |]. split; [constructor |]. split; [constructor |]. split; assumption.
  - cbn [gateway_replace_memory] in RUN |- *.
    destruct (gateway_source_instruction_before_boundary backend ge function statement continuation environment temporaries
      before world events terminal next BOUNDARY INTERNAL RUN)
      as (pending & rest & memory & called & trace & actual & EVENTS1 & AMBIENT & PREFIX & REAL & SUFFIX).
    assert (CALLED : property memory called).
    { eapply gateway_ambient_run_ready with
        (source := State function statement continuation environment temporaries before).
      - exact CLOSED.
      - exact READY.
      - exact AMBIENT.
      - exact PREFIX. }
    destruct (EDGES memory called CALLED) as [changed [[INTERNAL2 [CANON UNIQUE]] UPDATED]].
    destruct (UNIQUE _ _ REAL) as [TRACE SAME]; subst trace actual.
    destruct (IH changed called rest terminal next BOUNDARY UPDATED SUFFIX)
      as (prefix & suffix & final & owner & EVENTS2 & QUIET & SELECTED & FINAL & FINISH).
    exists (pending ++ gateway_source E0 :: prefix), suffix, final, owner.
    split; [rewrite EVENTS1, EVENTS2; repeat rewrite <- app_assoc; cbn [app]; reflexivity |]. split.
    + apply Forall_app; split.
      * eapply Forall_impl; [|exact AMBIENT]; intros event SAME; right; exact SAME.
      * constructor; [left; reflexivity | exact QUIET].
    + split.
      * eapply gateway_steps_append; [exact PREFIX |].
        econstructor; [apply gateway_internal; [exact INTERNAL2 | exact CANON] | exact SELECTED].
      * split; assumption.
Qed.

Lemma gateway_memory_same {World Event} (backend : gateway_backend World Event) ge target post
    property function statement continuation environment temporaries memory following :
  gateway_ambient_closed backend property ->
  ~ gateway_at_primitive (State function statement continuation environment temporaries memory) ->
  (forall before world, property before world ->
    store_edge ge (State function statement continuation environment temporaries before)
      (gateway_replace_memory following before)) ->
  gateway_memory_prefix backend ge target post property following ->
  gateway_memory_prefix backend ge target post property
    (State function statement continuation environment temporaries memory).
Proof.
  intros CLOSED INTERNAL EDGES REST.
  eapply gateway_memory_next; [exact CLOSED | exact INTERNAL | | exact REST].
  intros before world READY; exists before; split; [apply EDGES with (world := world); exact READY | exact READY].
Qed.
