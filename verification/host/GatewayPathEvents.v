(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Source-only decoder segments cannot consume hidden bytes. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewayMachine GatewayPure GatewayContexts GatewayFrames GatewayReadonly
  GatewayFramedRuntime GatewayStreamInterface GatewayOperations GatewayCallPath.
Import ListNotations.

Lemma gateway_source_silent ge source trace after :
  internal_state source ->step2 ge source trace after ->trace=E0.
Proof. intros INTERNAL STEP;inversion STEP;subst;try reflexivity;contradiction. Qed.

Lemma gateway_quiet_received {Event}(io:Event->option gateway_native_io)descriptor events :
  Forall gateway_quiet_event events ->gateway_received_bytes io descriptor events=[].
Proof.
  intro QUIET;induction QUIET;[reflexivity|].
  destruct H as[SOURCE|AMBIENT];subst x;cbn[gateway_received_bytes gateway_received_event];exact IHQUIET.
Qed.

Lemma gateway_received_append {Event}(io:Event->option gateway_native_io)descriptor first second :
  gateway_received_bytes io descriptor(first++second)=
    gateway_received_bytes io descriptor first++gateway_received_bytes io descriptor second.
Proof. apply flat_map_app. Qed.

Theorem gateway_readonly_run_events {World Event}(backend:gateway_backend World Event)ge
    source world events returned after next :
  gateway_readonly_state source ->
  gateway_steps backend ge(gateway_live source world)events
    (gateway_live(Returnstate returned Kstop after)next) ->Forall gateway_quiet_event events.
Proof.
  revert source world;induction events as[|event rest IH];intros source world PROFILE RUN;[constructor|].
  inversion RUN as[|first observed middle remaining target HEAD TAIL];subst.
  destruct(gateway_nonprimitive_step backend ge _ _ _ _(gateway_readonly_not_primitive _ PROFILE)HEAD)
    as[[trace[following[EVENT[REAL TARGET]]]]|
      [[changed[following_world[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
  - constructor.
    + left;f_equal;eapply gateway_source_silent;[|exact REAL].
      inversion HEAD;assumption.
    + destruct(gateway_readonly_source_step _ _ _ _ PROFILE REAL)as[NEXT SAME].
      eapply IH;eassumption.
  - constructor;[right;reflexivity|]. eapply IH;[apply gateway_readonly_replace;exact PROFILE|exact TAIL].
  - destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD];discriminate.
Qed.

Theorem gateway_runtime_path_events {World Event}(backend:gateway_backend World Event)ge
    property source value result world events returned after next :
  property(memory_of source)world ->gateway_runtime_path backend ge property source value result ->
  gateway_steps backend ge(gateway_live source world)events
    (gateway_live(Returnstate returned Kstop after)next) ->Forall gateway_quiet_event events.
Proof.
  revert source world property;induction events as[|event rest IH];
    intros source world property PROPERTY SCRIPT RUN;[constructor|].
  assert(INTERNAL:~gateway_at_primitive source)by(inversion SCRIPT;subst;[cbn;tauto|assumption]).
  inversion RUN as[|first observed middle remaining target HEAD TAIL];subst.
  destruct(gateway_nonprimitive_step backend ge _ _ _ _ INTERNAL HEAD)
    as[[trace[following[EVENT[REAL TARGET]]]]|
      [[changed[following_world[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
  - inversion SCRIPT;subst;[inversion REAL|].
    destruct(H1(memory_of source)world PROPERTY)as[changed[[PRIVATE[CANON UNIQUE]]POST]].
    rewrite gateway_memory_replace_identity in PRIVATE,CANON,UNIQUE.
    destruct(UNIQUE _ _ REAL)as[ZERO SAME];subst.
    constructor;[left;reflexivity|].
    eapply IH;[rewrite gateway_replace_memory_of;exact POST|
      exact(gateway_runtime_replace backend ge middle next0 value result changed H2)|exact TAIL].
  - constructor;[right;reflexivity|].
    eapply IH with(property:=property).
    + rewrite gateway_replace_memory_of;inversion SCRIPT;subst;
        match goal with CLOSED:gateway_ambient_closed backend property|-_=>eapply CLOSED;eassumption end.
    + apply gateway_runtime_replace;exact SCRIPT.
    + exact TAIL.
  - destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD];discriminate.
Qed.
