(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Header source cuts also consume the original caller's real return. *)
From Stdlib Require Import List Lia.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayMemoryPrefixes GatewayFramedRuntime
  GatewayHeaderCalls GatewayCallPath GatewayContexts GatewayReadonly GatewayRuntimeCuts GatewayOperations.
Import ListNotations.

Definition gateway_header_boundary(terminal:Clight.state):Prop:=
  match terminal with
  |Callstate definition _ _ _=>definition=Internal f_host_transfer
  |Returnstate _ continuation _=>continuation=Kstop
  |State _ _ _ _ _ _=>False end.

Lemma gateway_header_boundary_instruction terminal:
  gateway_header_boundary terminal->gateway_instruction_boundary terminal.
Proof. destruct terminal;cbn;tauto. Qed.

Theorem gateway_header_boundary_return_cut {World Event}(backend:gateway_backend World Event)ge
    writer arguments function environment temporaries outer before world events terminal next:
  gateway_header_boundary terminal->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal(gateway_header_function writer))arguments
      (Kcall None function environment temporaries outer)before)world)events(gateway_live terminal next)->
  exists prefix suffix value memory current,
    events=prefix++suffix /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal(gateway_header_function writer))arguments Kstop before)world)prefix
      (gateway_live(Returnstate value Kstop memory)current) /\
    gateway_steps backend ge
      (gateway_live(Returnstate value(Kcall None function environment temporaries outer)memory)current)suffix
      (gateway_live terminal next).
Proof.
  destruct terminal as[owner body continuation locals values target|definition actual_arguments actual_cont after|value continuation after];
    cbn[gateway_header_boundary];intro BOUNDARY;[contradiction| |subst continuation].
  - subst definition;apply gateway_header_helper_return_cut;[exact I|destruct writer;discriminate].
  - apply gateway_return_cut;[exact I|cbn;lia].
Qed.

Theorem gateway_header_caller_return_cut {World Event}(backend:gateway_backend World Event)ge
    property(CLOSED:gateway_ambient_closed backend property)value function environment temporaries outer
    before world events terminal next:
  gateway_header_boundary terminal->property before world->
  gateway_steps backend ge
    (gateway_live(Returnstate value(Kcall None function environment temporaries outer)before)world)events(gateway_live terminal next)->
  exists pending suffix memory current,
    events=pending++gateway_source E0::suffix /\Forall(fun event=>event=gateway_ambient)pending /\
    gateway_steps backend ge
      (gateway_live(Returnstate value(Kcall None function environment temporaries outer)before)world)pending
      (gateway_live(Returnstate value(Kcall None function environment temporaries outer)memory)current) /\
    property memory current /\
    gateway_steps backend ge(gateway_live(State function Sskip outer environment temporaries memory)current)suffix
      (gateway_live terminal next).
Proof.
  intro BOUNDARY;revert before world.
  induction events as[|event rest IH];intros before world READY RUN.
  - inversion RUN;subst;discriminate BOUNDARY.
  - inversion RUN as[|first observed middle remaining last STEP TAIL];subst.
    destruct(gateway_nonprimitive_step backend ge
      (Returnstate value(Kcall None function environment temporaries outer)before)world event middle ltac:(cbn;tauto)STEP)
      as[[trace[actual[EVENT[REAL TARGET]]]]|
        [[changed[current[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
    + inversion REAL;subst;exists[],rest,before,world;cbn.
      split;[reflexivity|]. split;[constructor|]. split;[constructor|]. split;assumption.
    + destruct(IH changed current(CLOSED _ _ _ _ READY INTERFERENCE)TAIL)
        as(pending&suffix&memory&owner&EVENTS&AMBIENT&PREFIX&FINAL&SUFFIX).
      exists(gateway_ambient::pending),suffix,memory,owner;split;[cbn;congruence|].
      split;[constructor;[reflexivity|exact AMBIENT]|]. split.
      * econstructor;[apply gateway_interleaved;exact INTERFERENCE|exact PREFIX].
      * split;assumption.
    + destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD];discriminate.
Qed.
