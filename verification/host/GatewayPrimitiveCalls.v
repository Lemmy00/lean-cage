(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Couple an actual primitive with its waiting and return suffix. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayOperations GatewayReadonly.
From HostGateway Require Import GatewayContexts GatewayStreamInterface GatewayTransferMath.
Import ListNotations.

Theorem gateway_terminal_return_ambient {World Event}(backend:gateway_backend World Event)ge
    value before world events actual after next :
  gateway_steps backend ge(gateway_live(Returnstate value Kstop before)world)events
    (gateway_live(Returnstate actual Kstop after)next) ->Forall(fun event=>event=gateway_ambient)events.
Proof.
  revert before world;induction events as[|event rest IH];intros before world RUN;
    [constructor|].
  inversion RUN;subst.
  match goal with STEP:gateway_step _ _ _ _ _|-_=>inversion STEP;subst end;cbn in *;try contradiction.
  - match goal with REAL:step2 _ (Returnstate _ Kstop _)_ _|-_=>inversion REAL end.
  - constructor;[reflexivity|eapply IH;eassumption].
  - match goal with TAIL:gateway_steps _ _ (gateway_dead _ _)_ _|-_=>
      destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD]end;discriminate.
Qed.

Lemma gateway_pending_received_empty {Event}io descriptor(events:list(gateway_event Event)) :
  Forall gateway_pending_event events ->gateway_received_bytes io descriptor events=[].
Proof.
  intro PENDING;induction PENDING;[reflexivity|]. destruct H as[SAME|SAME];subst x;cbn;exact IHPENDING.
Qed.

Lemma gateway_quiet_received_empty {Event}io descriptor(events:list(gateway_event Event)) :
  Forall gateway_quiet_event events ->gateway_received_bytes io descriptor events=[].
Proof.
  intro QUIET;induction QUIET;[reflexivity|]. destruct H as[SAME|SAME];subst x;cbn;exact IHQUIET.
Qed.

Theorem gateway_external_received_projection {World Event}(backend:gateway_backend World Event)ge io
    events returned after next prefix suffix changed changed_world observed descriptor :
  events=prefix++gateway_primitive observed::suffix ->Forall gateway_pending_event prefix ->
  gateway_steps backend ge(gateway_live(Returnstate returned Kstop changed)changed_world)suffix
    (gateway_live(Returnstate returned Kstop after)next) ->
  gateway_received_bytes io descriptor events=gateway_received_event io descriptor(gateway_primitive observed).
Proof.
  intros EVENTS PENDING SUFFIX;subst events.
  rewrite gateway_received_bytes_append,(gateway_pending_received_empty io descriptor prefix PENDING);cbn[app].
  assert(EMPTY:gateway_received_bytes io descriptor suffix=[]).
  { apply gateway_quiet_received_empty;eapply Forall_impl;
      [intros event SAME;right;exact SAME|eapply gateway_terminal_return_ambient;exact SUFFIX]. }
  change(gateway_received_event io descriptor(gateway_primitive observed)++gateway_received_bytes io descriptor suffix=
    gateway_received_event io descriptor(gateway_primitive observed)).
  rewrite EMPTY,app_nil_r;reflexivity.
Qed.

Theorem gateway_actual_primitive_context {World Event}(backend:gateway_backend World Event)ge
    external types result_type convention arguments
    (input:mem->World->Prop)(output:val->mem->World->Prop)
    (input_discipline:gateway_runtime_discipline backend input)
    (output_discipline:forall value,gateway_runtime_discipline backend(output value))
    (operation:forall before world result after next observed,
      input before world ->gateway_external backend external types result_type convention arguments
        before world result after next observed ->output result after next)
    before world events returned after next :
  input before world ->
  gateway_steps backend ge
    (gateway_live(Callstate(External external types result_type convention)arguments Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  exists prefix suffix called called_world changed changed_world observed,
    events=prefix++gateway_primitive observed::suffix /\Forall gateway_pending_event prefix /\
    gateway_steps backend ge
      (gateway_live(Callstate(External external types result_type convention)arguments Kstop before)world)prefix
      (gateway_live(Callstate(External external types result_type convention)arguments Kstop called)called_world) /\
    input called called_world /\
    gateway_external backend external types result_type convention arguments called called_world
      returned changed changed_world observed /\output returned changed changed_world /\
    gateway_steps backend ge(gateway_live(Returnstate returned Kstop changed)changed_world)suffix
      (gateway_live(Returnstate returned Kstop after)next) /\output returned after next.
Proof.
  intros READY RUN.
  destruct(gateway_external_operation_of_run backend ge external types result_type convention arguments
    before world events returned after next RUN)
    as[prefix[suffix[called[called_world[changed[changed_world[observed
      [EVENTS[PENDING[PREFIX[OPERATION SUFFIX]]]]]]]]]]].
  assert(INPUT:input called called_world).
  { eapply gateway_pending_run_ready with
      (source:=Callstate(External external types result_type convention)arguments Kstop before);
      [exact input_discipline|exact READY|exact PENDING|exact PREFIX]. }
  pose proof(operation called called_world returned changed changed_world observed INPUT OPERATION)as OUTPUT.
  assert(FINAL:output returned after next).
  { eapply gateway_readonly_run_side with(source:=Returnstate returned Kstop changed);
      [apply output_discipline|exact I|exact OUTPUT|exact SUFFIX]. }
  exists prefix,suffix,called,called_world,changed,changed_world,observed.
  split;[exact EVENTS|]. split;[exact PENDING|]. split;[exact PREFIX|]. split;[exact INPUT|].
  split;[exact OPERATION|]. split;[exact OUTPUT|]. split;assumption.
Qed.

Theorem gateway_actual_primitive_no_receive {World Event}(backend:gateway_backend World Event)ge io descriptor
    external types result_type convention arguments
    (input:mem->World->Prop)(discipline:gateway_runtime_discipline backend input)
    (operation:forall before world result after next observed,
      input before world ->gateway_external backend external types result_type convention arguments
        before world result after next observed ->io observed=None)
    before world events returned after next :
  input before world ->
  gateway_steps backend ge
    (gateway_live(Callstate(External external types result_type convention)arguments Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->gateway_received_bytes io descriptor events=[].
Proof.
  intros READY RUN.
  destruct(gateway_external_operation_of_run backend ge external types result_type convention arguments
    before world events returned after next RUN)
    as[prefix[suffix[called[called_world[changed[changed_world[observed
      [EVENTS[PENDING[PREFIX[OPERATION SUFFIX]]]]]]]]]]].
  assert(INPUT:input called called_world).
  { eapply gateway_pending_run_ready with
      (source:=Callstate(External external types result_type convention)arguments Kstop before);
      [exact discipline|exact READY|exact PENDING|exact PREFIX]. }
  pose proof(operation called called_world returned changed changed_world observed INPUT OPERATION)as IO.
  rewrite(gateway_external_received_projection backend ge io events returned after next prefix suffix
    changed changed_world observed descriptor EVENTS PENDING SUFFIX).
  unfold gateway_received_event;rewrite IO;reflexivity.
Qed.
