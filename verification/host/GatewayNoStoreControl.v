(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Source control certificates exclude own C assignments. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewayMachine GatewayFrames GatewayFramedRuntime GatewayPure.
Import ListNotations.

Definition gateway_not_assignment source : Prop :=
  match source with State _ (Sassign _ _) _ _ _ _ => False | _ => True end.

(* This is a source safety certificate, without a termination assertion. Each
   internal successor must follow its actual Clight step. SDK resumptions retain
   the same API occurrence and may change memory unless that API's own law says
   otherwise. The application producer supplies every control constructor. *)
CoInductive gateway_nostore_control {World Event} (backend : gateway_backend World Event) (ge : Clight.genv) :
    (mem -> World -> Prop) -> Clight.state -> Prop :=
| gateway_nostore_source : forall property source,
    gateway_ambient_closed backend property -> ~ gateway_at_primitive source -> gateway_not_assignment source ->
    (forall before world observed target, property before world ->
      step2 ge (gateway_replace_memory source before) observed target ->
      exists next, next (memory_of target) world /\ gateway_nostore_control backend ge next target) ->
    gateway_nostore_control backend ge property source
| gateway_nostore_external : forall property ef types result_type convention arguments continuation memory,
    gateway_ambient_closed backend property ->
    (forall before world result after next observed,
      property before world ->
      gateway_external backend ef types result_type convention arguments before world result after next observed ->
      exists following, following after next /\
        gateway_nostore_control backend ge following (Returnstate result continuation after)) ->
    gateway_nostore_control backend ge property
      (Callstate (External ef types result_type convention) arguments continuation memory).

Lemma gateway_nostore_replace {World Event} (backend : gateway_backend World Event) ge property source memory :
  gateway_nostore_control backend ge property source ->
  gateway_nostore_control backend ge property (gateway_replace_memory source memory).
Proof.
  intro CONTROL; inversion CONTROL; subst; cbn [gateway_replace_memory].
  - apply gateway_nostore_source.
    + assumption.
    + intro PRIMITIVE; apply H0; exact (proj1 (gateway_memory_replace_primitive _ _) PRIMITIVE).
    + destruct source; exact H1.
    + intros before world observed target READY STEP.
      rewrite gateway_memory_replace_twice in STEP; eapply H2; eassumption.
  - apply gateway_nostore_external; assumption.
Qed.

Definition gateway_nostore_state {World Event} (backend : gateway_backend World Event) ge (source : gateway_state World) : Prop :=
  match source with
  | gateway_live source world => exists property,
      property (memory_of source) world /\ gateway_nostore_control backend ge property source
  | gateway_dead _ _ => True
  end.

Theorem gateway_nostore_step {World Event} (backend : gateway_backend World Event) ge first observed target :
  gateway_nostore_state backend ge first -> gateway_step backend ge first observed target ->
  gateway_nostore_state backend ge target.
Proof.
  intros READY STEP; inversion STEP; subst; cbn [gateway_nostore_state] in READY |- *; try exact I.
  - destruct READY as [property [GOOD CONTROL]].
    inversion CONTROL as [p s CLOSED NOPRIM NOASSIGN SUCCESSORS |
      p ef types result_type convention arguments continuation memory CLOSED RESUME]; subst.
    + apply (SUCCESSORS (memory_of source) world observed0 next GOOD).
      rewrite gateway_memory_replace_identity; exact H0.
    + contradiction.
  - destruct READY as [property [GOOD CONTROL]].
    inversion CONTROL as [p s CLOSED NOPRIM NOASSIGN SUCCESSORS |
      p ef0 types0 result_type0 convention0 arguments0 continuation0 memory CLOSED RESUME]; subst.
    + exfalso; apply NOPRIM; exact I.
    + eapply RESUME; eassumption.
  - destruct READY as [property [GOOD CONTROL]]; inversion CONTROL; subst.
    match goal with NOPRIM : ~ gateway_at_primitive _ |- _ => exfalso; apply NOPRIM; exact I end.
  - destruct READY as [property [GOOD CONTROL]].
    exists property; rewrite gateway_replace_memory_of; split.
    + inversion CONTROL as [p s CLOSED NOPRIM NOASSIGN SUCCESSORS |
        p ef types result_type convention arguments continuation memory CLOSED RESUME]; subst;
        eapply CLOSED; eassumption.
    + apply gateway_nostore_replace; exact CONTROL.
  - exact READY.
Qed.

Theorem gateway_nostore_prefix {World Event} (backend : gateway_backend World Event) ge first observed target :
  gateway_nostore_state backend ge first -> gateway_steps backend ge first observed target ->
  gateway_nostore_state backend ge target.
Proof.
  intros READY RUN; revert READY; induction RUN; intro READY; [exact READY |].
  apply IHRUN; eapply gateway_nostore_step; eassumption.
Qed.

Theorem gateway_nostore_current {World Event} (backend : gateway_backend World Event) ge source world :
  gateway_nostore_state backend ge (gateway_live source world) -> gateway_not_assignment source.
Proof. intros [property [READY CONTROL]]; inversion CONTROL; subst; assumption || exact I. Qed.

Theorem gateway_nostore_adapt {World Event} (backend : gateway_backend World Event) ge property original source :
  gateway_ambient_closed backend property ->
  (forall memory world, property memory world -> original memory world) ->
  gateway_nostore_control backend ge original source -> gateway_nostore_control backend ge property source.
Proof.
  intros CLOSED WEAKEN CONTROL.
  inversion CONTROL as [p s _ NOPRIM NOASSIGN SUCCESSORS |
    p ef types result_type convention arguments continuation memory _ RESUME]; subst.
  - apply gateway_nostore_source; try assumption.
    intros before world observed target READY STEP; eapply SUCCESSORS; [apply WEAKEN; exact READY |exact STEP].
  - apply gateway_nostore_external; [exact CLOSED |].
    intros before world result after next observed READY OPERATION; eapply RESUME;
      [apply WEAKEN; exact READY |exact OPERATION].
Qed.

Theorem gateway_nostore_source_edge {World Event} (backend : gateway_backend World Event) ge
    property source target next :
  gateway_ambient_closed backend property -> ~ gateway_at_primitive source -> gateway_not_assignment source ->
  (forall before world, property before world -> exists after,
    store_edge ge (gateway_replace_memory source before) (gateway_replace_memory target after) /\ next after world) ->
  gateway_nostore_control backend ge next target -> gateway_nostore_control backend ge property source.
Proof.
  intros CLOSED NOAPI NOASSIGN EDGES CONTROL; apply gateway_nostore_source; try assumption.
  intros before world observed actual READY STEP.
  destruct (EDGES before world READY) as [after [[INTERNAL [CANON UNIQUE]] POST]].
  destruct (UNIQUE observed actual STEP) as [TRACE SAME]; subst actual.
  exists next; rewrite gateway_replace_memory_of; split; [exact POST |apply gateway_nostore_replace; exact CONTROL].
Qed.

Theorem gateway_nostore_source_same {World Event} (backend : gateway_backend World Event) ge property source target :
  gateway_ambient_closed backend property -> ~ gateway_at_primitive source -> gateway_not_assignment source ->
  (forall before world, property before world -> store_edge ge
    (gateway_replace_memory source before) (gateway_replace_memory target before)) ->
  gateway_nostore_control backend ge property target -> gateway_nostore_control backend ge property source.
Proof.
  intros CLOSED NOAPI NOASSIGN EDGES CONTROL; eapply gateway_nostore_source_edge; try eassumption.
  intros before world READY; exists before; split; [apply EDGES with (world := world); exact READY |exact READY].
Qed.

Theorem gateway_nostore_terminal {World Event} (backend : gateway_backend World Event) ge property value memory :
  gateway_ambient_closed backend property -> gateway_nostore_control backend ge property (Returnstate value Kstop memory).
Proof.
  intro CLOSED; apply gateway_nostore_source; [exact CLOSED |cbn; tauto |exact I |].
  intros before world observed target READY STEP; inversion STEP.
Qed.
