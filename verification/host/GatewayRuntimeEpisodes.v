(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Runtime callback spans keep their same actual before/after worlds. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayRuntimeMemory GatewayRuntimeCoverage.
Import ListNotations.

(* A leaf is one SDK memory action and its observed runtime-world progression.
   Application source callbacks are separate nodes, with their actual worlds;
   they cannot be replaced by an unrelated same-memory helper execution. *)
Inductive gateway_runtime_episode {World} ge storage
    (leaf : mem -> World -> mem -> World -> Prop)
    (callback : mem -> World -> list val -> mem -> World -> val -> Prop) :
    mem -> World -> list val -> mem -> World -> list val -> Prop :=
| gateway_episode_nil : forall memory world pool,
    gateway_runtime_episode ge storage leaf callback memory world pool memory world pool
| gateway_episode_leaf : forall before world pool middle current held after next final,
    leaf before world middle current ->
    gateway_runtime_memory_step ge storage (fun _ _ _ _ => False) before pool middle held ->
    gateway_runtime_episode ge storage leaf callback middle current held after next final ->
    gateway_runtime_episode ge storage leaf callback before world pool after next final
| gateway_episode_callback : forall before world pool arguments middle current result after next final,
    Forall (fun argument => In argument pool) arguments -> callback before world arguments middle current result ->
    gateway_runtime_episode ge storage leaf callback middle current (result :: pool) after next final ->
    gateway_runtime_episode ge storage leaf callback before world pool after next final.

Lemma gateway_runtime_memory_noncallback ge storage callback before pool after final :
  gateway_runtime_memory_step ge storage (fun _ _ _ _ => False) before pool after final ->
  gateway_runtime_memory_step ge storage callback before pool after final.
Proof.
  intro STEP; inversion STEP; subst; try contradiction;
    eauto using gateway_runtime_scalar, gateway_runtime_storage, gateway_runtime_argument, gateway_runtime_load,
      gateway_runtime_cast, gateway_runtime_binary, gateway_runtime_store, gateway_runtime_copy,
      gateway_runtime_bytes, gateway_runtime_allocate, gateway_runtime_release.
Qed.

Theorem gateway_runtime_episode_memory {World} ge storage leaf callback
    (projected : mem -> list val -> mem -> val -> Prop) before world pool after next final :
  (forall before world arguments after next result, callback before world arguments after next result ->
    projected before arguments after result) ->
  @gateway_runtime_episode World ge storage leaf callback before world pool after next final ->
  gateway_runtime_memory_steps ge storage projected before pool after final.
Proof.
  intros CALLBACK EPISODE; induction EPISODE.
  - constructor.
  - econstructor; [apply gateway_runtime_memory_noncallback; exact H0 |exact IHEPISODE].
  - econstructor; [eapply gateway_runtime_callback; [exact H |eapply CALLBACK; exact H0] |exact IHEPISODE].
Qed.

(* The source operation, event, returned value, memory and both World endpoints
   are unchanged. These are views of one real SDK occurrence, including loss. *)
Inductive gateway_observed_step {World Event} (backend : gateway_backend World Event) ge storage leaf callback :
    gateway_state World -> gateway_event Event -> gateway_state World -> Prop :=
| gateway_observed_internal : forall source world observed target,
    internal_state source -> step2 ge source observed target ->
    gateway_observed_step backend ge storage leaf callback (gateway_live source world)
      (gateway_source observed) (gateway_live target world)
| gateway_observed_external : forall ef types result_type convention arguments continuation before world
    result after next observed pool,
    gateway_external backend ef types result_type convention arguments before world result after next observed ->
    gateway_runtime_episode ge storage leaf callback before world arguments after next pool -> In result pool ->
    gateway_observed_step backend ge storage leaf callback
      (gateway_live (Callstate (External ef types result_type convention) arguments continuation before) world)
      (gateway_primitive observed) (gateway_live (Returnstate result continuation after) next)
| gateway_observed_builtin : forall body destination ef types arguments values continuation environment temporaries
    before world result after next observed pool,
    eval_exprlist ge environment temporaries before arguments types values ->
    gateway_builtin backend ef types values before world result after next observed ->
    gateway_runtime_episode ge storage leaf callback before world values after next pool -> In result pool ->
    gateway_observed_step backend ge storage leaf callback
      (gateway_live (State body (Sbuiltin destination ef types arguments) continuation environment temporaries before) world)
      (gateway_primitive observed)
      (gateway_live (State body Sskip continuation environment (set_opttemp destination result temporaries) after) next)
| gateway_observed_ambient : forall source world after next pool,
    gateway_interference backend (memory_of source) world after next ->
    gateway_runtime_episode ge storage leaf callback (memory_of source) world [] after next pool ->
    gateway_observed_step backend ge storage leaf callback (gateway_live source world) gateway_ambient
      (gateway_live (gateway_replace_memory source after) next)
| gateway_observed_wait : forall source world,
    gateway_at_primitive source -> gateway_observed_step backend ge storage leaf callback
      (gateway_live source world) gateway_blocked (gateway_live source world)
| gateway_observed_loss : forall source world,
    gateway_observed_step backend ge storage leaf callback (gateway_live source world)
      gateway_lost (gateway_dead (memory_of source) world)
| gateway_observed_external_loss : forall ef types result_type convention arguments continuation before world
    result after next observed pool,
    gateway_external backend ef types result_type convention arguments before world result after next observed ->
    gateway_runtime_episode ge storage leaf callback before world arguments after next pool ->
    gateway_observed_step backend ge storage leaf callback
      (gateway_live (Callstate (External ef types result_type convention) arguments continuation before) world)
      (gateway_committed_lost observed) (gateway_dead after next)
| gateway_observed_builtin_loss : forall body destination ef types arguments values continuation environment temporaries
    before world result after next observed pool,
    eval_exprlist ge environment temporaries before arguments types values ->
    gateway_builtin backend ef types values before world result after next observed ->
    gateway_runtime_episode ge storage leaf callback before world values after next pool ->
    gateway_observed_step backend ge storage leaf callback
      (gateway_live (State body (Sbuiltin destination ef types arguments) continuation environment temporaries before) world)
      (gateway_committed_lost observed) (gateway_dead after next).

Inductive gateway_observed_steps {World Event} (backend : gateway_backend World Event) ge storage leaf callback :
    gateway_state World -> list (gateway_event Event) -> gateway_state World -> Prop :=
| gateway_observed_nil : forall source, gateway_observed_steps backend ge storage leaf callback source [] source
| gateway_observed_cons : forall first observed middle rest target,
    gateway_observed_step backend ge storage leaf callback first observed middle ->
    gateway_observed_steps backend ge storage leaf callback middle rest target ->
    gateway_observed_steps backend ge storage leaf callback first (observed :: rest) target.

Theorem gateway_observed_step_memory {World Event} (backend : gateway_backend World Event) ge storage leaf callback
    projected first observed target :
  (forall before world arguments after next result, callback before world arguments after next result ->
    projected before arguments after result) ->
  gateway_observed_step backend ge storage leaf callback first observed target ->
  gateway_covered_step backend ge storage projected first observed target.
Proof.
  intros CALLBACK STEP; inversion STEP; subst;
    eauto using gateway_covered_internal, gateway_covered_external, gateway_covered_builtin,
      gateway_covered_ambient, gateway_covered_wait, gateway_covered_loss, gateway_covered_external_loss,
      gateway_covered_builtin_loss, gateway_runtime_episode_memory.
Qed.

Theorem gateway_observed_steps_memory {World Event} (backend : gateway_backend World Event) ge storage leaf callback
    projected first observed target :
  (forall before world arguments after next result, callback before world arguments after next result ->
    projected before arguments after result) ->
  gateway_observed_steps backend ge storage leaf callback first observed target ->
  gateway_covered_steps backend ge storage projected first observed target.
Proof.
  intros CALLBACK RUN; induction RUN; [constructor |].
  econstructor; [eapply gateway_observed_step_memory; [exact CALLBACK |exact H] |exact IHRUN].
Qed.
