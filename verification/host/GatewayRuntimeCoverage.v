(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Runtime micro-actions cover the same actual C/SDK source edges. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayRuntimeMemory.
Import ListNotations.

(* Every constructor retains its original primitive occurrence, arguments,
   before/after worlds and actual return. The memory view is additional evidence
   for that occurrence; it is not a second helper execution. *)
Inductive gateway_covered_step {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (storage : block -> Prop) (callback : mem -> list val -> mem -> val -> Prop) :
    gateway_state World -> gateway_event Event -> gateway_state World -> Prop :=
| gateway_covered_internal : forall source world observed target,
    internal_state source -> step2 ge source observed target ->
    gateway_covered_step backend ge storage callback (gateway_live source world)
      (gateway_source observed) (gateway_live target world)
| gateway_covered_external : forall ef types result_type convention arguments continuation before world
    result after next observed pool,
    gateway_external backend ef types result_type convention arguments before world result after next observed ->
    gateway_runtime_memory_steps ge storage callback before arguments after pool -> In result pool ->
    gateway_covered_step backend ge storage callback
      (gateway_live (Callstate (External ef types result_type convention) arguments continuation before) world)
      (gateway_primitive observed) (gateway_live (Returnstate result continuation after) next)
| gateway_covered_builtin : forall body destination ef types arguments values continuation environment temporaries
    before world result after next observed pool,
    eval_exprlist ge environment temporaries before arguments types values ->
    gateway_builtin backend ef types values before world result after next observed ->
    gateway_runtime_memory_steps ge storage callback before values after pool -> In result pool ->
    gateway_covered_step backend ge storage callback
      (gateway_live (State body (Sbuiltin destination ef types arguments) continuation environment temporaries before) world)
      (gateway_primitive observed)
      (gateway_live (State body Sskip continuation environment (set_opttemp destination result temporaries) after) next)
| gateway_covered_ambient : forall source world after next pool,
    gateway_interference backend (memory_of source) world after next ->
    gateway_runtime_memory_steps ge storage callback (memory_of source) [] after pool ->
    gateway_covered_step backend ge storage callback (gateway_live source world) gateway_ambient
      (gateway_live (gateway_replace_memory source after) next)
| gateway_covered_wait : forall source world,
    gateway_at_primitive source -> gateway_covered_step backend ge storage callback
      (gateway_live source world) gateway_blocked (gateway_live source world)
| gateway_covered_loss : forall source world,
    gateway_covered_step backend ge storage callback (gateway_live source world)
      gateway_lost (gateway_dead (memory_of source) world)
| gateway_covered_external_loss : forall ef types result_type convention arguments continuation before world
    result after next observed pool,
    gateway_external backend ef types result_type convention arguments before world result after next observed ->
    gateway_runtime_memory_steps ge storage callback before arguments after pool ->
    gateway_covered_step backend ge storage callback
      (gateway_live (Callstate (External ef types result_type convention) arguments continuation before) world)
      (gateway_committed_lost observed) (gateway_dead after next)
| gateway_covered_builtin_loss : forall body destination ef types arguments values continuation environment temporaries
    before world result after next observed pool,
    eval_exprlist ge environment temporaries before arguments types values ->
    gateway_builtin backend ef types values before world result after next observed ->
    gateway_runtime_memory_steps ge storage callback before values after pool ->
    gateway_covered_step backend ge storage callback
      (gateway_live (State body (Sbuiltin destination ef types arguments) continuation environment temporaries before) world)
      (gateway_committed_lost observed) (gateway_dead after next).

Inductive gateway_covered_steps {World Event} (backend : gateway_backend World Event) ge storage callback :
    gateway_state World -> list (gateway_event Event) -> gateway_state World -> Prop :=
| gateway_covered_nil : forall source, gateway_covered_steps backend ge storage callback source [] source
| gateway_covered_cons : forall first observed middle rest target,
    gateway_covered_step backend ge storage callback first observed middle ->
    gateway_covered_steps backend ge storage callback middle rest target ->
    gateway_covered_steps backend ge storage callback first (observed :: rest) target.

Theorem gateway_covered_step_actual {World Event} (backend : gateway_backend World Event) ge storage callback first observed target :
  gateway_covered_step backend ge storage callback first observed target -> gateway_step backend ge first observed target.
Proof.
  intro STEP; inversion STEP; subst; eauto using gateway_internal, gateway_external_returned,
    gateway_builtin_returned, gateway_interleaved, gateway_waiting, gateway_process_lost,
    gateway_external_committed_lost, gateway_builtin_committed_lost.
Qed.

Theorem gateway_covered_steps_actual {World Event} (backend : gateway_backend World Event) ge storage callback first observed target :
  gateway_covered_steps backend ge storage callback first observed target -> gateway_steps backend ge first observed target.
Proof.
  intro RUN; induction RUN.
  - exact (gateway_steps_nil backend ge source).
  - econstructor; [eapply gateway_covered_step_actual; exact H |exact IHRUN].
Qed.
