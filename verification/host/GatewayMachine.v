(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Actual source control and per-operation runtime effects share one run. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine.
Import ListNotations.

Record gateway_backend (World Event:Type) := {
  gateway_external : external_function -> list type -> type -> calling_convention ->
    list val -> mem -> World -> val -> mem -> World -> Event -> Prop;
  gateway_builtin : external_function -> list type -> list val -> mem -> World ->
    val -> mem -> World -> Event -> Prop;
  gateway_interference : mem -> World -> mem -> World -> Prop
}.

Arguments gateway_external {World Event} _ _ _ _ _ _ _ _ _ _ _ _.
Arguments gateway_builtin {World Event} _ _ _ _ _ _ _ _ _ _.
Arguments gateway_interference {World Event} _ _ _ _ _.

Inductive gateway_state (World:Type) :=
| gateway_live (source:Clight.state)(world:World)
| gateway_dead (memory:mem)(world:World).

Arguments gateway_live {World} _ _.
Arguments gateway_dead {World} _ _.

Inductive gateway_event (Event:Type) :=
| gateway_source (observed:trace)
| gateway_primitive (observed:Event)
| gateway_ambient
| gateway_blocked
| gateway_lost
| gateway_committed_lost (observed:Event).

Arguments gateway_source {Event} _.
Arguments gateway_primitive {Event} _.
Arguments gateway_ambient {Event}.
Arguments gateway_blocked {Event}.
Arguments gateway_lost {Event}.
Arguments gateway_committed_lost {Event} _.

Definition gateway_replace_memory (source:Clight.state)(memory:mem) : Clight.state :=
  match source with
  | State function body continuation environment temporaries _ =>
    State function body continuation environment temporaries memory
  | Callstate definition arguments continuation _ =>Callstate definition arguments continuation memory
  | Returnstate value continuation _ =>Returnstate value continuation memory
  end.

Definition gateway_at_primitive (source:Clight.state) : Prop :=
  match source with
  | Callstate(External _ _ _ _) _ _ _ =>True
  | State _ (Sbuiltin _ _ _ _) _ _ _ _ =>True
  | _ =>False
  end.

Inductive gateway_step {World Event}(backend:gateway_backend World Event)(ge:Clight.genv) :
    gateway_state World -> gateway_event Event -> gateway_state World -> Prop :=
| gateway_internal : forall source world observed next,
    internal_state source -> step2 ge source observed next ->
    gateway_step backend ge (gateway_live source world)(gateway_source observed)(gateway_live next world)
| gateway_external_returned : forall ef types result_type convention arguments continuation before world
    result after next observed,
    gateway_external backend ef types result_type convention arguments before world result after next observed ->
    gateway_step backend ge
      (gateway_live(Callstate(External ef types result_type convention)arguments continuation before)world)
      (gateway_primitive observed)(gateway_live(Returnstate result continuation after)next)
| gateway_builtin_returned : forall function destination ef types arguments values continuation
    environment temporaries before world result after next observed,
    eval_exprlist ge environment temporaries before arguments types values ->
    gateway_builtin backend ef types values before world result after next observed ->
    gateway_step backend ge
      (gateway_live(State function(Sbuiltin destination ef types arguments)continuation
        environment temporaries before)world)
      (gateway_primitive observed)
      (gateway_live(State function Sskip continuation environment(set_opttemp destination result temporaries)after)next)
| gateway_interleaved : forall source world after next,
    gateway_interference backend (memory_of source)world after next ->
    gateway_step backend ge (gateway_live source world)gateway_ambient
      (gateway_live(gateway_replace_memory source after)next)
| gateway_waiting : forall source world,
    gateway_at_primitive source ->
    gateway_step backend ge (gateway_live source world)gateway_blocked(gateway_live source world)
| gateway_process_lost : forall source world,
    gateway_step backend ge (gateway_live source world)gateway_lost(gateway_dead(memory_of source)world)
| gateway_external_committed_lost : forall ef types result_type convention arguments continuation
    before world result after next observed,
    gateway_external backend ef types result_type convention arguments before world result after next observed ->
    gateway_step backend ge
      (gateway_live(Callstate(External ef types result_type convention)arguments continuation before)world)
      (gateway_committed_lost observed)(gateway_dead after next)
| gateway_builtin_committed_lost : forall function destination ef types arguments values continuation
    environment temporaries before world result after next observed,
    eval_exprlist ge environment temporaries before arguments types values ->
    gateway_builtin backend ef types values before world result after next observed ->
    gateway_step backend ge
      (gateway_live(State function(Sbuiltin destination ef types arguments)continuation
        environment temporaries before)world)
      (gateway_committed_lost observed)(gateway_dead after next).

Inductive gateway_steps {World Event}(backend:gateway_backend World Event)(ge:Clight.genv) :
    gateway_state World -> list(gateway_event Event) -> gateway_state World -> Prop :=
| gateway_steps_nil : forall state,gateway_steps backend ge state [] state
| gateway_steps_cons : forall first observed middle rest last,
    gateway_step backend ge first observed middle -> gateway_steps backend ge middle rest last ->
    gateway_steps backend ge first(observed::rest)last.

Theorem gateway_no_stock_external {World Event}(backend:gateway_backend World Event)ge
    ef types result_type convention arguments continuation memory world observed target :
  ~gateway_step backend ge
    (gateway_live(Callstate(External ef types result_type convention)arguments continuation memory)world)
    (gateway_source observed)target.
Proof. intro STEP;inversion STEP;subst;contradiction. Qed.

Theorem gateway_dead_cannot_resume {World Event}(backend:gateway_backend World Event)ge memory world observed target :
  ~gateway_step backend ge (gateway_dead memory world)observed target.
Proof. intro STEP;inversion STEP. Qed.

Theorem gateway_steps_append {World Event}(backend:gateway_backend World Event)ge first prefix middle suffix last :
  gateway_steps backend ge first prefix middle -> gateway_steps backend ge middle suffix last ->
  gateway_steps backend ge first(prefix++suffix)last.
Proof. intros PREFIX SUFFIX;induction PREFIX;cbn;eauto using gateway_steps_cons. Qed.
