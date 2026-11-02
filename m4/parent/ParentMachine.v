(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Preserve actual observations and ordered source memory. *)
From Stdlib Require Import ZArith List String Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import IO Machine Library LibraryMachine.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine StringPath.
From LeanCageValidation Require Import ValidationStructure.
Import ListNotations.
Open Scope Z_scope.
Definition getppid_definition : Clight.fundef := External
 (EF_external "getppid" (mksignature [] Xint cc_default)) [] tint cc_default.
Theorem getppid_binding :
 Genv.find_symbol main_ge _getppid=Some(symbol_block _getppid) /\
 Genv.find_funct main_ge(Vptr(symbol_block _getppid)Ptrofs.zero)=Some getppid_definition.
Proof. split;reflexivity. Qed.
Inductive parent_event := previous (ev:string_event) | parent_observed(value:int) | parent_wait.
Inductive parent_step ge cell : machine->parent_event->machine->Prop :=
 | previous_step : forall s ev target,string_step ge cell s ev target->parent_step ge cell s(previous ev)target
 | observe_parent : forall k m value,parent_step ge cell(live(Callstate getppid_definition [] k m))
   (parent_observed value)(live(Returnstate(Vint value)k m))
 | wait_parent : forall k m,parent_step ge cell(live(Callstate getppid_definition [] k m))
   parent_wait(live(Callstate getppid_definition [] k m)).
Inductive parent_steps ge cell : machine->list parent_event->machine->Prop :=
 | parent_steps_nil : forall s,parent_steps ge cell s [] s
 | parent_steps_cons : forall s ev mid rest target,parent_step ge cell s ev mid->parent_steps ge cell mid rest target->
   parent_steps ge cell s(ev::rest)target.
Definition parent_loss := previous string_loss.
Definition parent_waiting ev := match ev with previous ev=>string_waiting ev|parent_wait=>true|_=>false end.
Definition parent_cost events := List.length(filter(fun ev=>negb(parent_waiting ev))events).
Lemma getppid_old_only_loss ge cell k m ev target :
 string_step ge cell(live(Callstate getppid_definition [] k m))ev target->ev=string_loss /\target=dead m.
Proof.
 intros STEP;inversion STEP;subst;try discriminate.
 inversion H;subst;try discriminate.
 - match goal with H:Machine.step _ _ _ _ _|-_=>inversion H;subst;cbn in * end;
   try contradiction;auto;
   match goal with H:boundary _ _ _|-_=>inversion H;subst;destruct(operation q);discriminate end.
 - match goal with H:library_ready _ _|-_=>inversion H end.
Qed.
Theorem getppid_cases ge cell k m ev target :
 parent_step ge cell(live(Callstate getppid_definition [] k m))ev target->
 (exists value,ev=parent_observed value /\target=live(Returnstate(Vint value)k m)) \/
 (ev=parent_wait /\target=live(Callstate getppid_definition [] k m)) \/
 (ev=parent_loss /\target=dead m).
Proof.
 intros STEP;inversion STEP;subst.
 - destruct(getppid_old_only_loss _ _ _ _ _ _ H)as[EV TARGET];subst;right;right;auto.
 - left;eexists;split;reflexivity.
 - right;left;auto.
Qed.
Lemma parent_dead_terminal ge cell m ev target : ~parent_step ge cell(dead m)ev target.
Proof. intros STEP;inversion STEP;subst;eapply string_dead_terminal;eassumption. Qed.
Lemma parent_dead_steps ge cell m events target : parent_steps ge cell(dead m)events target->events=[] /\target=dead m.
Proof. intros RUN;inversion RUN;subst;auto;exfalso;eapply parent_dead_terminal;eassumption. Qed.
Lemma parent_loss_everywhere ge cell s : parent_step ge cell(live s)parent_loss(dead(memory_of s)).
Proof. constructor;apply string_loss_everywhere. Qed.
Lemma parent_steps_trans ge cell a first b second c : parent_steps ge cell a first b->parent_steps ge cell b second c->
 parent_steps ge cell a(first++second)c.
Proof. intros AB BC;induction AB;cbn;auto;econstructor;eauto. Qed.
Theorem prior_runs_preserved ge cell s events target : string_steps ge cell s events target->
 parent_steps ge cell s(map previous events)target.
Proof. intros RUN;induction RUN;cbn;[constructor|];econstructor;[constructor;exact H|exact IHRUN]. Qed.
Theorem parent_wait_then_loss ge cell k m n : parent_steps ge cell(live(Callstate getppid_definition [] k m))
 (repeat parent_wait n++[parent_loss])(dead m).
Proof. induction n;cbn;[econstructor;[apply parent_loss_everywhere|constructor]|econstructor;[constructor|exact IHn]]. Qed.
Theorem parent_observations_unconstrained ge cell k m first second :
 parent_step ge cell(live(Callstate getppid_definition [] k m))(parent_observed first)(live(Returnstate(Vint first)k m)) /\
 parent_step ge cell(live(Callstate getppid_definition [] k m))(parent_observed second)(live(Returnstate(Vint second)k m)).
Proof. split;constructor. Qed.
