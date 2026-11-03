(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-compiled-reporting.connection: Lift stock Clight runs to the retained byte-aware source proof. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight Smallstep.
Require Import Machine LibraryMachine LibraryControl Fault PrimitiveCalls ReportingTrace.
Import ListNotations.

Definition source_ready ge cell s :=
 (exists value,Clight.final_state s value) \/
 (exists event target,control_progress event /\ library_step ge cell (live s) event target).

Lemma ready_builtin_impossible ge cell f opt ef types expressions k e le m :
 ~source_ready ge cell (State f (Sbuiltin opt ef types expressions) k e le m).
Proof.
 intros [[value FINAL]|[event[target[PROGRESS STEP]]]];[inversion FINAL|].
 destruct(no_library_builtin_bypass ge cell f opt ef types expressions k e le m event target STEP)as[EV TARGET].
 subst event;exact(proj1(proj2 PROGRESS)eq_refl).
Qed.

Lemma stock_step_source ge cell observe initial prefix s trace next :
 runtime_contract ge cell observe initial ->
 library_steps ge cell (live initial) prefix (live s) ->
 source_ready ge cell s -> Clight.step2 ge s trace next ->
 exists event,library_step ge cell (live s) event (live next) /\
   trace_bytes observe trace=reporting_bytes event.
Proof.
 intros CONTRACT PREFIX READY STEP.
 destruct s as[f statement k env temps before|def args k before|value k before].
 - destruct statement;try solve[
     exists(original_event(source_step trace));split;
     [apply original_step;apply internal;[exact I|exact STEP]|
      assert(trace=E0)by(inversion STEP;reflexivity);subst;reflexivity]].
   exfalso;eapply ready_builtin_impossible;exact READY.
 - destruct def as[f|ef types result_type convention].
   + exists(original_event(source_step trace));split.
     * apply original_step;apply internal;[exact I|exact STEP].
     * assert(trace=E0)by(inversion STEP;reflexivity);subst;reflexivity.
   + inversion STEP;subst.
     match goal with EXTERNAL:external_call _ _ _ _ _ _ _|-_ =>
       destruct(runtime_sound _ _ _ _ CONTRACT _ _ _ _ _ _ _ _ _ _ _ PREFIX EXTERNAL)
         as[event[EFFECT BYTES]] end.
     exists event;split;[apply primitive_source_step;exact EFFECT|exact BYTES].
 - exists(original_event(source_step trace));split.
   + apply original_step;apply internal;[exact I|exact STEP].
   + assert(trace=E0)by(inversion STEP;reflexivity);subst;reflexivity.
Qed.

Lemma internal_stock_progress ge cell s event target :
 internal_state s -> control_progress event ->
 library_step ge cell(live s)event target ->
 exists trace next,Clight.step2 ge s trace next.
Proof.
 intros INSIDE PROGRESS STEP.
 destruct(internal_boundary_unchanged _ _ _ _ _ INSIDE STEP)as[old[EV OLD]].
 subst event;inversion OLD;subst;cbn [internal_state] in INSIDE;try contradiction;
   try match goal with B:boundary _ _ _|-_=>inversion B;subst;contradiction end.
 - eexists;eexists;eassumption.
 - exfalso;exact(proj1(proj2 PROGRESS)eq_refl).
Qed.

Lemma ready_stock_progress ge cell observe initial prefix s :
 runtime_contract ge cell observe initial ->
 library_steps ge cell (live initial) prefix (live s) ->
 source_ready ge cell s ->
 (exists r,Clight.final_state s r) \/ (exists trace next,Clight.step2 ge s trace next).
Proof.
 intros CONTRACT PREFIX [FINAL|[event[target[PROGRESS STEP]]]];[left;exact FINAL|].
 assert(READY:source_ready ge cell s)by(right;exists event,target;auto).
 right;destruct s as[f statement k env temps before|def args k before|value k before].
 - destruct statement;try solve[eapply internal_stock_progress;[exact I|exact PROGRESS|exact STEP]].
   exfalso;eapply ready_builtin_impossible;exact READY.
 - destruct def as[f|ef types result_type convention].
   + eapply internal_stock_progress;[exact I|exact PROGRESS|exact STEP].
   + destruct(runtime_progress _ _ _ _ CONTRACT prefix ef types result_type convention args k before PREFIX)
       as[trace[value[final EXTERNAL]]].
     exists trace,(Returnstate value k final);constructor;exact EXTERNAL.
 - eapply internal_stock_progress;[exact I|exact PROGRESS|exact STEP].
Qed.

Theorem stock_run_source ge cell observe initial :
 runtime_contract ge cell observe initial ->
 (forall events s,library_steps ge cell(live initial)events(live s)->source_ready ge cell s) ->
 forall s trace after,star(Clight.step2)ge s trace after ->
 forall prefix,library_steps ge cell(live initial)prefix(live s) ->
 exists events,library_steps ge cell(live s)events(live after) /\
   trace_bytes observe trace=reporting_trace events.
Proof.
 intros CONTRACT READY s trace after RUN;induction RUN;intros prefix PREFIX.
 - exists [];split;[constructor|reflexivity].
 - destruct(stock_step_source _ _ _ _ _ _ _ _ CONTRACT PREFIX (READY _ _ PREFIX) H)
     as[event[STEP BYTES]].
   assert(EXTENDED:library_steps ge cell(live initial)(prefix++[event])(live s2)).
   { eapply library_steps_trans;[exact PREFIX|econstructor;[exact STEP|constructor]]. }
   destruct(IHRUN _ EXTENDED)as[events[TAIL OUTPUT]].
   exists(event::events);split;[econstructor;eassumption|].
   subst t;rewrite trace_bytes_app,BYTES,OUTPUT;reflexivity.
Qed.
