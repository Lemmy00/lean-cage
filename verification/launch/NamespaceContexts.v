(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Actual namespace callbacks retain the caller's continuation. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps AST Values Memory Events Ctypes Cop Clight.
Require Import Machine LibraryMachine CallContexts.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessContexts.
From EntryNamespace Require Import NamespaceMachine.
Import ListNotations.

Lemma plug_namespace_ready state suffix :
  namespace_ready state ->namespace_ready(plug_state state suffix).
Proof. intro READY;inversion READY;subst;cbn;constructor;assumption. Qed.

Lemma unplug_namespace_ready state suffix :
  namespace_ready(plug_state state suffix) ->namespace_ready state.
Proof.
  intro READY;destruct state;cbn in READY;inversion READY;subst;constructor;assumption.
Qed.

Theorem plug_namespace_step ge cell before event after suffix :
  is_call_cont suffix ->namespace_step ge cell before event after ->
  namespace_step ge cell(plug_machine before suffix)event(plug_machine after suffix).
Proof.
  intros CALL STEP;inversion STEP;subst;cbn.
  - apply namespace_process_step,plug_process_step;assumption.
  - apply namespace_pair_step;assumption.
  - apply namespace_duplicate_step;assumption.
  - apply namespace_mask_step;assumption.
  - apply namespace_fork_step;assumption.
  - apply namespace_default_step;assumption.
  - apply namespace_pair_loss;assumption.
  - apply namespace_duplicate_loss;assumption.
  - apply namespace_mask_loss;assumption.
  - apply namespace_fork_loss;assumption.
  - apply namespace_default_loss;assumption.
  - apply namespace_wait_step,plug_namespace_ready;assumption.
Qed.

Theorem unplug_namespace_step ge cell state event after suffix :
  is_call_cont suffix ->~local_return state ->
  namespace_step ge cell(live(plug_state state suffix))event after ->
  exists next,namespace_step ge cell(live state)event next /\after=plug_machine next suffix.
Proof.
  intros CALL NOTRETURN STEP;inversion STEP;subst.
  { match goal with ORIGINAL:process_step _ _ _ _ _|-_=>
      destruct(unplug_process_step _ _ _ _ _ _ CALL NOTRETURN ORIGINAL)as[next[REAL SAME]]end.
    exists next;split;[apply namespace_process_step;exact REAL|exact SAME]. }
  all:try solve[exists(live state);split;
    [apply namespace_wait_step;eapply unplug_namespace_ready;eassumption|reflexivity]].
  all:destruct state;cbn in *;try discriminate;
    match goal with EQ:Callstate _ _ _ _=Callstate _ _ _ _|-_=>inversion EQ;subst end;
    eexists;split;[first[apply namespace_pair_step|apply namespace_duplicate_step|
      apply namespace_mask_step|apply namespace_fork_step|apply namespace_default_step|
      apply namespace_pair_loss|apply namespace_duplicate_loss|apply namespace_mask_loss|
      apply namespace_fork_loss|apply namespace_default_loss];eassumption|reflexivity].
Qed.

Theorem namespace_caller_run_decomposition ge cell suffix start events target :
  is_call_cont suffix ->
  namespace_steps ge cell(live(plug_state start suffix))events target ->
  (exists local_target,namespace_steps ge cell(live start)events local_target /\
    target=plug_machine local_target suffix) \/
  (exists before after value memory,events=before++after /\
    namespace_steps ge cell(live start)before(live(Returnstate value Kstop memory)) /\
    namespace_steps ge cell(live(Returnstate value suffix memory))after target).
Proof.
  revert start;induction events as[|event rest IH];intros start CALL RUN.
  - inversion RUN;subst;left;exists(live start);split;[constructor|reflexivity].
  - destruct(local_return_dec start)as[[value[memory SAME]]|NOTRETURN].
    + subst;right;exists[],(event::rest),value,memory;split;[reflexivity|].
      split;[constructor|exact RUN].
    + inversion RUN;subst.
      match goal with STEP:namespace_step _ _ _ _ _|-_=>
        destruct(unplug_namespace_step _ _ _ _ _ _ CALL NOTRETURN STEP)as[local_middle[REAL SAME]]end.
      subst middle;destruct local_middle as[next|memory];cbn in *.
      * match goal with TAIL:namespace_steps _ _ (live(plug_state next suffix)) _ _|-_=>
          destruct(IH next CALL TAIL)as[[last[LOCAL SAME]]|
            [before[after[value[memory[EVENTS[LOCAL CONTINUE]]]]]]]end.
        -- left;exists last;split;[econstructor;eassumption|exact SAME].
        -- right;exists(event::before),after,value,memory;split;[cbn;congruence|].
           split;[econstructor;eassumption|exact CONTINUE].
      * match goal with TAIL:namespace_steps _ _ (dead memory) _ _|-_=>
          destruct(namespace_dead_steps _ _ _ _ _ TAIL)as[EVENTS SAME]end.
        subst;left;exists(dead memory);split;[econstructor;[exact REAL|constructor]|reflexivity].
Qed.
