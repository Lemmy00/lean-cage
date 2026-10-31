(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.reporting: Compose complete source procedures under their real call continuations. *)
From Coq Require Import List.
From compcert Require Import Values Memory Clight.
Require Import Machine Deterministic LibraryMachine LibraryControl CallContexts CallProgress SourceGuarantees.
Import ListNotations.
Lemma plug_routine_memory : forall s k,routine_memory (plug_machine s k)=routine_memory s.
Proof. intros [s|m] k;cbn;[apply plug_memory|reflexivity]. Qed.

Theorem call_procedure_guarantee : forall ge cell P LOCAL POST start suffix,
  is_call_cont suffix -> procedure_guarantee ge cell P LOCAL start ->
  (forall value after,LOCAL value after ->
    procedure_guarantee ge cell P POST (Returnstate value suffix after)) ->
  procedure_guarantee ge cell P POST (plug_state start suffix).
Proof.
  intros ge cell P LOCAL POST start suffix CALL [MEMORY PROGRESS] RETURN;split.
  - intros events target RUN.
    destruct (caller_run_decomposition _ _ _ _ _ _ CALL RUN)
      as [[last [PREFIX SAME]]|[before [after [value [final [ES [PREFIX TAIL]]]]]]].
    + subst target;rewrite plug_routine_memory;exact (MEMORY _ _ PREFIX).
    + apply (proj1 (RETURN value final (procedure_return_post _ _ _ _ _ _ _ PROGRESS PREFIX)) _ _ TAIL).
  - intros events current RUN.
    destruct (caller_run_decomposition _ _ _ _ _ _ CALL RUN)
      as [[last [PREFIX SAME]]|[before [after [value [final [ES [PREFIX TAIL]]]]]]].
    + destruct last as [local|m];[|discriminate]. inversion SAME;subst current.
      destruct (PROGRESS _ _ PREFIX) as [[value [after [EQ POSTCONDITION]]]|[ev [next [ORD STEP]]]].
      * subst local. change (plug_state (Returnstate value Kstop after) suffix) with (Returnstate value suffix after).
        apply (proj2 (RETURN value after POSTCONDITION) []);constructor.
      * right;exists ev,(plug_machine next suffix);split;[exact ORD|].
        exact (plug_library_step ge cell (live local) ev next suffix CALL STEP).
    + exact (proj2 (RETURN value final (procedure_return_post _ _ _ _ _ _ _ PROGRESS PREFIX)) _ _ TAIL).
Qed.

Require Import Fault.
Theorem fault_procedure_guarantee : forall cell m mode name xs ys (P : mem -> Prop),
  fault_input (Clight.globalenv Slice.prog) m mode name xs ys -> P m ->
  procedure_guarantee (Clight.globalenv Slice.prog) cell P
    (fun value after=>value=fault_value xs ys /\ after=m) (fault_initial name Kstop m).
Proof.
  intros cell m mode name xs ys P OWN PM;split.
  - intros events target RUN.
    pose proof (fault_all_prefixes _ _ _ _ _ _ _ _ OWN RUN) as [MEM _]. rewrite MEM;exact PM.
  - intros events s RUN.
    destruct (fault_defined_prefix _ _ _ _ _ _ _ _ OWN RUN) as [EQ|PROGRESS].
    + left;exists (fault_value xs ys),m;auto.
    + right;exact PROGRESS.
Qed.
