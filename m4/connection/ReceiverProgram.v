(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.reads: Whole actual receiver safety from independent inputs, retaining all read/close outcomes. *)
From Coq Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Clight.
Require Import Slice Machine StoreSteps WriteAll Deterministic ResultLayout LibraryMachine CallProgress
  SourceGuarantees FinishMemory ReceiverSource ReceiverReadSource ReceiverReadMemory
  ReceiverRouting ReceiverReadReturns ReceiverReadStep ReceiverReadGuarantee
  ReceiverMemory ReceiverInput ReceiverChoice ReceiverConstruction ReceiverTerminal ReceiverEntry.
Import ListNotations.
Open Scope Z_scope.
Definition receiver_post b output ofs bad entered done status uid run value after :=
  exists bytes reason,receiver_stop_valid reason bytes /\
    receiver_choice_result output ofs(receiver_select bytes(receiver_bad bad reason)entered done status)uid run b value after.
Theorem receiver_program_guarantee : forall cell base output ofs fd bad entered done status run uid,
  receiver_input cell base output ofs run uid ->
  exists b allocated,receiver_allocations base b allocated /\
    procedure_guarantee result_ge cell(receiver_preserved cell base output ofs)
      (receiver_post b output ofs bad entered done status uid run)
      (receiver_initial output ofs fd bad entered done status Kstop base).
Proof.
  intros cell base output ofs fd bad entered done status run uid INPUT.
  destruct(receiver_entry_prepared cell base output ofs fd bad entered done status run uid INPUT)
    as[b[allocated[initialized[count[ALLOC[PATH[LIVE[BUFFER REGS]]]]]]]].
  exists b,allocated;split;[exact ALLOC|].
  eapply source_path_guarantee;[exact PATH|].
  eapply receiver_read_continuation_weaken with
    (P:=receiver_live_memory cell base b output ofs fd)
    (original:=receiver_temps output ofs fd bad entered done status)(bad:=bad)(bytes:=[]).
  - apply receiver_live_read;exact(proj1(proj2 INPUT)).
  - apply receiver_live_descriptor.
  - intros m [OLD REST];apply receiver_sender_preserved;exact OLD.
  - eapply receiver_loop_routed;[exact LIVE|exact(proj2(proj2(proj2 LIVE)))|exact BUFFER|exact REGS].
  - intros bytes stopped[le[m[reason[EQ[STOP[LIVE'[BUFFER'[KEEP[BAD USED]]]]]]]]];subst stopped.
    eapply procedure_guarantee_consequence.
    + eapply receiver_terminal_guarantee.
      * exact INPUT.
      * exact LIVE'.
      * exact BUFFER'.
      * rewrite(KEEP __res ltac:(cbn;tauto));unfold receiver_temps;WriteAll.lookup.
      * exact BAD.
      * rewrite(KEEP _entered ltac:(cbn;tauto));unfold receiver_temps;WriteAll.lookup.
      * rewrite(KEEP _leader_done ltac:(cbn;tauto));unfold receiver_temps;WriteAll.lookup.
      * rewrite(KEEP _leader_status ltac:(cbn;tauto));unfold receiver_temps;WriteAll.lookup.
      * exact USED.
    + intros;assumption.
    + intros value after POST;exists bytes,reason;split;assumption.
Qed.
Theorem receiver_return_source_exact : forall cell base output ofs fd bad entered done status run uid events value after,
  receiver_input cell base output ofs run uid ->
  library_steps result_ge cell(live(receiver_initial output ofs fd bad entered done status Kstop base))events
    (live(Returnstate value Kstop after)) ->
  exists b allocated,receiver_allocations base b allocated /\
    receiver_post b output ofs bad entered done status uid run value after /\
    receiver_preserved cell base output ofs after.
Proof.
  intros cell base output ofs fd bad entered done status run uid events value after INPUT RUN.
  destruct(receiver_program_guarantee cell base output ofs fd bad entered done status run uid INPUT)as[b[allocated[ALLOC[MEMORY PROGRESS]]]].
  exists b,allocated;split;[exact ALLOC|]. split.
  - eapply procedure_return_post;[exact PROGRESS|exact RUN].
  - exact(MEMORY _ _ RUN).
Qed.
Theorem receiver_all_prefixes : forall cell base output ofs fd bad entered done status run uid events target,
  receiver_input cell base output ofs run uid ->
  library_steps result_ge cell(live(receiver_initial output ofs fd bad entered done status Kstop base))events target ->
  receiver_preserved cell base output ofs(routine_memory target).
Proof.
  intros cell base output ofs fd bad entered done status run uid events target INPUT RUN.
  destruct(receiver_program_guarantee cell base output ofs fd bad entered done status run uid INPUT)as[b[allocated[ALLOC[MEMORY PROGRESS]]]].
  exact(MEMORY _ _ RUN).
Qed.
Theorem receiver_defined_prefix : forall cell base output ofs fd bad entered done status run uid events s,
  receiver_input cell base output ofs run uid ->
  library_steps result_ge cell(live(receiver_initial output ofs fd bad entered done status Kstop base))events(live s) ->
  (exists b allocated value after,receiver_allocations base b allocated /\ s=Returnstate value Kstop after /\
    receiver_post b output ofs bad entered done status uid run value after) \/
  (exists ev target,LibraryControl.control_progress ev /\ library_step result_ge cell(live s)ev target).
Proof.
  intros cell base output ofs fd bad entered done status run uid events s INPUT RUN.
  destruct(receiver_program_guarantee cell base output ofs fd bad entered done status run uid INPUT)as[b[allocated[ALLOC[MEMORY PROGRESS]]]].
  destruct(PROGRESS _ _ RUN)as[[value[after[EQ POST]]]|NEXT].
  - left;exists b,allocated,value,after;auto.
  - right;exact NEXT.
Qed.
