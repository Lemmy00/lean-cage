(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.main-inputs: Compose actual pointer initialization and all numeric calls. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine Deterministic StoreSteps ScalarMemory.
From LeanCageMainNumber Require Import NumberInitial.
From LeanCageMain Require Import Main MainStructure MainMemory MainValues MainControl MainLoop MainPrefix MainFields MainEntry.
Import ListNotations.
Open Scope Z_scope.
Definition numeric_region_memory before initialized fields inputs current :=
 field_prefix fields before policy_fields current \/
 policy_prefix main_policy_block 0 initialized(numeric_values inputs)current.
Theorem numeric_region_source before fields argv ofs inputs e le k :
 length inputs=10%nat -> numeric_entry_buffers before fields argv ofs inputs ->
 numeric_locals e fields -> e!_policy__1=None -> le!_argv=Some(Vptr argv ofs) ->
 exists initialized count after final,
 scalar_stores fields before(map field_cell policy_fields)initialized /\
 policy_stores main_policy_block 0 initialized(numeric_values inputs)after /\
 numeric_registers final argv ofs(Z.of_nat(length(numeric_values inputs))) /\
 store_path main_ge(numeric_region_memory before initialized fields inputs)
 (State f_main numeric_region k e le before)count
 (numeric_endpoint inputs e final(Kseq after_numeric k)after).
Proof.
 intros LEN OWN LOCALS GLOBAL ARGV.
 destruct OWN as[FNE[ANE[AF[BOUND[SEP[ARGS[OUTPUT RANGE]]]]]]].
 destruct(field_initialization_exists fields before RANGE)as[initialized STORES].
 assert(OWN : numeric_entry_buffers before fields argv ofs inputs).
 { split;[exact FNE|]. split;[exact ANE|]. split;[exact AF|]. split;[exact BOUND|].
   split;[exact SEP|]. split;[exact ARGS|]. split;assumption. }
 pose proof(numeric_entry_ready fields before initialized argv ofs inputs OWN STORES)as READY.
 destruct(numeric_loop_source initialized fields argv ofs 0 inputs e(numeric_start_env le)(Kseq after_numeric k)
  ltac:(lia) ltac:(rewrite LEN;reflexivity) READY LOCALS(numeric_start_registers le argv ofs ARGV))
  as[n [after [final [POLICY [REGS LOOP]]]]].
 exists initialized,(34+n)%nat,after,final;split;[exact STORES|]. split;[exact POLICY|]. split;[exact REGS|].
 eapply store_path_trans with(n:=34%nat).
 - eapply number_path_implication;[intros current GOOD;left;exact GOOD|].
   exact(numeric_initialization_source fields before initialized e le k LOCALS GLOBAL STORES).
 - eapply number_path_implication;[intros current GOOD;right;exact GOOD|exact LOOP].
Qed.
Definition numeric_outside fields b pos :=
 (b<>fields \/ pos<0 \/ 80<=pos) /\ (b<>main_policy_block \/ pos<0 \/ 80<=pos).
Lemma field_prefix_outside fields before current : field_prefix fields before policy_fields current ->
 Mem.unchanged_on(fun b pos=>b<>fields \/ pos<0 \/ 80<=pos)before current.
Proof.
 intros[done[rest[EQ STORES]]];eapply scalar_stores_outside;[exact STORES|].
 pose proof field_cells_valid as VALID;rewrite EQ,map_app,Forall_app in VALID;tauto.
Qed.
Theorem numeric_region_memory_outside before initialized fields inputs current :
 length inputs=10%nat -> scalar_stores fields before(map field_cell policy_fields)initialized ->
 numeric_region_memory before initialized fields inputs current ->
 Mem.unchanged_on(numeric_outside fields)before current.
Proof.
 intros LEN STORES[INIT|POLICY].
 - eapply Mem.unchanged_on_implies;[apply field_prefix_outside;exact INIT|]. intros b pos[LEFT RIGHT]VALID;exact LEFT.
 - eapply Mem.unchanged_on_trans.
   + eapply Mem.unchanged_on_implies;[eapply scalar_stores_outside;[exact STORES|apply field_cells_valid]|].
     intros b pos[LEFT RIGHT]VALID;exact LEFT.
   + eapply Mem.unchanged_on_implies;[apply policy_prefix_outside with(i:=0)(values:=numeric_values inputs);
      [lia|pose proof(numeric_values_length inputs);rewrite LEN in *;lia|exact POLICY]|].
     intros b pos[LEFT RIGHT]VALID;exact RIGHT.
Qed.
Theorem numeric_region_execution cell before fields argv ofs inputs e le k :
 length inputs=10%nat -> numeric_entry_buffers before fields argv ofs inputs ->
 numeric_locals e fields -> e!_policy__1=None -> le!_argv=Some(Vptr argv ofs) ->
 exists initialized count after final,
 scalar_stores fields before(map field_cell policy_fields)initialized /\
 policy_stores main_policy_block 0 initialized(numeric_values inputs)after /\
 numeric_registers final argv ofs(Z.of_nat(length(numeric_values inputs))) /\
 steps main_ge cell(live(State f_main numeric_region k e le before))(repeat(source_step E0)count)
 (live(numeric_endpoint inputs e final(Kseq after_numeric k)after)) /\
 (forall events target,steps main_ge cell(live(State f_main numeric_region k e le before))events target ->
  (length events<=count)%nat -> numeric_region_memory before initialized fields inputs(routine_memory target)) /\
 (forall n,(n<=count)%nat -> exists mid,
  steps main_ge cell(live(State f_main numeric_region k e le before))(repeat(source_step E0)n)(live mid) /\
  steps main_ge cell(live(State f_main numeric_region k e le before))(repeat(source_step E0)n++[loss_step])(dead(memory_of mid)) /\
  numeric_region_memory before initialized fields inputs(memory_of mid)).
Proof.
 intros LEN OWN LOCALS GLOBAL ARGV.
 destruct(numeric_region_source before fields argv ofs inputs e le k LEN OWN LOCALS GLOBAL ARGV)
 as[initialized[count[after[final[STORES[POLICY[REGS PATH]]]]]]].
 exists initialized,count,after,final;split;[exact STORES|]. split;[exact POLICY|]. split;[exact REGS|].
 split;[eapply store_path_actual;exact PATH|]. split.
 - intros events target RUN BOUND;eapply store_path_bounded_memory;eassumption.
 - intros n BOUND;eapply store_path_loss_every_prefix;eassumption.
Qed.
