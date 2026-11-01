(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.composition: Candidate source connection; integration review remains open. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine Deterministic StoreSteps ScalarMemory WriteAll.
From LeanCageMainNumber Require Import NumberInitial.
From LeanCageMain Require Import Main MainStructure MainMemory MainValues MainControl MainLoop MainPrefix MainFields MainEntry MainSource.
From LeanCageParent Require Import NumericFrame.
Import ListNotations.
Open Scope Z_scope.
Theorem numeric_region_framed before fields argv ofs inputs e le k :
 length inputs=10%nat -> numeric_entry_buffers before fields argv ofs inputs ->
 numeric_locals e fields -> e!_policy__1=None -> le!_argv=Some(Vptr argv ofs) ->
 exists initialized count after final,
 scalar_stores fields before(map field_cell policy_fields)initialized /\
 policy_stores main_policy_block 0 initialized(numeric_values inputs)after /\
 numeric_registers final argv ofs(Z.of_nat(length(numeric_values inputs))) /\
 final!_argc=le!_argc /\
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
 destruct(numeric_loop_framed initialized fields argv ofs 0 inputs e(numeric_start_env le)(Kseq after_numeric k)
  ltac:(lia) ltac:(rewrite LEN;reflexivity) READY LOCALS(numeric_start_registers le argv ofs ARGV))
  as[n [after [final [POLICY [REGS [FRAME LOOP]]]]]].
 exists initialized,(34+n)%nat,after,final;split;[exact STORES|]. split;[exact POLICY|]. split;[exact REGS|]. split;[rewrite FRAME;unfold numeric_start_env;WriteAll.lookup|].
 eapply store_path_trans with(n:=34%nat).
 - eapply number_path_implication;[intros current GOOD;left;exact GOOD|].
   exact(numeric_initialization_source fields before initialized e le k LOCALS GLOBAL STORES).
 - eapply number_path_implication;[intros current GOOD;right;exact GOOD|exact LOOP].
Qed.
