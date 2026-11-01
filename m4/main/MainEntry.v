(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.main-inputs:
   Ownership survives pointer initialization before parsing starts. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess WriteAll ScalarMemory.
From LeanCageMainNumber Require Import NumberMemory NumberInitial.
From LeanCageMain Require Import Main MainStructure MainMemory MainValues MainControl MainFields.
Import ListNotations.
Open Scope Z_scope.
Definition numeric_entry_buffers m fields argv ofs inputs :=
 fields<>main_policy_block /\ argv<>main_policy_block /\ argv<>fields /\
 Ptrofs.unsigned ofs+96<=Ptrofs.modulus /\
 Forall(fun x=>input_block x<>fields)inputs /\
 arguments_ready m main_policy_block argv ofs 0 inputs /\ policy_writable m main_policy_block /\
 Mem.range_perm m fields 0 80 Cur Freeable.
Lemma argument_offset_exact ofs i : Ptrofs.unsigned ofs+96<=Ptrofs.modulus -> 0<=i<10 ->
 Ptrofs.unsigned(argument_offset ofs i)=Ptrofs.unsigned ofs+8*(i+2) /\
 Ptrofs.unsigned(argument_offset ofs i)+8<=Ptrofs.modulus.
Proof.
 intros BOUND INDEX;unfold argument_offset,Ptrofs.add.
 rewrite(Ptrofs.unsigned_repr(8*(i+2)))by(change Ptrofs.max_unsigned with 18446744073709551615;lia).
 pose proof(Ptrofs.unsigned_range ofs)as RANGE.
 rewrite Ptrofs.unsigned_repr by(unfold Ptrofs.max_unsigned;lia);split;[reflexivity|lia].
Qed.
Lemma field_stores_load fields before cells after chunk b ofs value :
 scalar_stores fields before cells after -> b<>fields ->
 Mem.loadv chunk before(Vptr b ofs)=Some value -> Mem.loadv chunk after(Vptr b ofs)=Some value.
Proof.
 intros STORES NE LOAD;unfold Mem.loadv in *;destruct(zle _ _);[|discriminate].
 rewrite(scalar_stores_load_other _ _ _ _ _ _ _ STORES)by auto;exact LOAD.
Qed.
Lemma field_stores_input fields before after x :
 scalar_stores fields before(map field_cell policy_fields)after -> input_block x<>fields ->
 number_input before(input_block x)(input_offset x)(input_bytes x) ->
 number_input after(input_block x)(input_offset x)(input_bytes x).
Proof.
 intros STORES NE[BOUND[NOZERO LOAD]];split;[exact BOUND|]. split;[exact NOZERO|].
 eapply Mem.loadbytes_unchanged_on with(P:=fun b pos=>b<>fields \/ pos<0 \/ 80<=pos);[|intros;left;exact NE|exact LOAD].
 eapply scalar_stores_outside;[exact STORES|apply field_cells_valid].
Qed.
Lemma numeric_entry_ready fields before after argv ofs inputs :
 numeric_entry_buffers before fields argv ofs inputs ->
 scalar_stores fields before(map field_cell policy_fields)after ->
 numeric_buffers after main_policy_block fields argv ofs 0 inputs.
Proof.
 intros[FNE[ANE[AF[BOUND[SEPARATE[ARGS[OUTPUT RANGE]]]]]]]STORES.
 split;[exact FNE|]. split;[exact ANE|]. split;[apply initialized_fields_mapping with(before:=before);exact STORES|].
 split.
 - revert ARGS;generalize 0 as i;induction SEPARATE as[|x rest NE SEP IH];intros i ARGS;[exact I|].
   destruct ARGS as[INPUT[XP[LOAD TAIL]]];split.
   + eapply field_stores_input;eassumption.
   + split;[exact XP|]. split.
     * eapply field_stores_load;eassumption.
     * apply IH;exact TAIL.
 - intros i INDEX;destruct(OUTPUT i INDEX)as[SIZE[PERM ALIGN]];split;[exact SIZE|]. split;[|exact ALIGN].
   red;intros pos LIMIT;apply(scalar_stores_permissions _ _ _ _ STORES);apply PERM;exact LIMIT.
Qed.
Definition numeric_start_env le := PTree.set _i(Vint Int.zero)le.
Theorem numeric_initialization_source fields before after e le k :
 numeric_locals e fields -> e!_policy__1=None ->
 scalar_stores fields before(map field_cell policy_fields)after ->
 store_path main_ge(field_prefix fields before policy_fields)
 (State f_main numeric_region k e le before)34
 (State f_main numeric_loop(Kseq after_numeric k)e(numeric_start_env le)after).
Proof.
 intros[LOCAL NUMBER]GLOBAL STORES;rewrite numeric_region_structure.
 assert(GOOD : field_prefix fields before policy_fields after).
 { exists policy_fields,[];split;[rewrite app_nil_r;reflexivity|exact STORES]. }
 eapply store_path_trans with(n:=30%nat).
 - apply field_initializers_source;[apply Forall_forall;auto|exact LOCAL|exact GLOBAL|exact STORES].
 - main_route;main_route;main_next;[eapply certified_set_edge;apply old_expression_value;apply value_int|].
   main_route;apply store_done;exact GOOD.
Qed.
Lemma numeric_start_registers le argv ofs : le!_argv=Some(Vptr argv ofs) ->
 numeric_registers(numeric_start_env le)argv ofs 0.
Proof. intros ARGV;unfold numeric_start_env,numeric_registers;split;WriteAll.lookup. Qed.
