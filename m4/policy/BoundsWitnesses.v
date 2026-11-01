(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.bounds: Construct readable policies in the full program's initial memory. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine StoreSteps ScalarMemory.
From LeanCageMain Require Import Main MainStructure MainMemory MainPrefix MainGlobals.
From LeanCageBounds Require Import BoundsStructure BoundsMemory BoundsSource.
Import ListNotations.
Open Scope Z_scope.
Lemma writable_scalar_stores_exist b size cells m :
 Forall(scalar_valid size)cells -> Mem.range_perm m b 0 size Cur Writable ->
 exists after,scalar_stores b m cells after.
Proof.
 intros VALID;revert m;induction VALID as[|c rest VALID REST IH];intros m RANGE.
 - exists m;constructor.
 - destruct VALID as[LOW[HIGH ALIGN]].
   assert(ACCESS:Mem.valid_access m(scalar_chunk c)b(scalar_offset c)Writable).
   { split;[red;intros pos BOUND;apply RANGE;lia|exact ALIGN]. }
   destruct(Mem.valid_access_store _ _ _ _ (scalar_value c)ACCESS)as[mid STORE].
   destruct(IH mid)as[after TAIL].
   { red;intros pos BOUND;eapply Mem.perm_store_1;[exact STORE|apply RANGE;exact BOUND]. }
   exists after;econstructor;eassumption.
Qed.
Theorem allocated_policy_image values : length values=10%nat ->
 Forall(fun v=>0<=v<=Int64.max_unsigned)values ->
 exists initial m,Genv.init_mem Main.prog=Some initial /\
 policy_stores main_policy_block 0 initial values m /\ policy_image m values.
Proof.
 intros LEN RANGE;destruct native_initial_memory_exists as[initial INIT].
 destruct(native_policy_permissions initial INIT)as[WRITABLE UNUSED].
 destruct(writable_scalar_stores_exist main_policy_block 80(policy_cells 0 values)initial)
 as[m STORES].
 - apply policy_cells_valid;[lia|rewrite LEN;reflexivity].
 - red;intros pos BOUND;apply WRITABLE;lia.
 - exists initial,m;split;[exact INIT|]. split;[exact STORES|].
   eapply policy_image_stored;[exact LEN|exact RANGE|exact STORES].
Qed.
Definition bounds_fixture_temps argc bytes :=
 PTree.set _bytes(Vlong(Int64.repr bytes))
 (PTree.set _argc(Vint(Int.repr argc))(create_undef_temps(fn_temps f_main))).
Lemma bounds_fixture_registers argc bytes :
 (bounds_fixture_temps argc bytes)!_argc=Some(Vint(Int.repr argc)) /\
 (bounds_fixture_temps argc bytes)!_bytes=Some(Vlong(Int64.repr bytes)).
Proof. split;reflexivity. Qed.
Theorem bounds_allocated_execution argc bytes values :
 17<=argc<=2147483647 -> 0<=bytes<=Int64.max_unsigned -> length values=10%nat ->
 Forall(fun v=>0<=v<=Int64.max_unsigned)values ->
 exists initial m count final,Genv.init_mem Main.prog=Some initial /\
 policy_stores main_policy_block 0 initial values m /\ (count<=140)%nat /\ forall cell k,
 steps main_ge cell(live(State f_main bounds_region k empty_env(bounds_fixture_temps argc bytes)m))
 (repeat(source_step E0)count)(live(bounds_endpoint empty_env final k m(bounds_rejected argc bytes values))) /\
 (forall n,(n<=count)%nat ->
 steps main_ge cell(live(State f_main bounds_region k empty_env(bounds_fixture_temps argc bytes)m))
 (repeat(source_step E0)n++[loss_step])(dead m)).
Proof.
 intros COUNT BYTES LEN RANGE;destruct(allocated_policy_image values LEN RANGE)as[initial[m[INIT[STORES IMAGE]]]].
 destruct(bounds_region_execution empty_env(bounds_fixture_temps argc bytes)m argc bytes values COUNT BYTES
  (proj1(bounds_fixture_registers argc bytes))(proj2(bounds_fixture_registers argc bytes))eq_refl IMAGE)
 as[count[final[BOUND RUN]]].
 exists initial,m,count,final;split;[exact INIT|]. split;[exact STORES|]. split;[exact BOUND|].
 intros cell k;destruct(RUN cell k)as[PATH[MEM[PROGRESS[END LOSS]]]];auto.
Qed.
