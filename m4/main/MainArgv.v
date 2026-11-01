(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.main-inputs:
   Allocate and initialize the actual pointer-table representation. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Require Import ScalarMemory.
From LeanCageMainNumber Require Import NumberMemory.
From LeanCageMain Require Import MainMemory MainPacked.
Import ListNotations.
Open Scope Z_scope.
Fixpoint argv_cells i inputs := match inputs with
 | []=>[]|x::rest=>{|scalar_chunk:=Mptr;scalar_offset:=8*(i+2);scalar_value:=input_pointer x|}::argv_cells(i+1)rest end.
Lemma argv_cells_valid i inputs : 0<=i -> i+Z.of_nat(length inputs)<=10 ->
 Forall(scalar_valid 96)(argv_cells i inputs).
Proof.
 revert i;induction inputs as[|x rest IH];intros i LOW HIGH;[constructor|]. constructor.
 - change(0<=8*(i+2) /\ 8*(i+2)+8<=96 /\ (8|8*(i+2))).
   split;[lia|]. split;[change(i+Z.of_nat(S(length rest))<=10)in HIGH;lia|exists(i+2);ring].
 - apply IH;change(i+Z.of_nat(S(length rest))<=10)in HIGH;lia.
Qed.
Lemma argv_cells_lower i inputs : Forall(fun c=>8*(i+2)<=scalar_offset c)(argv_cells i inputs).
Proof.
 revert i;induction inputs as[|x rest IH];intros i;[constructor|]. constructor;[change(8*(i+2)<=8*(i+2));lia|].
 eapply Forall_impl with(P:=fun c=>8*(i+1+2)<=scalar_offset c);[intros c BOUND;lia|exact(IH(i+1))].
Qed.
Lemma argv_cells_ordered i inputs : scalar_orderedb(argv_cells i inputs)=true.
Proof.
 revert i;induction inputs as[|x rest IH];intros i;[reflexivity|].
 cbn[argv_cells scalar_orderedb];apply andb_true_iff;split;[|apply IH].
 apply forallb_forall;intros c IN;apply Z.leb_le.
 pose proof(argv_cells_lower(i+1)rest)as LOWER;rewrite Forall_forall in LOWER;specialize(LOWER c IN).
 change(8*(i+2)+8<=scalar_offset c);lia.
Qed.
Lemma arguments_ready_from_cells m policy argv i inputs :
 0<=i -> i+Z.of_nat(length inputs)<=10 -> inputs_owned m inputs ->
 Forall(fun x=>input_block x<>policy)inputs ->
 Forall(fun c=>Mem.load(scalar_chunk c)m argv(scalar_offset c)=
  Some(Val.load_result(scalar_chunk c)(scalar_value c)))(argv_cells i inputs) ->
 arguments_ready m policy argv Ptrofs.zero i inputs.
Proof.
 revert i;induction inputs as[|x rest IH];intros i LOW HIGH OWN SEP LOADS;[exact I|].
 inversion OWN as[|? ? INPUT TAIL];subst;inversion SEP as[|? ? NE REST];subst;inversion LOADS as[|? ? LOAD MORE];subst.
 split;[exact INPUT|]. split;[exact NE|]. split.
 - unfold argument_offset;rewrite Ptrofs.add_zero_l;unfold Mem.loadv.
   rewrite Ptrofs.unsigned_repr by(change Ptrofs.max_unsigned with 18446744073709551615;change(i+Z.of_nat(S(length rest))<=10)in HIGH;lia).
   destruct(zle _ _)as[BOUND|OVER].
   + exact LOAD.
   + change(8*(i+2)+8>Ptrofs.modulus)in OVER;change Ptrofs.modulus with 18446744073709551616 in OVER.
     change(i+Z.of_nat(S(length rest))<=10)in HIGH;lia.
 - apply IH;try assumption;change(i+Z.of_nat(S(length rest))<=10)in HIGH;lia.
Qed.
Theorem initialized_arguments argv before after policy inputs :
 length inputs=10%nat -> scalar_stores argv before(argv_cells 0 inputs)after ->
 inputs_owned after inputs -> Forall(fun x=>input_block x<>policy)inputs ->
 arguments_ready after policy argv Ptrofs.zero 0 inputs.
Proof.
 intros LEN STORES OWN SEP;apply arguments_ready_from_cells;[lia|rewrite LEN;lia|exact OWN|exact SEP|].
 apply Forall_forall;intros c IN;eapply scalar_stores_fields;
 [exact STORES|apply scalar_orderedb_sound;apply argv_cells_ordered|exact IN].
Qed.
Theorem argv_initialization_exists argv before inputs : length inputs=10%nat ->
 Mem.range_perm before argv 0 96 Cur Freeable -> exists after,scalar_stores argv before(argv_cells 0 inputs)after.
Proof.
 intros LEN RANGE;apply scalar_stores_exist with(size:=96);
 [apply argv_cells_valid;[lia|rewrite LEN;lia]|exact RANGE].
Qed.
