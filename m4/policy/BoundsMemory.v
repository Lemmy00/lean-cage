(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.bounds: Independently readable policy values and earlier numeric stores. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Clight.
Require Import ScalarMemory LocalAccess.
From LeanCageMainNumber Require Import NumberMath.
From LeanCageMain Require Import Main MainStructure MainMemory MainPrefix MainFields.
From LeanCageBounds Require Import BoundsStructure.
Import ListNotations.
Open Scope Z_scope.
Definition policy_image m values := length values=10%nat /\
 Forall(fun v=>0<=v<=Int64.max_unsigned)values /\
 forall i id,In(i,id)policy_fields ->
 Mem.loadv Mint64 m(Vptr main_policy_block(Ptrofs.repr(8*i)))=
 Some(Vlong(Int64.repr(nth(Z.to_nat i)values 0))).
Lemma policy_image_read m values e le i id : policy_image m values ->
 e!_policy__1=None -> In(i,id)policy_fields ->
 expression_value main_ge e le m(Efield(Evar _policy__1 policy_type)id tulong)
 (Vlong(Int64.repr(nth(Z.to_nat i)values 0))).
Proof.
 intros [LEN[RANGE READ]] GLOBAL IN;eapply location_read_value.
 - apply main_policy_field with(i:=i);assumption.
 - eapply deref_loc_value;[reflexivity|apply READ with(id:=id);exact IN].
Qed.
Lemma policy_image_range m values i id : policy_image m values -> In(i,id)policy_fields ->
 0<=nth(Z.to_nat i)values 0<=Int64.max_unsigned.
Proof.
 intros[LEN[RANGE READ]]IN;rewrite Forall_forall in RANGE;apply RANGE;apply nth_In.
 pose proof(policy_field_index i id IN);lia.
Qed.
Lemma policy_cells_member i values j : (j<length values)%nat ->
 In {|scalar_chunk:=Mint64;scalar_offset:=8*(i+Z.of_nat j);
 scalar_value:=Vlong(Int64.repr(nth j values 0))|}(policy_cells i values).
Proof.
 revert i j;induction values as[|v rest IH];intros i j J;[cbn in J;lia|].
 destruct j as[|j];cbn[policy_cells nth];[left;f_equal;lia|right].
 replace(i+Z.of_nat(S j))with((i+1)+Z.of_nat j)by lia;apply IH;cbn in J;lia.
Qed.
Theorem policy_image_stored before values after : length values=10%nat ->
 Forall(fun v=>0<=v<=Int64.max_unsigned)values ->
 policy_stores main_policy_block 0 before values after -> policy_image after values.
Proof.
 intros LEN RANGE STORES;split;[exact LEN|]. split;[exact RANGE|]. intros i id IN.
 pose proof(policy_field_index i id IN)as INDEX.
 pose proof(policy_cells_member 0 values(Z.to_nat i)ltac:(lia))as MEMBER.
 rewrite Z2Nat.id in MEMBER by lia;cbn[Z.add]in MEMBER.
 pose proof(policy_stores_values _ _ _ _ _ _ STORES MEMBER)as READ.
 unfold Mem.loadv;rewrite Ptrofs.unsigned_repr by(change(0<=8*i<=18446744073709551615);lia).
 destruct(zle _ _)as[LIMIT|OVER];[exact READ|exfalso;change(8*i+8>18446744073709551616)in OVER;lia].
Qed.
Theorem numeric_values_width inputs : Forall(fun v=>0<=v<=Int64.max_unsigned)(numeric_values inputs).
Proof.
 induction inputs as[|x rest IH];[constructor|]. cbn[numeric_values].
 destruct(decimal_number(input_bytes x))as[v|]eqn:VALUE;[|constructor].
 constructor;[apply decimal_number_exact in VALUE;change(0<=v<=decimal_max);tauto|exact IH].
Qed.
Theorem complete_numeric_image before inputs after : length inputs=10%nat ->
 numeric_complete inputs=true -> policy_stores main_policy_block 0 before(numeric_values inputs)after ->
 policy_image after(numeric_values inputs).
Proof.
 intros LEN COMPLETE STORES;eapply policy_image_stored;[apply numeric_complete_length in COMPLETE;lia|
 apply numeric_values_width|exact STORES].
Qed.
