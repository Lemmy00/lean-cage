(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.encoding: Every actual scalar initialization store in the sender's frame buffer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Slice Machine ClightSteps WriteAll StoreSteps LocalAccess WriteBytes ResultLayout
  DecoderZeros SenderSource.
Import ListNotations.
Open Scope Z_scope.
Lemma sender_zero_pointer : forall result_local bytes_local le m index,
  (index<=160)%nat ->
  expression_value result_ge (sender_env result_local bytes_local) le m
    (Ebinop Oadd (Evar _bytes (tarray tuchar 160))
      (Econst_int (Int.repr (Z.of_nat index)) tint) (tptr tuchar))
    (Vptr bytes_local (Ptrofs.repr (Z.of_nat index))).
Proof.
  intros. eapply binary_expression_value.
  - eapply location_read_value;[eapply local_location_value;unfold sender_env;WriteAll.lookup|].
    apply deref_loc_reference;reflexivity.
  - apply old_expression_value;constructor.
  - change (Some (Vptr bytes_local (Ptrofs.add Ptrofs.zero
      (Ptrofs.mul (Ptrofs.repr 1) (ptrofs_of_int Signed (Int.repr (Z.of_nat index))))))=
      Some (Vptr bytes_local (Ptrofs.repr (Z.of_nat index)))).
    rewrite small_counter_pointer by exact H;rewrite Ptrofs.add_zero_l;reflexivity.
Qed.
Lemma sender_zero_store_edge : forall result_local bytes_local le m after index k,
  (index<160)%nat -> Mem.store Mint8unsigned m bytes_local (Z.of_nat index) (Vint Int.zero)=Some after ->
  store_edge result_ge
    (State f_send_frame (sender_zero_store index) k (sender_env result_local bytes_local) le m)
    (State f_send_frame Sskip k (sender_env result_local bytes_local) le after).
Proof.
  intros result_local bytes_local le m after index k BOUND STORE.
  unfold sender_zero_store;eapply assignment_source_edge.
  - eapply pointer_location_value;apply sender_zero_pointer;lia.
  - apply old_expression_value;constructor.
  - reflexivity.
  - eapply assign_loc_value;[reflexivity|].
    assert (ZERO : cast_int_int I8 Unsigned Int.zero=Int.zero) by (vm_compute;reflexivity).
    rewrite ZERO.
    assert (REP : Ptrofs.unsigned (Ptrofs.repr (Z.of_nat index))=Z.of_nat index).
    { apply Ptrofs.unsigned_repr;change (0<=Z.of_nat index<=18446744073709551615);lia. }
    unfold Mem.storev;rewrite REP.
    destruct (zle (Z.of_nat index+size_chunk Mint8unsigned) Ptrofs.modulus) as [OK|NO];[exact STORE|].
    exfalso;change (Z.of_nat index+1>18446744073709551616) in NO;lia.
Qed.
Theorem sender_zero_sequence_path : forall (P : mem -> Prop) result_local bytes_local le k tail count index m after,
  (index+count<=160)%nat -> byte_writes m bytes_local (Z.of_nat index) (repeat Int.zero count) after -> P m ->
  (forall before next pos, P before -> Mem.store Mint8unsigned before bytes_local pos (Vint Int.zero)=Some next -> P next) ->
  exists steps, store_path result_ge P
    (State f_send_frame (sender_zero_sequence index count tail) k (sender_env result_local bytes_local) le m)
    steps (State f_send_frame tail k (sender_env result_local bytes_local) le after).
Proof.
  intros P result_local bytes_local le k tail count;induction count as [|count IH];
    intros index m after BOUND WRITES PM STABLE;cbn [repeat] in WRITES.
  - inversion WRITES;subst;exists 0%nat;constructor;exact PM.
  - inversion WRITES;subst.
    match goal with
    | STORE : Mem.store _ m _ _ _=Some ?next,
      REST : byte_writes ?next _ _ _ after |- _ =>
      assert (PN : P next) by (eapply STABLE;eassumption);
      replace (Z.of_nat index+1) with (Z.of_nat (S index)) in REST by lia;
      destruct (IH (S index) next after ltac:(lia) REST PN STABLE) as [steps PATH]
    end.
    exists (S (S (S steps)));cbn [sender_zero_sequence].
    eapply store_next;[exact PM|apply unchanged_store_edge;WriteAll.structural|].
    eapply store_next;[exact PM|apply sender_zero_store_edge;[lia|eassumption]|].
    eapply store_next;[exact PN|apply unchanged_store_edge;WriteAll.structural|exact PATH].
Qed.
