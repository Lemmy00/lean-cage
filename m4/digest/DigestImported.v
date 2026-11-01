(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.digest: Interpret the exact strictly imported byte computation. *)
From Stdlib Require Import ZArith Arith List Lia Bool.
From LeanImport Require Import Lean.
From LeanCageDigest Require Import DigestImport.
Local Close Scope lean_scope.
Open Scope Z_scope.
Import ListNotations.
Definition digest_nat n := Z.of_nat(nat_of_Nat n).
Definition digest_bool (b:DigestImport.Bool) : bool :=
 match b with Bool_false=>false|Bool_true=>true end.
Fixpoint digest_values (xs:List_inst1 Nat) : list Z := match xs with
 | List_nil_inst1 _=>[]|List_cons_inst1 _ n rest=>digest_nat n::digest_values rest end.
Lemma digest_nat_nonnegative n : 0<=digest_nat n.
Proof. unfold digest_nat;lia. Qed.
Lemma digest_nat_double n : digest_nat(double n)=2*digest_nat n.
Proof. induction n;unfold digest_nat in *;cbn[double nat_of_Nat];lia. Qed.
Lemma digest_nat_succ n : digest_nat(Nat_succ n)=1+digest_nat n.
Proof. unfold digest_nat;cbn[nat_of_Nat];lia. Qed.
Lemma digest_nat_zero : digest_nat Nat_zero=0.
Proof. reflexivity. Qed.
Lemma digest_bool_and a b : digest_bool(DigestImport.Bool_and a b)=andb(digest_bool a)(digest_bool b).
Proof. destruct a,b;reflexivity. Qed.
Lemma digest_ble a b : digest_bool(DigestImport.Nat_ble a b)=(digest_nat a<=?digest_nat b).
Proof.
 assert(NAT:digest_bool(DigestImport.Nat_ble a b)=Nat.leb(nat_of_Nat a)(nat_of_Nat b)).
 { revert b;induction a as[|a IH];intros[|b];try reflexivity.
   change(digest_bool(DigestImport.Nat_ble a b)=Nat.leb(nat_of_Nat a)(nat_of_Nat b));apply IH. }
 rewrite NAT;unfold digest_nat.
 destruct(Nat.leb(nat_of_Nat a)(nat_of_Nat b))eqn:LE;symmetry;
 [apply Nat.leb_le in LE;apply Z.leb_le|apply Nat.leb_gt in LE;apply Z.leb_gt];lia.
Qed.
Lemma digest_beq a b : digest_bool(DigestImport.Nat_beq a b)=(digest_nat a=?digest_nat b).
Proof.
 assert(NAT:digest_bool(DigestImport.Nat_beq a b)=Nat.eqb(nat_of_Nat a)(nat_of_Nat b)).
 { revert b;induction a as[|a IH];intros[|b];try reflexivity.
   change(digest_bool(DigestImport.Nat_beq a b)=Nat.eqb(nat_of_Nat a)(nat_of_Nat b));apply IH. }
 rewrite NAT;unfold digest_nat.
 destruct(Nat.eqb(nat_of_Nat a)(nat_of_Nat b))eqn:EQ;symmetry;
 [apply Nat.eqb_eq in EQ;apply Z.eqb_eq|apply Nat.eqb_neq in EQ;apply Z.eqb_neq];lia.
Qed.
Lemma digest_add a b : digest_nat(DigestImport.Nat_add a b)=digest_nat a+digest_nat b.
Proof.
 induction b as[|b IH].
 - change(digest_nat a=digest_nat a+0);lia.
 - change(digest_nat(Nat_succ(DigestImport.Nat_add a b))=digest_nat a+digest_nat(Nat_succ b)).
   rewrite !digest_nat_succ,IH;lia.
Qed.
Lemma digest_bool_or a b : digest_bool(DigestImport.Bool_or a b)=orb(digest_bool a)(digest_bool b).
Proof. destruct a,b;reflexivity. Qed.
Definition digest_hex_nat n := ((48<=?digest_nat n)&&(digest_nat n<=?57))||
 ((97<=?digest_nat n)&&(digest_nat n<=?102)).
Theorem imported_hex_byte n : digest_bool(LeanCageM4_Digest_hexByte n)=digest_hex_nat n.
Proof.
 change(digest_bool(DigestImport.Bool_or
 (DigestImport.Bool_and(DigestImport.Nat_ble 48 n)(DigestImport.Nat_ble n 57))
 (DigestImport.Bool_and(DigestImport.Nat_ble 97 n)(DigestImport.Nat_ble n 102)))=digest_hex_nat n).
 rewrite digest_bool_or,!digest_bool_and,!digest_ble;reflexivity.
Qed.
Theorem imported_hex_bytes xs : digest_bool(LeanCageM4_Digest_hexBytes xs)=
 forallb(fun n=>((48<=?n)&&(n<=?57))||((97<=?n)&&(n<=?102)))(digest_values xs).
Proof.
 induction xs as[|n rest IH];[reflexivity|].
 change(digest_bool(DigestImport.Bool_and(LeanCageM4_Digest_hexByte n)
 (LeanCageM4_Digest_hexBytes rest))=digest_hex_nat n&&
 forallb(fun n=>((48<=?n)&&(n<=?57))||((97<=?n)&&(n<=?102)))(digest_values rest)).
 rewrite digest_bool_and,imported_hex_byte,IH;reflexivity.
Qed.
Theorem imported_byte_count xs : digest_nat(LeanCageM4_Digest_byteCount xs)=Z.of_nat(length(digest_values xs)).
Proof.
 induction xs as[|n rest IH];[reflexivity|].
 change(digest_nat(DigestImport.Nat_add 1(LeanCageM4_Digest_byteCount rest))=
 Z.of_nat(S(length(digest_values rest)))).
 rewrite digest_add,IH;change(digest_nat 1)with 1;lia.
Qed.
Definition imported_digest xs := digest_bool(LeanCageM4_Digest_nativeDigestBytes xs).
Theorem imported_digest_exact xs : imported_digest xs=
 (Z.of_nat(length(digest_values xs))=?64)&&
 forallb(fun n=>((48<=?n)&&(n<=?57))||((97<=?n)&&(n<=?102)))(digest_values xs).
Proof.
 change(digest_bool(DigestImport.Bool_and
 (DigestImport.Nat_beq(LeanCageM4_Digest_byteCount xs)64)(LeanCageM4_Digest_hexBytes xs))=
 (Z.of_nat(length(digest_values xs))=?64)&&
 forallb(fun n=>((48<=?n)&&(n<=?57))||((97<=?n)&&(n<=?102)))(digest_values xs)).
 rewrite digest_bool_and,digest_beq,imported_byte_count,imported_hex_bytes;reflexivity.
Qed.
