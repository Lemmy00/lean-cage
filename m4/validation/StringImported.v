(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.strings: Interpret the exact strictly imported byte computation. *)
From Stdlib Require Import ZArith Arith List Lia Bool.
From LeanImport Require Import Lean.
From LeanCageValidation Require Import ValidationImport.
Local Close Scope lean_scope.
Open Scope Z_scope.
Import ListNotations.
Definition validation_nat n := Z.of_nat(nat_of_Nat n).
Definition validation_bool (b:ValidationImport.Bool) : bool :=
 match b with Bool_false=>false|Bool_true=>true end.
Fixpoint validation_values (xs:List_inst1 Nat) : list Z := match xs with
 | List_nil_inst1 _=>[]|List_cons_inst1 _ n rest=>validation_nat n::validation_values rest end.
Lemma validation_nat_nonnegative n : 0<=validation_nat n.
Proof. unfold validation_nat;lia. Qed.
Lemma validation_nat_double n : validation_nat(double n)=2*validation_nat n.
Proof. induction n;unfold validation_nat in *;cbn[double nat_of_Nat];lia. Qed.
Lemma validation_nat_succ n : validation_nat(Nat_succ n)=1+validation_nat n.
Proof. unfold validation_nat;cbn[nat_of_Nat];lia. Qed.
Lemma validation_nat_zero : validation_nat Nat_zero=0.
Proof. reflexivity. Qed.
Lemma validation_bool_and a b : validation_bool(ValidationImport.Bool_and a b)=andb(validation_bool a)(validation_bool b).
Proof. destruct a,b;reflexivity. Qed.
Lemma validation_ble a b : validation_bool(ValidationImport.Nat_ble a b)=(validation_nat a<=?validation_nat b).
Proof.
 assert(NAT:validation_bool(ValidationImport.Nat_ble a b)=Nat.leb(nat_of_Nat a)(nat_of_Nat b)).
 { revert b;induction a as[|a IH];intros[|b];try reflexivity.
   change(validation_bool(ValidationImport.Nat_ble a b)=Nat.leb(nat_of_Nat a)(nat_of_Nat b));apply IH. }
 rewrite NAT;unfold validation_nat.
 destruct(Nat.leb(nat_of_Nat a)(nat_of_Nat b))eqn:LE;symmetry;
 [apply Nat.leb_le in LE;apply Z.leb_le|apply Nat.leb_gt in LE;apply Z.leb_gt];lia.
Qed.
Lemma validation_beq a b : validation_bool(ValidationImport.Nat_beq a b)=(validation_nat a=?validation_nat b).
Proof.
 assert(NAT:validation_bool(ValidationImport.Nat_beq a b)=Nat.eqb(nat_of_Nat a)(nat_of_Nat b)).
 { revert b;induction a as[|a IH];intros[|b];try reflexivity.
   change(validation_bool(ValidationImport.Nat_beq a b)=Nat.eqb(nat_of_Nat a)(nat_of_Nat b));apply IH. }
 rewrite NAT;unfold validation_nat.
 destruct(Nat.eqb(nat_of_Nat a)(nat_of_Nat b))eqn:EQ;symmetry;
 [apply Nat.eqb_eq in EQ;apply Z.eqb_eq|apply Nat.eqb_neq in EQ;apply Z.eqb_neq];lia.
Qed.
Lemma validation_add a b : validation_nat(ValidationImport.Nat_add a b)=validation_nat a+validation_nat b.
Proof.
 induction b as[|b IH].
 - change(validation_nat a=validation_nat a+0);lia.
 - change(validation_nat(Nat_succ(ValidationImport.Nat_add a b))=validation_nat a+validation_nat(Nat_succ b)).
   rewrite !validation_nat_succ,IH;lia.
Qed.
Lemma validation_bool_or a b : validation_bool(ValidationImport.Bool_or a b)=orb(validation_bool a)(validation_bool b).
Proof. destruct a,b;reflexivity. Qed.
Definition validation_hex_nat n := ((48<=?validation_nat n)&&(validation_nat n<=?57))||
 ((97<=?validation_nat n)&&(validation_nat n<=?102)).
Theorem validation_imported_hex_byte n : validation_bool(LeanCageM4_Digest_hexByte n)=validation_hex_nat n.
Proof.
 change(validation_bool(ValidationImport.Bool_or
 (ValidationImport.Bool_and(ValidationImport.Nat_ble 48 n)(ValidationImport.Nat_ble n 57))
 (ValidationImport.Bool_and(ValidationImport.Nat_ble 97 n)(ValidationImport.Nat_ble n 102)))=validation_hex_nat n).
 rewrite validation_bool_or,!validation_bool_and,!validation_ble;reflexivity.
Qed.
Theorem validation_imported_hex_bytes xs : validation_bool(LeanCageM4_Digest_hexBytes xs)=
 forallb(fun n=>((48<=?n)&&(n<=?57))||((97<=?n)&&(n<=?102)))(validation_values xs).
Proof.
 induction xs as[|n rest IH];[reflexivity|].
 change(validation_bool(ValidationImport.Bool_and(LeanCageM4_Digest_hexByte n)
 (LeanCageM4_Digest_hexBytes rest))=validation_hex_nat n&&
 forallb(fun n=>((48<=?n)&&(n<=?57))||((97<=?n)&&(n<=?102)))(validation_values rest)).
 rewrite validation_bool_and,validation_imported_hex_byte,IH;reflexivity.
Qed.
Theorem validation_imported_byte_count xs : validation_nat(LeanCageM4_Digest_byteCount xs)=Z.of_nat(length(validation_values xs)).
Proof.
 induction xs as[|n rest IH];[reflexivity|].
 change(validation_nat(ValidationImport.Nat_add 1(LeanCageM4_Digest_byteCount rest))=
 Z.of_nat(S(length(validation_values rest)))).
 rewrite validation_add,IH;change(validation_nat 1)with 1;lia.
Qed.
Definition validation_imported_digest xs := validation_bool(LeanCageM4_Digest_nativeDigestBytes xs).
Theorem validation_imported_digest_exact xs : validation_imported_digest xs=
 (Z.of_nat(length(validation_values xs))=?64)&&
 forallb(fun n=>((48<=?n)&&(n<=?57))||((97<=?n)&&(n<=?102)))(validation_values xs).
Proof.
 change(validation_bool(ValidationImport.Bool_and
 (ValidationImport.Nat_beq(LeanCageM4_Digest_byteCount xs)64)(LeanCageM4_Digest_hexBytes xs))=
 (Z.of_nat(length(validation_values xs))=?64)&&
 forallb(fun n=>((48<=?n)&&(n<=?57))||((97<=?n)&&(n<=?102)))(validation_values xs)).
 rewrite validation_bool_and,validation_beq,validation_imported_byte_count,validation_imported_hex_bytes;reflexivity.
Qed.
Fixpoint signed_list_eq (xs ys:list Z) : bool := match xs,ys with
 |[],[]=>true|x::xs,y::ys=>(x=?y)&&signed_list_eq xs ys|_,_=>false end.
Lemma validation_imported_equal xs ys : validation_bool(LeanCageM4_Validation_bytesEq xs ys)=
 signed_list_eq(validation_values xs)(validation_values ys).
Proof.
 revert ys;induction xs as[|x xs IH];intros[|y ys];try reflexivity.
 change(validation_bool(ValidationImport.Bool_and(ValidationImport.Nat_beq x y)
 (LeanCageM4_Validation_bytesEq xs ys))=(validation_nat x=?validation_nat y)&&
 signed_list_eq(validation_values xs)(validation_values ys)).
 rewrite validation_bool_and,validation_beq,IH;reflexivity.
Qed.
Definition validation_check kind argc xs := validation_bool(LeanCageM4_Validation_nativeStringCheck kind argc xs).
Lemma validation_mode_computation argc xs : validation_check 0 argc xs=
 (17<=?validation_nat argc)&&
 (signed_list_eq(validation_values xs)[77;51;80;76;65;78;49]||
 signed_list_eq(validation_values xs)[77;51;67;72;69;67;75;49]).
Proof.
 change(validation_bool(ValidationImport.Bool_and(ValidationImport.Nat_ble 17 argc)
 (ValidationImport.Bool_or(LeanCageM4_Validation_bytesEq xs LeanCageM4_Validation_planBytes)
 (LeanCageM4_Validation_bytesEq xs LeanCageM4_Validation_checkBytes)))=(17<=?validation_nat argc)&&
 (signed_list_eq(validation_values xs)[77;51;80;76;65;78;49]||
 signed_list_eq(validation_values xs)[77;51;67;72;69;67;75;49])).
 rewrite validation_bool_and,validation_ble,validation_bool_or,!validation_imported_equal;reflexivity.
Qed.
Lemma validation_export_computation argc xs : validation_check 1 argc xs=
 signed_list_eq(validation_values xs)[100;105;115;99;97;114;100]||
 signed_list_eq(validation_values xs)[114;101;103;117;108;97;114;45;102;105;108;101;115].
Proof.
 change(validation_bool(ValidationImport.Bool_or(LeanCageM4_Validation_bytesEq xs LeanCageM4_Validation_discardBytes)
 (LeanCageM4_Validation_bytesEq xs LeanCageM4_Validation_filesBytes))=signed_list_eq(validation_values xs)[100;105;115;99;97;114;100]||
 signed_list_eq(validation_values xs)[114;101;103;117;108;97;114;45;102;105;108;101;115]).
 rewrite validation_bool_or,!validation_imported_equal;reflexivity.
Qed.
Lemma validation_option_computation argc xs : validation_check 2 argc xs=
 signed_list_eq(validation_values xs)[110;111;110;101]||validation_imported_digest xs.
Proof.
 change(validation_bool(ValidationImport.Bool_or(LeanCageM4_Validation_bytesEq xs LeanCageM4_Validation_noneBytes)
 (LeanCageM4_Digest_nativeDigestBytes xs))=signed_list_eq(validation_values xs)[110;111;110;101]||validation_imported_digest xs).
 rewrite validation_bool_or,validation_imported_equal;reflexivity.
Qed.
Lemma validation_executable_computation argc xs : validation_check 3 argc xs=
 signed_list_eq(validation_values xs)[47;98;105;110;47;115;104]||
 signed_list_eq(validation_values xs)[47;117;115;114;47;108;111;99;97;108;47;98;105;110;47;112;121;116;104;111;110;51].
Proof.
 change(validation_bool(ValidationImport.Bool_or(LeanCageM4_Validation_bytesEq xs LeanCageM4_Validation_shellBytes)
 (LeanCageM4_Validation_bytesEq xs LeanCageM4_Validation_pythonBytes))=signed_list_eq(validation_values xs)[47;98;105;110;47;115;104]||
 signed_list_eq(validation_values xs)[47;117;115;114;47;108;111;99;97;108;47;98;105;110;47;112;121;116;104;111;110;51]).
 rewrite validation_bool_or,!validation_imported_equal;reflexivity.
Qed.
Lemma validation_other_computation argc xs kind :
 validation_check(Nat_succ(Nat_succ(Nat_succ(Nat_succ kind))))argc xs=false.
Proof. reflexivity. Qed.
