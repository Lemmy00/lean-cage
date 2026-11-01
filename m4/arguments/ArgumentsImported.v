(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.arguments: Interpret the strictly imported length computation. *)
From Stdlib Require Import ZArith Arith List Lia Bool.
From LeanImport Require Import Lean.
From LeanCageArguments Require Import ArgumentsImport.
Local Close Scope lean_scope.
Open Scope Z_scope.
Import ListNotations.
Definition argument_nat n := Z.of_nat(nat_of_Nat n).
Definition argument_bool (b:ArgumentsImport.Bool) : bool :=
 match b with Bool_false=>false|Bool_true=>true end.
Fixpoint argument_values (xs:List_inst1 Nat) : list Z := match xs with
 | List_nil_inst1 _=>[]|List_cons_inst1 _ n rest=>argument_nat n::argument_values rest end.
Lemma argument_nat_nonnegative n : 0<=argument_nat n.
Proof. unfold argument_nat;lia. Qed.
Lemma argument_nat_double n : argument_nat(double n)=2*argument_nat n.
Proof. induction n;unfold argument_nat in *;cbn[double nat_of_Nat];lia. Qed.
Lemma argument_nat_succ n : argument_nat(Nat_succ n)=1+argument_nat n.
Proof. unfold argument_nat;cbn[nat_of_Nat];lia. Qed.
Lemma argument_nat_zero : argument_nat Nat_zero=0.
Proof. reflexivity. Qed.
Lemma argument_bool_and a b : argument_bool(ArgumentsImport.Bool_and a b)=andb(argument_bool a)(argument_bool b).
Proof. destruct a,b;reflexivity. Qed.
Lemma argument_ble a b : argument_bool(ArgumentsImport.Nat_ble a b)=(argument_nat a<=?argument_nat b).
Proof.
 assert(NAT:argument_bool(ArgumentsImport.Nat_ble a b)=Nat.leb(nat_of_Nat a)(nat_of_Nat b)).
 { revert b;induction a as[|a IH];intros[|b];try reflexivity.
   change(argument_bool(ArgumentsImport.Nat_ble a b)=Nat.leb(nat_of_Nat a)(nat_of_Nat b));apply IH. }
 rewrite NAT;unfold argument_nat.
 destruct(Nat.leb(nat_of_Nat a)(nat_of_Nat b))eqn:LE;symmetry;
 [apply Nat.leb_le in LE;apply Z.leb_le|apply Nat.leb_gt in LE;apply Z.leb_gt];lia.
Qed.
Lemma argument_beq a b : argument_bool(ArgumentsImport.Nat_beq a b)=(argument_nat a=?argument_nat b).
Proof.
 assert(NAT:argument_bool(ArgumentsImport.Nat_beq a b)=Nat.eqb(nat_of_Nat a)(nat_of_Nat b)).
 { revert b;induction a as[|a IH];intros[|b];try reflexivity.
   change(argument_bool(ArgumentsImport.Nat_beq a b)=Nat.eqb(nat_of_Nat a)(nat_of_Nat b));apply IH. }
 rewrite NAT;unfold argument_nat.
 destruct(Nat.eqb(nat_of_Nat a)(nat_of_Nat b))eqn:EQ;symmetry;
 [apply Nat.eqb_eq in EQ;apply Z.eqb_eq|apply Nat.eqb_neq in EQ;apply Z.eqb_neq];lia.
Qed.
Lemma argument_add a b : argument_nat(ArgumentsImport.Nat_add a b)=argument_nat a+argument_nat b.
Proof.
 induction b as[|b IH].
 - change(argument_nat a=argument_nat a+0);lia.
 - change(argument_nat(Nat_succ(ArgumentsImport.Nat_add a b))=argument_nat a+argument_nat(Nat_succ b)).
   rewrite !argument_nat_succ,IH;lia.
Qed.
Lemma argument_bool_not b : argument_bool(ArgumentsImport.Bool_not b)=negb(argument_bool b).
Proof. destruct b;reflexivity. Qed.
Fixpoint sizes_accept (sizes:list Z) : bool := match sizes with
|[]=>true|n::rest=>(negb(n=?0)&&(n<=?4096))&&sizes_accept rest end.
Fixpoint sizes_total (sizes:list Z) : Z := match sizes with []=>0|n::rest=>n+1+sizes_total rest end.
Theorem imported_lengths_valid sizes :
 argument_bool(LeanCageM4_Arguments_lengthsValid sizes)=sizes_accept(argument_values sizes).
Proof.
 induction sizes as[|n rest IH];[reflexivity|].
 change(argument_bool(ArgumentsImport.Bool_and
 (ArgumentsImport.Bool_and(ArgumentsImport.Bool_not(ArgumentsImport.Nat_beq n Nat_zero))
 (ArgumentsImport.Nat_ble n 4096))(LeanCageM4_Arguments_lengthsValid rest))=
 ((negb(argument_nat n=?0)&&(argument_nat n<=?4096))&&sizes_accept(argument_values rest))).
 rewrite !argument_bool_and,argument_bool_not,argument_beq,argument_ble,IH;reflexivity.
Qed.
Theorem imported_nul_bytes sizes :
 argument_nat(LeanCageM4_Arguments_nulBytes sizes)=sizes_total(argument_values sizes).
Proof.
 induction sizes as[|n rest IH];[reflexivity|].
 change(argument_nat(ArgumentsImport.Nat_add(ArgumentsImport.Nat_add n 1)
 (LeanCageM4_Arguments_nulBytes rest))=argument_nat n+1+sizes_total(argument_values rest)).
 rewrite !argument_add,IH;reflexivity.
Qed.
Definition imported_lengths_accept sizes := argument_bool(fst2 ArgumentsImport.Bool Nat(LeanCageM4_Arguments_nativeArgumentLengths sizes)).
Definition imported_lengths_total sizes := argument_nat(snd2 ArgumentsImport.Bool Nat(LeanCageM4_Arguments_nativeArgumentLengths sizes)).
Theorem imported_argument_profile sizes :
 imported_lengths_accept sizes=sizes_accept(argument_values sizes) /\
 imported_lengths_total sizes=sizes_total(argument_values sizes).
Proof. split;[apply imported_lengths_valid|apply imported_nul_bytes]. Qed.
