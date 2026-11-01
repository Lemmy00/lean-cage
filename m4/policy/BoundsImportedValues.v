(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.bounds: Exact imported naturals, booleans, fields and page remainder. *)
From Stdlib Require Import ZArith Arith List Lia Bool.
From LeanImport Require Import Lean.
From LeanCageBounds Require Import BoundsImport.
Local Close Scope lean_scope.
Open Scope Z_scope.
Import ListNotations.
Definition bound_nat n := Z.of_nat(nat_of_Nat n).
Definition bound_bool (b:BoundsImport.Bool) : bool :=
 match b with Bool_false=>false|Bool_true=>true end.
Fixpoint bound_values (xs:List_inst1 Nat) : list Z := match xs with
 | List_nil_inst1 _=>[]|List_cons_inst1 _ n rest=>bound_nat n::bound_values rest end.
Lemma bound_nat_nonnegative n : 0<=bound_nat n.
Proof. unfold bound_nat;lia. Qed.
Lemma bound_nat_double n : bound_nat(double n)=2*bound_nat n.
Proof. induction n;unfold bound_nat in *;cbn[double nat_of_Nat];lia. Qed.
Lemma bound_nat_succ n : bound_nat(Nat_succ n)=1+bound_nat n.
Proof. unfold bound_nat;cbn[nat_of_Nat];lia. Qed.
Lemma bound_nat_zero : bound_nat Nat_zero=0.
Proof. reflexivity. Qed.
Lemma bound_bool_and a b : bound_bool(BoundsImport.Bool_and a b)=andb(bound_bool a)(bound_bool b).
Proof. destruct a,b;reflexivity. Qed.
Lemma bound_ble a b : bound_bool(BoundsImport.Nat_ble a b)=(bound_nat a<=?bound_nat b).
Proof.
 assert(NAT:bound_bool(BoundsImport.Nat_ble a b)=Nat.leb(nat_of_Nat a)(nat_of_Nat b)).
 { revert b;induction a as[|a IH];intros[|b];try reflexivity.
   change(bound_bool(BoundsImport.Nat_ble a b)=Nat.leb(nat_of_Nat a)(nat_of_Nat b));apply IH. }
 rewrite NAT;unfold bound_nat.
 destruct(Nat.leb(nat_of_Nat a)(nat_of_Nat b))eqn:LE;symmetry;
 [apply Nat.leb_le in LE;apply Z.leb_le|apply Nat.leb_gt in LE;apply Z.leb_gt];lia.
Qed.
Lemma bound_beq a b : bound_bool(BoundsImport.Nat_beq a b)=(bound_nat a=?bound_nat b).
Proof.
 assert(NAT:bound_bool(BoundsImport.Nat_beq a b)=Nat.eqb(nat_of_Nat a)(nat_of_Nat b)).
 { revert b;induction a as[|a IH];intros[|b];try reflexivity.
   change(bound_bool(BoundsImport.Nat_beq a b)=Nat.eqb(nat_of_Nat a)(nat_of_Nat b));apply IH. }
 rewrite NAT;unfold bound_nat.
 destruct(Nat.eqb(nat_of_Nat a)(nat_of_Nat b))eqn:EQ;symmetry;
 [apply Nat.eqb_eq in EQ;apply Z.eqb_eq|apply Nat.eqb_neq in EQ;apply Z.eqb_neq];lia.
Qed.
Lemma bound_pred a : bound_nat(BoundsImport.Nat_pred a)=Z.max 0(bound_nat a-1).
Proof. destruct a;[reflexivity|].
 change(bound_nat a=Z.max 0(bound_nat(Nat_succ a)-1));rewrite bound_nat_succ;
 pose proof(bound_nat_nonnegative a);lia. Qed.
Lemma bound_sub a b : bound_nat(BoundsImport.Nat_sub a b)=Z.max 0(bound_nat a-bound_nat b).
Proof.
 induction b as[|b IH].
 - change(bound_nat a=Z.max 0(bound_nat a-0));pose proof(bound_nat_nonnegative a);lia.
 - change(bound_nat(BoundsImport.Nat_pred(BoundsImport.Nat_sub a b))=
    Z.max 0(bound_nat a-bound_nat(Nat_succ b))).
   rewrite bound_pred,IH,bound_nat_succ;lia.
Qed.
Lemma bound_add a b : bound_nat(BoundsImport.Nat_add a b)=bound_nat a+bound_nat b.
Proof.
 induction b as[|b IH].
 - change(bound_nat a=bound_nat a+0);lia.
 - change(bound_nat(Nat_succ(BoundsImport.Nat_add a b))=bound_nat a+bound_nat(Nat_succ b)).
   rewrite !bound_nat_succ,IH;lia.
Qed.
Lemma bound_ite A b (yes no:A) :
 BoundsImport.ite A(Lean.eq b Bool_true)(instDecidableEqBool b Bool_true)yes no=
 if bound_bool b then yes else no.
Proof. destruct b;reflexivity. Qed.
Theorem imported_page_remainder fuel n : bound_nat n<=bound_nat fuel ->
 bound_nat(LeanCageM4_Bounds_pageRemainder fuel n)=bound_nat n mod 4096.
Proof.
 revert n;induction fuel as[|fuel IH];intros n ENOUGH.
 - assert(ZERO:n=Nat_zero).
   { destruct n;[reflexivity|rewrite bound_nat_succ,bound_nat_zero in ENOUGH;
     pose proof(bound_nat_nonnegative n);lia]. }
   subst n;reflexivity.
 - change(bound_nat(BoundsImport.ite Nat
    (Lean.eq (BoundsImport.Nat_ble 4096 n) Bool_true)
    (instDecidableEqBool(BoundsImport.Nat_ble 4096 n)Bool_true)
    (LeanCageM4_Bounds_pageRemainder fuel(BoundsImport.Nat_sub n 4096))n)=bound_nat n mod 4096).
   rewrite bound_ite,bound_ble;change(bound_nat 4096)with 4096.
   destruct(4096<=?bound_nat n)eqn:LARGE.
   + apply Z.leb_le in LARGE;rewrite IH.
     * rewrite bound_sub;change(bound_nat 4096)with 4096.
       rewrite Z.max_r by lia.
       replace(bound_nat n-4096)with(bound_nat n+(-1)*4096)by ring.
       rewrite Z.mod_add by lia;reflexivity.
     * rewrite bound_sub;change(bound_nat 4096)with 4096.
       rewrite bound_nat_succ in ENOUGH;pose proof(bound_nat_nonnegative fuel);lia.
   + apply Z.leb_gt in LARGE;symmetry;apply Z.mod_small;pose proof(bound_nat_nonnegative n);lia.
Qed.
Theorem imported_page_aligned n :
 bound_bool(LeanCageM4_Bounds_pageAligned n)=(bound_nat n mod 4096=?0).
Proof.
 change(bound_bool(BoundsImport.Nat_beq(LeanCageM4_Bounds_pageRemainder n n)Nat_zero)=(bound_nat n mod 4096=?0)).
 rewrite bound_beq,imported_page_remainder by lia;reflexivity.
Qed.
Theorem imported_field_count fields : bound_nat(LeanCageM4_Bounds_fieldCount fields)=Z.of_nat(length(bound_values fields)).
Proof.
 induction fields as[|x fields IH];[reflexivity|].
 change(bound_nat(BoundsImport.Nat_add(LeanCageM4_Bounds_fieldCount fields)1)=
  Z.of_nat(S(length(bound_values fields)))).
 rewrite bound_add,IH;change(bound_nat 1)with 1;lia.
Qed.
Theorem imported_field_at fields index :
 bound_nat(LeanCageM4_Bounds_fieldAt fields index)=nth(nat_of_Nat index)(bound_values fields)0.
Proof.
 revert index;induction fields as[|x fields IH];intros[|index];try reflexivity.
 change(bound_nat(LeanCageM4_Bounds_fieldAt fields index)=nth(nat_of_Nat index)(bound_values fields)0);apply IH.
Qed.
