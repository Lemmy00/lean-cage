(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.plan: Exact meaning of the strictly imported numeric byte interface. *)
From Stdlib Require Import Arith List Lia Bool.
From LeanImport Require Import Lean.
From LeanCagePlan Require Import PlanImport.
Local Close Scope lean_scope.
Local Open Scope nat_scope.
Import ListNotations.
Fixpoint plan_values (xs : List_inst1 Nat) : list nat :=
 match xs with List_nil_inst1 _ => [] | List_cons_inst1 _ n xs => nat_of_Nat n::plan_values xs end.
Definition plan_bool (b : PlanImport.Bool) : bool :=
 match b with PlanImport.Bool_false => false | PlanImport.Bool_true => true end.
Definition plan_option (value : PlanImport.Option_inst1 Nat) : option nat :=
 match value with PlanImport.Option_none_inst1 _ => None
 | PlanImport.Option_some_inst1 _ n => Some (nat_of_Nat n) end.
Fixpoint natural_decimal_fold acc bytes := match bytes with
 | [] => acc | b::tail => natural_decimal_fold (acc*10+(b-48)) tail end.
Fixpoint natural_decimal_digits bytes := match bytes with
 | [] => true | b::tail => ((48<=?b)&&(b<=?57)) && natural_decimal_digits tail end.
Definition natural_decimal bound bytes := match bytes with
 | [] => None | _::_ => if natural_decimal_digits bytes && (natural_decimal_fold 0 bytes<=?bound)
 then Some(natural_decimal_fold 0 bytes) else None end.
Lemma plan_add_exact a b : nat_of_Nat (PlanImport.Nat_add a b)=nat_of_Nat a+nat_of_Nat b.
Proof.
 induction b as [|b IH].
 - change (nat_of_Nat a=nat_of_Nat a+0);lia.
 - change (S(nat_of_Nat(PlanImport.Nat_add a b))=nat_of_Nat a+S(nat_of_Nat b)).
   rewrite IH;lia.
Qed.
Lemma plan_mul_exact a b : nat_of_Nat (PlanImport.Nat_mul a b)=nat_of_Nat a*nat_of_Nat b.
Proof.
 induction b as [|b IH].
 - change (0=nat_of_Nat a*0);lia.
 - change (nat_of_Nat(PlanImport.Nat_add (PlanImport.Nat_mul a b) a)=nat_of_Nat a*S(nat_of_Nat b)).
   rewrite plan_add_exact,IH;lia.
Qed.
Lemma plan_pred_exact a : nat_of_Nat(PlanImport.Nat_pred a)=Nat.pred(nat_of_Nat a).
Proof. destruct a;reflexivity. Qed.
Lemma plan_sub_exact a b : nat_of_Nat(PlanImport.Nat_sub a b)=nat_of_Nat a-nat_of_Nat b.
Proof.
 induction b as [|b IH].
 - change (nat_of_Nat a=nat_of_Nat a-0);lia.
 - change (nat_of_Nat(PlanImport.Nat_pred(PlanImport.Nat_sub a b))=nat_of_Nat a-S(nat_of_Nat b)).
   rewrite plan_pred_exact,IH;lia.
Qed.
Lemma plan_ble_exact a b : plan_bool(PlanImport.Nat_ble a b)=Nat.leb(nat_of_Nat a)(nat_of_Nat b).
Proof.
 revert b;induction a as [|a IH];intros [|b];try reflexivity.
 change (plan_bool(PlanImport.Nat_ble a b)=Nat.leb(nat_of_Nat a)(nat_of_Nat b));apply IH.
Qed.
Lemma plan_bool_and a b : plan_bool(PlanImport.Bool_and a b)=andb(plan_bool a)(plan_bool b).
Proof. destruct a,b;reflexivity. Qed.
Lemma plan_ite_bool A b (t e : A) :
 PlanImport.ite A (Lean.eq b PlanImport.Bool_true) (PlanImport.instDecidableEqBool b PlanImport.Bool_true) t e =
 if plan_bool b then t else e.
Proof. destruct b;reflexivity. Qed.
Theorem plan_fold_exact acc bytes :
 nat_of_Nat(LeanCageM4_Plan_decimalFold acc bytes)=natural_decimal_fold(nat_of_Nat acc)(plan_values bytes).
Proof.
 revert acc;induction bytes as [|b bytes IH];intro acc;[reflexivity|].
 change (nat_of_Nat(LeanCageM4_Plan_decimalFold
  (PlanImport.Nat_add (PlanImport.Nat_mul acc 10) (PlanImport.Nat_sub b 48)) bytes)=
  natural_decimal_fold (nat_of_Nat acc*10+(nat_of_Nat b-48)) (plan_values bytes)).
 rewrite IH,plan_add_exact,plan_mul_exact,plan_sub_exact;reflexivity.
Qed.
Theorem plan_digits_exact bytes :
 plan_bool(LeanCageM4_Plan_decimalDigits bytes)=natural_decimal_digits(plan_values bytes).
Proof.
 induction bytes as [|b bytes IH];[reflexivity|].
 change (plan_bool(PlanImport.Bool_and (PlanImport.Bool_and (PlanImport.Nat_ble 48 b)
  (PlanImport.Nat_ble b 57)) (LeanCageM4_Plan_decimalDigits bytes))=
  ((48<=?nat_of_Nat b)&&(nat_of_Nat b<=?57))&&natural_decimal_digits(plan_values bytes)).
 rewrite !plan_bool_and,!plan_ble_exact,IH;reflexivity.
Qed.
Theorem plan_parser_exact bound bytes :
 plan_option(LeanCageM4_Plan_parseDecimal bound bytes)=natural_decimal(nat_of_Nat bound)(plan_values bytes).
Proof.
 destruct bytes as [|b bytes];[reflexivity|].
 set (bs:=List_cons_inst1 Nat b bytes).
 set (test:=PlanImport.Bool_and (LeanCageM4_Plan_decimalDigits bs)
   (PlanImport.Nat_ble (LeanCageM4_Plan_decimalFold 0 bs) bound)).
 change (plan_option(PlanImport.ite (PlanImport.Option_inst1 Nat)
  (Lean.eq test PlanImport.Bool_true)
  (PlanImport.instDecidableEqBool test PlanImport.Bool_true)
  (PlanImport.Option_some_inst1 Nat (LeanCageM4_Plan_decimalFold 0 bs))
  (PlanImport.Option_none_inst1 Nat))=natural_decimal(nat_of_Nat bound)(plan_values bs)).
 rewrite plan_ite_bool;unfold test.
 rewrite plan_bool_and,plan_digits_exact,plan_ble_exact,plan_fold_exact.
 change (plan_option (if natural_decimal_digits(plan_values bs)&&
    (natural_decimal_fold 0 (plan_values bs)<=?nat_of_Nat bound)
   then PlanImport.Option_some_inst1 Nat (LeanCageM4_Plan_decimalFold 0 bs)
   else PlanImport.Option_none_inst1 Nat)=
   if natural_decimal_digits(plan_values bs)&&
    (natural_decimal_fold 0 (plan_values bs)<=?nat_of_Nat bound)
   then Some(natural_decimal_fold 0 (plan_values bs)) else None).
 destruct (natural_decimal_digits(plan_values bs)&&
  (natural_decimal_fold 0 (plan_values bs)<=?nat_of_Nat bound)).
 - cbn [plan_option];rewrite plan_fold_exact;reflexivity.
 - reflexivity.
Qed.
