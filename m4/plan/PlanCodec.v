(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.plan: Exact imported parser agreement with the native digit language. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Integers.
From LeanImport Require Import Lean.
From LeanCageController Require Import NumberMath.
From LeanCagePlan Require Import PlanImport PlanValues.
Local Close Scope lean_scope.
Local Open Scope Z_scope.
Import ListNotations.
Definition byte_naturals bytes := map (fun b => Z.to_nat(Byte.unsigned b)) bytes.
Fixpoint plan_bytes (bytes : list Byte.int) : List_inst1 Nat :=
 match bytes with [] => List_nil_inst1 Nat
 | b::tail => List_cons_inst1 Nat (Nat_of_nat(Z.to_nat(Byte.unsigned b))) (plan_bytes tail) end.
Definition plan_bound := Nat_of_nat(Z.to_nat decimal_max).
Definition plan_parsed bytes := plan_option(LeanCageM4_Plan_parseDecimal plan_bound (plan_bytes bytes)).
Lemma plan_bytes_values bytes : plan_values(plan_bytes bytes)=byte_naturals bytes.
Proof. induction bytes;cbn [plan_values plan_bytes byte_naturals map];[reflexivity|]. rewrite nat2Natid,IHbytes;reflexivity. Qed.
Lemma natural_digits_true bytes : natural_decimal_digits bytes=true <-> Forall (fun b => (48<=b<=57)%nat) bytes.
Proof.
 induction bytes as [|b bytes IH];[cbn;split;intros;constructor|].
 cbn [natural_decimal_digits];rewrite !andb_true_iff,!Nat.leb_le,IH.
 split;[intros [[LO HI] REST];constructor;auto|intro ALL;inversion ALL;tauto].
Qed.
Lemma natural_decimal_some bound bytes value : natural_decimal bound bytes=Some value <->
 bytes<>[] /\ Forall (fun b => (48<=b<=57)%nat) bytes /\
 value=natural_decimal_fold 0 bytes /\ (value<=bound)%nat.
Proof.
 destruct bytes as [|b bytes];[cbn;split;[discriminate|tauto]|].
 unfold natural_decimal;destruct(natural_decimal_digits(b::bytes)&&
  (natural_decimal_fold 0 (b::bytes)<=?bound)%nat) eqn:COND.
 - apply andb_true_iff in COND;destruct COND as [DIG SIZE].
   apply natural_digits_true in DIG;apply Nat.leb_le in SIZE.
   split;[intro EQ;inversion EQ;subst;repeat split;try discriminate;assumption|].
   intros [_ [_ [-> _]]];reflexivity.
 - split;[discriminate|]. intros [_ [DIG [VALUE SIZE]]];subst value.
   assert (OK : natural_decimal_digits(b::bytes)&&
    (natural_decimal_fold 0 (b::bytes)<=?bound)%nat=true).
   { apply andb_true_iff;split;[apply natural_digits_true|apply Nat.leb_le];assumption. }
   congruence.
Qed.
Lemma byte_digits_exact bytes :
 Forall (fun b => (48<=b<=57)%nat) (byte_naturals bytes) <-> Forall decimal_digit_ok bytes.
Proof.
 induction bytes as [|b bytes IH];[split;intro;constructor|].
 cbn [byte_naturals map];rewrite !Forall_cons_iff,IH.
 assert (BACK : Z.of_nat(Z.to_nat(Byte.unsigned b))=Byte.unsigned b).
 { apply Z2Nat.id;pose proof(Byte.unsigned_range b);lia. }
 split;intros [DIG REST];split;[unfold decimal_digit_ok;lia|exact REST|unfold decimal_digit_ok in DIG;lia|exact REST].
Qed.
Lemma byte_decimal_fold bytes acc : Forall decimal_digit_ok bytes ->
 Z.of_nat(natural_decimal_fold acc (byte_naturals bytes))=decimal_fold (Z.of_nat acc) bytes.
Proof.
 revert acc;induction bytes as [|b bytes IH];intros acc DIG;[reflexivity|].
 inversion DIG as [|? ? D REST];subst.
 cbn [byte_naturals map natural_decimal_fold decimal_fold].
 rewrite IH by exact REST.
 unfold decimal_digit_ok in D;unfold decimal_digit.
 rewrite Nat2Z.inj_add,Nat2Z.inj_mul,Nat2Z.inj_sub by lia.
 rewrite Z2Nat.id by lia;reflexivity.
Qed.
Theorem plan_parser_some bytes value : plan_parsed bytes=Some value <->
 decimal_number bytes=Some(Z.of_nat value).
Proof.
 unfold plan_parsed;rewrite plan_parser_exact,plan_bytes_values.
 unfold plan_bound;rewrite nat2Natid,natural_decimal_some,decimal_number_exact.
 split.
 - intros [NE [DIG [VALUE SIZE]]].
   apply byte_digits_exact in DIG.
   split;[intro EMPTY;subst;apply NE;reflexivity|]. split;[exact DIG|]. split.
   + rewrite VALUE,byte_decimal_fold by exact DIG;reflexivity.
   + unfold decimal_max in *;lia.
 - intros [NE [DIG [VALUE RANGE]]].
   split;[destruct bytes;[contradiction|discriminate]|]. split.
   + apply byte_digits_exact;exact DIG.
   + split.
     * apply Nat2Z.inj;rewrite byte_decimal_fold by exact DIG;exact VALUE.
     * unfold decimal_max in *;lia.
Qed.
Theorem plan_parser_none bytes : plan_parsed bytes=None <-> decimal_number bytes=None.
Proof.
 split.
 - intro NONE;destruct(decimal_number bytes) as [value|] eqn:PARSE;[|reflexivity].
   pose proof(proj1(decimal_number_exact bytes value) PARSE) as [_ [_ [_ RANGE]]].
   assert (SOME : plan_parsed bytes=Some(Z.to_nat value)).
   { apply plan_parser_some;rewrite Z2Nat.id by lia;exact PARSE. }
   congruence.
 - intro NONE;destruct(plan_parsed bytes) as [value|] eqn:PARSE;[|reflexivity].
   apply plan_parser_some in PARSE;congruence.
Qed.
Theorem plan_parser_value bytes : option_map Z.of_nat (plan_parsed bytes)=decimal_number bytes.
Proof.
 destruct(plan_parsed bytes) as [value|] eqn:PARSE;cbn [option_map].
 - symmetry;apply plan_parser_some;exact PARSE.
 - symmetry;apply plan_parser_none;exact PARSE.
Qed.
