(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.digest: Strict imported bytes select the actual complete-function return. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory Globalenvs Ctypes Clight.
Require Import Library Machine ClightSteps Deterministic.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine StringPath.
From LeanCageDigest Require Import DigestStructure DigestWords DigestSource DigestWitnesses DigestImported StringControl.
Import ListNotations.
Open Scope nat_scope.
Theorem imported_digest_agreement xs bytes : digest_values xs=map Byte.unsigned bytes->
 imported_digest xs=digest_valid bytes.
Proof.
 intros REPR;rewrite imported_digest_exact,REPR,length_map;unfold digest_valid;f_equal;clear REPR xs.
 induction bytes as[|b rest IH];cbn[map forallb];[reflexivity|rewrite IH;reflexivity].
Qed.
Theorem imported_digest_source cell m p bytes xs k :
 digest_values xs=map Byte.unsigned bytes->c_string m p bytes->
 exists count,count<=2068 /\ string_path main_ge cell(digest_initial(address_value p)k m)count
 (Returnstate(Val.of_bool(imported_digest xs))(call_cont k)m).
Proof. intros REPR OWN;rewrite(imported_digest_agreement _ _ REPR);apply digest_source;exact OWN. Qed.
Theorem imported_digest_all_returns cell m p bytes xs events value after :
 digest_values xs=map Byte.unsigned bytes->c_string m p bytes->
 string_steps main_ge cell(live(digest_initial(address_value p)Kstop m))events
 (live(Returnstate value Kstop after))->value=Val.of_bool(imported_digest xs) /\ after=m.
Proof.
 intros REPR OWN RUN;rewrite(imported_digest_agreement _ _ REPR);eapply digest_all_returns;eassumption.
Qed.
Theorem imported_digest_all_prefixes cell m p bytes xs events target :
 digest_values xs=map Byte.unsigned bytes->c_string m p bytes->
 string_steps main_ge cell(live(digest_initial(address_value p)Kstop m))events target->
 routine_memory target=m /\ string_cost events<=2069 /\
 (forall s,target=live s->exists remaining,string_certificate main_ge cell(fun after=>after=m)
 (fun value after=>value=Val.of_bool(imported_digest xs) /\ after=m)remaining s).
Proof.
 intros REPR OWN RUN;rewrite(imported_digest_agreement _ _ REPR);eapply digest_all_prefixes;eassumption.
Qed.
From LeanImport Require Import Lean.
From LeanCageDigest Require Import DigestImport.
Local Close Scope lean_scope.
Fixpoint digest_encode_nat(n:nat):Nat:=match n with O=>Nat_zero|S rest=>Nat_succ(digest_encode_nat rest)end.
Lemma digest_encode_nat_exact n : digest_nat(digest_encode_nat n)=Z.of_nat n.
Proof. induction n;[reflexivity|cbn[digest_encode_nat];rewrite digest_nat_succ,IHn;lia]. Qed.
Fixpoint digest_encode_bytes(bytes:list Byte.int):List_inst1 Nat:=match bytes with
|[]=>List_nil_inst1 Nat
|b::rest=>List_cons_inst1 Nat(digest_encode_nat(Z.to_nat(Byte.unsigned b)))(digest_encode_bytes rest)end.
Theorem digest_encode_bytes_exact bytes : digest_values(digest_encode_bytes bytes)=map Byte.unsigned bytes.
Proof.
 induction bytes as[|b rest IH];[reflexivity|];cbn[digest_encode_bytes digest_values map].
 rewrite digest_encode_nat_exact,Z2Nat.id by(pose proof(Byte.unsigned_range b);lia);rewrite IH;reflexivity.
Qed.
Theorem digest_representation_inhabited bytes :
 imported_digest(digest_encode_bytes bytes)=digest_valid bytes.
Proof. apply imported_digest_agreement,digest_encode_bytes_exact. Qed.
Theorem allocated_imported_digest cell bytes : digest_input_admissible bytes->
 exists initial m p (count:nat),Genv.init_mem Main.prog=Some initial /\
 c_string m p bytes /\ (count<=2068)%nat /\
 string_path main_ge cell(digest_initial(address_value p)Kstop m)count
 (Returnstate(Val.of_bool(imported_digest(digest_encode_bytes bytes)))Kstop m).
Proof.
 intros VALID;destruct(allocated_digest_source cell bytes VALID)as[initial[m[p[count[INIT[OLD[OWN[BOUND PATH]]]]]]]].
 exists initial,m,p,count;rewrite digest_representation_inhabited;auto.
Qed.
