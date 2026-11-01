(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.arguments: Readable argv cells, terminated strings and pointer spans. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory.
Require Import Library.
From LeanCageArguments Require Import ArgumentWords.
Import ListNotations.
Open Scope Z_scope.
Record guest_argument := {guest_pointer:address;guest_bytes:list Byte.int}.
Definition guest_size x := Z.of_nat(length(guest_bytes x)).
Definition guest_table_span ofs argc := 0<=argc /\ Ptrofs.unsigned ofs+8*argc<=Ptrofs.modulus.
Fixpoint guest_arguments_owned m argv ofs i inputs := match inputs with
|[]=>True
|x::rest=>c_string m(guest_pointer x)(guest_bytes x) /\
 Mem.loadv Mptr m(Vptr argv(Ptrofs.add ofs(Ptrofs.repr(8*i))))=Some(address_value(guest_pointer x)) /\
 guest_arguments_owned m argv ofs(i+1)rest end.
Lemma guest_table_address ofs argc i : guest_table_span ofs argc -> 0<=i<argc ->
 Ptrofs.unsigned(Ptrofs.add ofs(Ptrofs.repr(8*i)))=Ptrofs.unsigned ofs+8*i /\
 Ptrofs.unsigned ofs+8*i+8<=Ptrofs.modulus.
Proof.
 intros[COUNT SPAN]INDEX;pose proof(Ptrofs.unsigned_range ofs)as RANGE.
 rewrite Ptrofs.add_unsigned;rewrite(Ptrofs.unsigned_repr(8*i))by(unfold Ptrofs.max_unsigned;lia).
 rewrite Ptrofs.unsigned_repr by(unfold Ptrofs.max_unsigned;lia);split;[reflexivity|lia].
Qed.
Lemma guest_size_range m argv ofs i x rest : guest_arguments_owned m argv ofs i(x::rest) ->
 0<=guest_size x<Int64.max_unsigned.
Proof. intros[OWN _];exact(argument_strlen_range _ _ _ OWN). Qed.
Fixpoint guest_total inputs := match inputs with []=>0|x::rest=>guest_size x+1+guest_total rest end.
Definition guest_sizes_valid inputs := Forall(fun x=>1<=guest_size x<=4096)inputs.
Inductive argument_outcome :=
| arguments_accepted (total:Z)
| arguments_rejected (index total:Z).
Fixpoint argument_scan i total inputs := match inputs with
|[]=>arguments_accepted total
|x::rest=>if argument_bad(guest_size x) then arguments_rejected i total
 else argument_scan(i+1)(total+guest_size x+1)rest end.
Definition outcome_total result := match result with arguments_accepted total|arguments_rejected _ total=>total end.
Definition outcome_index argc result := match result with arguments_accepted _=>argc|arguments_rejected index _=>index end.
Theorem argument_scan_valid i total inputs : guest_sizes_valid inputs ->
 argument_scan i total inputs=arguments_accepted(total+guest_total inputs).
Proof.
 intros VALID;revert i total;induction VALID as[|x rest SIZE REST IH];intros i total;cbn[argument_scan guest_total].
 - f_equal;lia.
 - rewrite(proj2(argument_bad_false(guest_size x)ltac:(lia))SIZE),IH;f_equal;lia.
Qed.
Theorem argument_scan_reject i total prefix x rest : guest_sizes_valid prefix ->
 argument_bad(guest_size x)=true ->
 argument_scan i total(prefix++x::rest)=
 arguments_rejected(i+Z.of_nat(length prefix))(total+guest_total prefix).
Proof.
 intros VALID BAD;revert i total;induction VALID as[|a prefix SIZE REST IH];intros i total;cbn[argument_scan guest_total app length].
 - rewrite BAD;f_equal;lia.
 - rewrite(proj2(argument_bad_false(guest_size a)ltac:(lia))SIZE),IH;f_equal;lia.
Qed.
Theorem guest_total_bound inputs : guest_sizes_valid inputs ->
 0<=guest_total inputs<=4097*Z.of_nat(length inputs).
Proof. intros VALID;induction VALID;cbn[guest_total length];lia. Qed.
Lemma guest_size_nonnegative x : 0<=guest_size x.
Proof. unfold guest_size;lia. Qed.
Theorem argument_scan_range i total argc inputs : 16<=i ->
 i+Z.of_nat(length inputs)=argc -> 0<=total<=4097*(i-16) ->
 0<=outcome_total(argument_scan i total inputs)<=4097*(argc-16).
Proof.
 revert i total;induction inputs as[|x rest IH];intros i total INDEX COUNT TOTAL;cbn[argument_scan].
 - cbn[outcome_total];cbn in COUNT;lia.
 - destruct(argument_bad(guest_size x))eqn:BAD.
   + cbn[outcome_total];cbn in COUNT;lia.
   + apply IH;[lia|cbn in COUNT;lia|].
     pose proof(proj1(argument_bad_false(guest_size x)(guest_size_nonnegative x))BAD);lia.
Qed.
Theorem argument_scan_accepts i total inputs :
 (exists value,argument_scan i total inputs=arguments_accepted value) <-> guest_sizes_valid inputs.
Proof.
 revert i total;induction inputs as[|x rest IH];intros i total;cbn[argument_scan].
 - split;[intros;constructor|intros; eauto].
 - destruct(argument_bad(guest_size x))eqn:BAD.
   + split;[intros[v H];discriminate|intros ALL;inversion ALL;subst].
     pose proof(proj2(argument_bad_false(guest_size x)(guest_size_nonnegative x))H1);congruence.
   + rewrite IH;split.
     * intros REST;constructor;[apply argument_bad_false;[apply guest_size_nonnegative|exact BAD]|exact REST].
     * intros ALL;inversion ALL;assumption.
Qed.
Fixpoint argument_scan_bytes i total (sources:list(list Byte.int)) := match sources with
|[]=>arguments_accepted total
|bytes::rest=>if argument_bad(Z.of_nat(length bytes))then arguments_rejected i total
 else argument_scan_bytes(i+1)(total+Z.of_nat(length bytes)+1)rest end.
Theorem argument_scan_representation i total inputs :
 argument_scan i total inputs=argument_scan_bytes i total(map guest_bytes inputs).
Proof.
 revert i total;induction inputs as[|x rest IH];intros i total;[reflexivity|].
 cbn[argument_scan argument_scan_bytes map];unfold guest_size;destruct(argument_bad(Z.of_nat(length(guest_bytes x))));[reflexivity|apply IH].
Qed.
