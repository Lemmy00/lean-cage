(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Preserve actual observations and ordered source memory. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Clight.
Require Import Library WriteAll.
From LeanCageMainNumber Require Import NumberMemory.
From LeanCageMain Require Import Main MainStructure MainMemory MainValues.
From LeanCageArguments Require Import ArgumentMemory.
From LeanCageInitialization Require Import StoreFrames.
From LeanCageParent Require Import ParentAllocation NumericMemory ValidationAllocation.
Import ListNotations.
Open Scope Z_scope.
Definition validation_locals fields output := PTree.set _fields(fields,tarray(tptr tulong)10)
 (PTree.set _parent(output,tulong)empty_env).
Lemma validation_numeric_locals fields output : numeric_locals(validation_locals fields output)fields.
Proof. unfold numeric_locals,validation_locals;split;WriteAll.lookup. Qed.
Definition guest_numeric arg : numeric_input := {|input_block:=address_block(guest_pointer arg);
 input_offset:=Ptrofs.repr(address_offset(guest_pointer arg));input_bytes:=guest_bytes arg|}.
Lemma split_guest_bytes inputs first rest : map guest_bytes inputs=first++rest->
 exists left right,inputs=left++right /\map guest_bytes left=first /\map guest_bytes right=rest.
Proof.
 revert inputs;induction first as[|bytes first IH];intros inputs EQ.
 - exists [],inputs;cbn in *;auto.
 - destruct inputs as[|x inputs];[discriminate EQ|];cbn in EQ;injection EQ as HEAD TAIL.
   destruct(IH inputs TAIL)as[left[right[INPUTS[A B]]]];exists(x::left),right;split;[cbn;rewrite INPUTS;reflexivity|].
   split;[cbn;rewrite HEAD,A;reflexivity|exact B].
Qed.
Lemma guest_arguments_split m argv ofs i left right :
 guest_arguments_owned m argv ofs i(left++right)->
 guest_arguments_owned m argv ofs i left /\guest_arguments_owned m argv ofs(i+Z.of_nat(length left))right.
Proof.
 revert i;induction left as[|x left IH];intros i OWN.
 - cbn;replace(i+0)with i by lia;auto.
 - destruct OWN as[TEXT[LOAD REST]];destruct(IH(i+1)REST)as[A B];split.
   + split;[exact TEXT|];split;assumption.
   + change(guest_arguments_owned m argv ofs(i+Z.of_nat(S(length left)))right).
     replace(i+Z.of_nat(S(length left)))with(i+1+Z.of_nat(length left))by lia;exact B.
Qed.
Lemma guest_numeric_ready m argv ofs i inputs :
 Forall(fun arg=>address_block(guest_pointer arg)<>main_policy_block)inputs->
 guest_arguments_owned m argv ofs(i+2)inputs->arguments_ready m main_policy_block argv ofs i(map guest_numeric inputs).
Proof.
 intros SEP;revert i;induction SEP as[|x rest HEAD TAIL IH];intros i OWN;[exact I|].
 destruct OWN as[TEXT[LOAD REST]];split;[apply parent_string_input;exact TEXT|];split;[exact HEAD|];split.
 - exact LOAD.
 - apply IH;replace(i+1+2)with(i+2+1)by lia;exact REST.
Qed.
Lemma validation_separate_numeric fields output b : validation_separate fields output b->numeric_separate fields b.
Proof. intros[SETUP[F O]];split;[exact F|exact(proj1(proj2 SETUP))]. Qed.
