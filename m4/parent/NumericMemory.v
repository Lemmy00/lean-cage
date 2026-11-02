(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Preserve actual observations and ordered source memory. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory.
Require Import Library ScalarMemory.
From LeanCageMainNumber Require Import NumberMemory NumberStorage NumberSafety.
From LeanCageMain Require Import Main MainStructure MainMemory MainPrefix MainFields MainSource.
From LeanCageArguments Require Import ArgumentMemory.
From LeanCageValidation Require Import ValidationStructure ValidationAllocation.
Import ListNotations.
Open Scope Z_scope.
Definition numeric_write_frame fields before after :=
 Mem.unchanged_on(numeric_outside fields)before after /\
 forall b pos kind perm,Mem.perm before b pos kind perm<->Mem.perm after b pos kind perm.
Lemma numeric_final_frame fields before initialized after values : (length values<=10)%nat->
 scalar_stores fields before(map field_cell policy_fields)initialized->
 policy_stores main_policy_block 0 initialized values after->numeric_write_frame fields before after.
Proof.
 intros LENGTH FIELDS POLICY;split.
 - eapply Mem.unchanged_on_trans.
   + eapply Mem.unchanged_on_implies;[eapply scalar_stores_outside;[exact FIELDS|apply field_cells_valid]|].
     intros b pos[LEFT RIGHT]VALID;exact LEFT.
   + eapply Mem.unchanged_on_implies;[apply policy_stores_outside with(i:=0)(values:=values);[lia|lia|exact POLICY]|].
     intros b pos[LEFT RIGHT]VALID;exact RIGHT.
 - intros b pos kind perm;rewrite(scalar_stores_permissions _ _ _ _ POLICY),(scalar_stores_permissions _ _ _ _ FIELDS);tauto.
Qed.
Definition numeric_separate fields b := b<>fields /\b<>main_policy_block.
Lemma numeric_frame_string fields before after p bytes :
 numeric_write_frame fields before after->numeric_separate fields(address_block p)->
 c_string before p bytes->c_string after p bytes.
Proof.
 intros[OLD PERM][FIELDS POLICY][NZ[SPAN LOAD]];split;[exact NZ|];split;[exact SPAN|].
 eapply Mem.loadbytes_unchanged_on;[exact OLD|intros;split;left;assumption|exact LOAD].
Qed.
Lemma numeric_frame_input fields before after p bytes :
 numeric_write_frame fields before after->numeric_separate fields(address_block p)->
 number_input before(address_block p)(Ptrofs.repr(address_offset p))bytes->
 number_input after(address_block p)(Ptrofs.repr(address_offset p))bytes.
Proof.
 intros[OLD PERM][FIELDS POLICY][BOUND[NZ LOAD]];split;[exact BOUND|];split;[exact NZ|].
 eapply Mem.loadbytes_unchanged_on;[exact OLD|intros;split;left;assumption|exact LOAD].
Qed.
Lemma numeric_frame_load fields before after b chunk ofs value :
 numeric_write_frame fields before after->numeric_separate fields b->
 Mem.loadv chunk before(Vptr b ofs)=Some value->Mem.loadv chunk after(Vptr b ofs)=Some value.
Proof.
 intros[OLD PERM][FIELDS POLICY]LOAD;unfold Mem.loadv in *;destruct(zle _ _);[|discriminate].
 eapply Mem.load_unchanged_on;[exact OLD|intros;split;left;assumption|exact LOAD].
Qed.
Lemma numeric_frame_access fields before after b chunk ofs perm : numeric_write_frame fields before after->
 Mem.valid_access before chunk b ofs perm->Mem.valid_access after chunk b ofs perm.
Proof.
 intros[OLD PERM][RANGE ALIGN];split;[|exact ALIGN];intros pos WITHIN;apply PERM;apply RANGE;exact WITHIN.
Qed.
Lemma numeric_frame_output fields before after b ofs : numeric_write_frame fields before after->
 number_output before b ofs->number_output after b ofs.
Proof. intros FRAME[BOUND ACCESS];split;[exact BOUND|eapply numeric_frame_access;eassumption]. Qed.
Definition numeric_literal_separation fields := Forall(fun item=>numeric_separate fields(address_block(literal_address(fst item))))literal_cases.
Lemma numeric_frame_literals fields before after : numeric_write_frame fields before after->
 numeric_literal_separation fields->literals_owned before->literals_owned after.
Proof.
 intros FRAME SEP OWN;unfold numeric_literal_separation in SEP;unfold literals_owned in *;
 rewrite Forall_forall in *;intros item IN;eapply numeric_frame_string;
 [exact FRAME|apply SEP;exact IN|apply OWN;exact IN].
Qed.
Lemma numeric_frame_arguments fields before after argv ofs i inputs : numeric_write_frame fields before after->
 numeric_separate fields argv->Forall(fun arg=>numeric_separate fields(address_block(guest_pointer arg)))inputs->
 guest_arguments_owned before argv ofs i inputs->guest_arguments_owned after argv ofs i inputs.
Proof.
 intros FRAME TABLE SEP;revert i;induction SEP as[|x rest HEAD TAIL IH];intros i OWN;[exact I|].
 destruct OWN as[TEXT[LOAD REST]];split;[eapply numeric_frame_string;eassumption|];split;
 [eapply numeric_frame_load;eassumption|apply IH;exact REST].
Qed.
