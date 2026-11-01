(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.strings: Actual caller checks, owned bytes and explicit execution boundaries. *)
From Stdlib Require Import ZArith List Lia Bool.
From LeanImport Require Import Lean.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
Require Import Library Machine.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine.
From LeanCageDigest Require Import DigestWords.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationValues ValidationFinish
 DigestCaller ExportCaller ExecutableCaller ModeCaller ValidationImport StringImported.
Local Close Scope lean_scope.
Import ListNotations.
Open Scope Z_scope.
Lemma signed_list_eq_exact xs ys : signed_list_eq xs ys=true<->xs=ys.
Proof.
 revert ys;induction xs as[|x xs IH];intros[|y ys];cbn;try(split;congruence).
 rewrite andb_true_iff,Z.eqb_eq,IH;split;[intros[-> ->];reflexivity|intros EQ;inversion EQ;auto].
Qed.
Lemma bytes_map_injective xs ys : map Byte.unsigned xs=map Byte.unsigned ys->xs=ys.
Proof.
 revert ys;induction xs as[|x xs IH];intros[|y ys]SAME;cbn in SAME;try discriminate;[reflexivity|].
 inversion SAME;f_equal;[apply byte_unsigned_injective;assumption|apply IH;assumption].
Qed.
Lemma bool_from_true a b : (a=true<->b=true)->a=b.
Proof. destruct a,b;intros EQ;try reflexivity;intuition discriminate. Qed.
Theorem signed_list_eq_bytes xs ys : signed_list_eq(map Byte.unsigned xs)(map Byte.unsigned ys)=bytes_equal xs ys.
Proof.
 apply bool_from_true;rewrite signed_list_eq_exact,bytes_equal_iff;split;
 [apply bytes_map_injective|intros->;reflexivity].
Qed.
Theorem validation_imported_digest_agreement xs bytes : validation_values xs=map Byte.unsigned bytes->
 validation_imported_digest xs=digest_valid bytes.
Proof.
 intros REPR;rewrite validation_imported_digest_exact,REPR,length_map;unfold digest_valid;f_equal;clear REPR xs.
 induction bytes as[|b rest IH];cbn[map forallb];[reflexivity|rewrite IH;reflexivity].
Qed.
Theorem imported_mode_agreement argc xs bytes : validation_values xs=map Byte.unsigned bytes->
 validation_check 0 argc xs=negb(mode_bad(validation_nat argc)bytes).
Proof.
 intros REPR;rewrite validation_mode_computation,REPR.
 change [77;51;80;76;65;78;49]with(map Byte.unsigned plan_bytes).
 change [77;51;67;72;69;67;75;49]with(map Byte.unsigned check_bytes).
 rewrite !signed_list_eq_bytes;unfold mode_bad,mode_bytes_bad.
 rewrite Bool.negb_orb,Bool.negb_andb,!Bool.negb_involutive.
 f_equal;apply bool_from_true;rewrite Z.leb_le,Bool.negb_true_iff,Z.ltb_ge;lia.
Qed.
Theorem imported_export_agreement argc xs bytes : validation_values xs=map Byte.unsigned bytes->
 validation_check 1 argc xs=negb(export_bad bytes).
Proof.
 intros REPR;rewrite validation_export_computation,REPR.
 change [100;105;115;99;97;114;100]with(map Byte.unsigned discard_bytes).
 change [114;101;103;117;108;97;114;45;102;105;108;101;115]with(map Byte.unsigned files_bytes).
 rewrite !signed_list_eq_bytes;unfold export_bad;rewrite Bool.negb_andb,!Bool.negb_involutive;reflexivity.
Qed.
Theorem imported_option_agreement argc xs bytes : validation_values xs=map Byte.unsigned bytes->
 validation_check 2 argc xs=negb(option_bad bytes).
Proof.
 intros REPR;rewrite validation_option_computation,REPR,(validation_imported_digest_agreement xs bytes REPR).
 change [110;111;110;101]with(map Byte.unsigned none_bytes).
 rewrite signed_list_eq_bytes;unfold option_bad;rewrite Bool.negb_andb,!Bool.negb_involutive;reflexivity.
Qed.
Theorem imported_executable_agreement argc xs bytes : validation_values xs=map Byte.unsigned bytes->
 validation_check 3 argc xs=negb(executable_bad bytes).
Proof.
 intros REPR;rewrite validation_executable_computation,REPR.
 change [47;98;105;110;47;115;104]with(map Byte.unsigned shell_bytes).
 change [47;117;115;114;47;108;111;99;97;108;47;98;105;110;47;112;121;116;104;111;110;51]with(map Byte.unsigned python_bytes).
 rewrite !signed_list_eq_bytes;unfold executable_bad;rewrite Bool.negb_andb,!Bool.negb_involutive;reflexivity.
Qed.
Local Close Scope lean_scope.
Fixpoint validation_encode_nat(n:nat):Nat:=match n with O=>Nat_zero|S rest=>Nat_succ(validation_encode_nat rest)end.
Lemma validation_encode_nat_exact n : validation_nat(validation_encode_nat n)=Z.of_nat n.
Proof. induction n;[reflexivity|cbn[validation_encode_nat];rewrite validation_nat_succ,IHn;lia]. Qed.
Fixpoint validation_encode_bytes(bytes:list Byte.int):List_inst1 Nat:=match bytes with
|[]=>List_nil_inst1 Nat
|b::rest=>List_cons_inst1 Nat(validation_encode_nat(Z.to_nat(Byte.unsigned b)))(validation_encode_bytes rest)end.
Theorem validation_encode_bytes_exact bytes : validation_values(validation_encode_bytes bytes)=map Byte.unsigned bytes.
Proof.
 induction bytes as[|b rest IH];[reflexivity|];cbn[validation_encode_bytes validation_values map].
 rewrite validation_encode_nat_exact,Z2Nat.id by(pose proof(Byte.unsigned_range b);lia);rewrite IH;reflexivity.
Qed.

From compcert Require Import Maps.
From LeanCageValidation Require Import StringSource.
Local Open Scope nat_scope.
Theorem imported_mode_source cell e le m k argc argv ofs p xs bytes :
 validation_values xs=map Byte.unsigned bytes->
 (Int.min_signed<=validation_nat argc<=Int.max_signed)%Z->le!_argc=Some(Vint(Int.repr(validation_nat argc)))->
 e!_strcmp=None->e!___stringlit_131=None->e!___stringlit_130=None->le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr m(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 8)))=Some(address_value p)->
 c_string m p bytes->c_string m(literal_address ___stringlit_131)plan_bytes->
 c_string m(literal_address ___stringlit_130)check_bytes->
 region_guarantee main_ge cell(fun after=>after=m)(selection_frontier 2 e le k m(negb(validation_check 0 argc xs)))31
 (State f_main(validation_suffix 2)k e le m).
Proof. intros REPR;rewrite(imported_mode_agreement argc xs bytes REPR),Bool.negb_involutive;apply mode_source. Qed.
Theorem imported_export_source cell e le m k argv ofs p xs bytes :
 validation_values xs=map Byte.unsigned bytes->
 e!_strcmp=None->e!___stringlit_133=None->e!___stringlit_132=None->le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr m(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 104)))=Some(address_value p)->
 c_string m p bytes->c_string m(literal_address ___stringlit_133)discard_bytes->
 c_string m(literal_address ___stringlit_132)files_bytes->
 region_guarantee main_ge cell(fun after=>after=m)(selection_frontier 16 e le k m(negb(validation_check 1 Lean.Nat_zero xs)))26
 (State f_main(validation_suffix 16)k e le m).
Proof. intros REPR;rewrite(imported_export_agreement Lean.Nat_zero xs bytes REPR),Bool.negb_involutive;apply export_source. Qed.
Theorem imported_executable_source cell e le m k argv ofs p xs bytes :
 validation_values xs=map Byte.unsigned bytes->
 e!_strcmp=None->e!___stringlit_135=None->e!___stringlit_134=None->e!_policy__1=None->
 Mem.loadv Mptr m(Vptr main_policy_block(Ptrofs.repr 88))=Some(Vptr argv ofs)->
 Mem.loadv Mptr m(Vptr argv ofs)=Some(address_value p)->
 c_string m p bytes->c_string m(literal_address ___stringlit_135)shell_bytes->
 c_string m(literal_address ___stringlit_134)python_bytes->
 region_guarantee main_ge cell(fun after=>after=m)(selection_frontier 22 e le k m(negb(validation_check 3 Lean.Nat_zero xs)))34
 (State f_main(validation_suffix 22)k e le m).
Proof. intros REPR;rewrite(imported_executable_agreement Lean.Nat_zero xs bytes REPR),Bool.negb_involutive;apply executable_source. Qed.
Theorem imported_digest_pair_source cell e le m k tree stdin tree_xs stdin_xs tree_bytes stdin_bytes :
 validation_values tree_xs=map Byte.unsigned tree_bytes->validation_values stdin_xs=map Byte.unsigned stdin_bytes->
 e!_strcmp=None->e!___stringlit_56=None->e!_tree_digest=None->e!_stdin_digest=None->e!_digest_text=None->
 Mem.loadv Mptr m(Vptr(symbol_block _tree_digest)Ptrofs.zero)=Some(address_value tree)->
 Mem.loadv Mptr m(Vptr(symbol_block _stdin_digest)Ptrofs.zero)=Some(address_value stdin)->
 c_string m tree tree_bytes->c_string m stdin stdin_bytes->c_string m(literal_address ___stringlit_56)none_bytes->
 region_guarantee main_ge cell(fun after=>after=m)
 (selection_frontier 20 e le k m(negb(validation_check 2 Lean.Nat_zero tree_xs&&validation_check 2 Lean.Nat_zero stdin_xs)))4300
 (State f_main(validation_suffix 20)k e le m).
Proof.
 intros TREE STDIN;rewrite(imported_option_agreement Lean.Nat_zero tree_xs tree_bytes TREE),
 (imported_option_agreement Lean.Nat_zero stdin_xs stdin_bytes STDIN),Bool.negb_andb,!Bool.negb_involutive.
 apply digest_pair_source.
Qed.
