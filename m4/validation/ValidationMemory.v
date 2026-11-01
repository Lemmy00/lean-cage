(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.strings: Actual caller checks, owned bytes and explicit execution boundaries. *)
From Stdlib Require Import List ZArith Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Globalenvs Ctypes Clight.
Require Import Library.
From LeanCageMain Require Import Main MainStructure MainGlobals.
From LeanCageValidation Require Import ValidationStructure.
Import ListNotations.
Open Scope Z_scope.
Definition validation_literals := [___stringlit_56;___stringlit_133;___stringlit_132;
 ___stringlit_135;___stringlit_134;___stringlit_131;___stringlit_130].
Lemma validation_literal_binding id : In id validation_literals->
 Genv.find_symbol main_ge id=Some(symbol_block id).
Proof.
 unfold validation_literals;intros IN;repeat destruct IN as[<-|IN];try contradiction;reflexivity.
Qed.
Ltac literal_initial gv :=
 let initial := fresh "INIT" in let loaded := fresh "LOAD" in let variable := fresh "VAR" in
 intros initial;
 match goal with |- c_string _ (literal_address ?id) _=>
 assert(variable:Genv.find_var_info(Genv.globalenv Main.prog)(symbol_block id)=Some gv)by reflexivity;
 pose proof(Genv.init_mem_characterization Main.prog(symbol_block id)variable initial)as[_[_[_ loaded]]]end;
 specialize(loaded eq_refl);split;
 [repeat(apply Forall_cons;[vm_compute;discriminate|]);apply Forall_nil|split;
 [unfold span_bounds,literal_address;vm_compute;repeat split;congruence|exact loaded]].

Lemma initial_none m : Genv.init_mem Main.prog=Some m->c_string m(literal_address ___stringlit_56)none_bytes.
Proof. literal_initial v___stringlit_56. Qed.
Lemma initial_discard m : Genv.init_mem Main.prog=Some m->c_string m(literal_address ___stringlit_133)discard_bytes.
Proof. literal_initial v___stringlit_133. Qed.
Lemma initial_files m : Genv.init_mem Main.prog=Some m->c_string m(literal_address ___stringlit_132)files_bytes.
Proof. literal_initial v___stringlit_132. Qed.
Lemma initial_shell m : Genv.init_mem Main.prog=Some m->c_string m(literal_address ___stringlit_135)shell_bytes.
Proof. literal_initial v___stringlit_135. Qed.
Lemma initial_python m : Genv.init_mem Main.prog=Some m->c_string m(literal_address ___stringlit_134)python_bytes.
Proof. literal_initial v___stringlit_134. Qed.
Lemma initial_plan m : Genv.init_mem Main.prog=Some m->c_string m(literal_address ___stringlit_131)plan_bytes.
Proof. literal_initial v___stringlit_131. Qed.
Lemma initial_check m : Genv.init_mem Main.prog=Some m->c_string m(literal_address ___stringlit_130)check_bytes.
Proof. literal_initial v___stringlit_130. Qed.
