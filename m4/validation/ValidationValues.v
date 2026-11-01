(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.strings: Actual caller checks, owned bytes and explicit execution boundaries. *)
From Stdlib Require Import List ZArith Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Library ClightSteps LocalAccess CallAccess WriteAll.
From LeanCageMainNumber Require Import NumberControl.
From LeanCageMain Require Import Main MainStructure MainValues.
From LeanCageArguments Require Import ArgumentWords.
From LeanCageValidation Require Import ValidationStructure ValidationMemory.
Import ListNotations.
Open Scope Z_scope.
Definition bytes_equal xs ys := match compare_bytes xs ys with Eq=>true|_=>false end.
Lemma bytes_equal_iff xs ys : bytes_equal xs ys=true<->xs=ys.
Proof.
 unfold bytes_equal;rewrite <-compare_bytes_equal;destruct(compare_bytes xs ys);split;congruence.
Qed.
Lemma strcmp_exact_zero m left right xs ys value :
 c_string m left xs->c_string m right ys->strcmp_result m left right value->
 Int.eq value Int.zero=bytes_equal xs ys.
Proof.
 intros LEFT RIGHT[a[b[A[B RESULT]]]].
 assert(a=xs)by(eapply c_string_unique;eassumption);subst a.
 assert(b=ys)by(eapply c_string_unique;eassumption);subst b.
 exact(comparison_result_zero _ _ RESULT).
Qed.
Lemma strcmp_bool m value xs ys : Int.eq value Int.zero=bytes_equal xs ys->
 bool_val(Vint value)tint m=Some(negb(bytes_equal xs ys)).
Proof. intros EQ;change(Some(negb(Int.eq value Int.zero))=Some(negb(bytes_equal xs ys)));rewrite EQ;reflexivity. Qed.
Lemma strcmp_cast m value xs ys : Int.eq value Int.zero=bytes_equal xs ys->
 sem_cast(Vint value)tint tbool m=Some(Val.of_bool(negb(bytes_equal xs ys))).
Proof. intros EQ;change(Some(Vint(if Int.eq value Int.zero then Int.zero else Int.one))=Some(Val.of_bool(negb(bytes_equal xs ys))));rewrite EQ;destruct(bytes_equal xs ys);reflexivity. Qed.
Lemma bool_negation m flag : sem_unary_operation Onotbool(Val.of_bool flag)tint m=Some(Val.of_bool(negb flag)).
Proof. destruct flag;reflexivity. Qed.
Lemma validation_literal_value e le m id size : e!id=None->In id validation_literals->
 expression_value main_ge e le m(Evar id(tarray tschar size))(address_value(literal_address id)).
Proof.
 intros GLOBAL IN;apply old_expression_value;eapply value_function;
 [exact GLOBAL|apply validation_literal_binding;exact IN|reflexivity].
Qed.
Lemma validation_global_pointer e le m id p : e!id=None->
 Genv.find_symbol main_ge id=Some(symbol_block id)->
 Mem.loadv Mptr m(Vptr(symbol_block id)Ptrofs.zero)=Some(address_value p)->
 expression_value main_ge e le m(Evar id(tptr tschar))(address_value p).
Proof.
 intros LOCAL SYMBOL LOAD;eapply location_read_value;
 [apply global_location_value;[exact LOCAL|exact SYMBOL]|eapply deref_loc_value;[reflexivity|exact LOAD]].
Qed.
Lemma validation_argv_value e le m argv ofs index p :
 le!_argv=Some(Vptr argv ofs)->0<=index<=2147483647->
 Mem.loadv Mptr m(Vptr argv(Ptrofs.add ofs(Ptrofs.repr(8*index))))=Some(address_value p)->
 expression_value main_ge e le m
 (Ederef(Ebinop Oadd(Etempvar _argv(tptr(tptr tschar)))(Econst_int(Int.repr index)tint)(tptr(tptr tschar)))(tptr tschar))
 (address_value p).
Proof.
 intros ARGV INDEX LOAD;eapply main_pointer_load;[|exact LOAD].
 eapply binary_expression_value;
 [apply old_expression_value;apply value_temp;exact ARGV|apply old_expression_value;apply value_int|
 apply argument_pointer_add;exact INDEX].
Qed.

Definition validation_frame(before after:temp_env) := after!_argv=before!_argv /\ after!_argc=before!_argc.
Ltac validation_frame_auto := unfold validation_frame;split;repeat rewrite PTree.gso by discriminate;reflexivity.
Lemma validation_frame_trans before middle after : validation_frame before middle->
 validation_frame middle after->validation_frame before after.
Proof. unfold validation_frame;intros[A B][C D];split;congruence. Qed.
From compcert Require Import Errors.
From LeanCageMain Require Import MainFields.
Lemma policy_arguments_location e le m : e!_policy__1=None->
 location_value main_ge e le m(Efield(Evar _policy__1 policy_type)_args(tptr(tptr tschar)))
 main_policy_block(Ptrofs.repr 88).
Proof.
 intros GLOBAL.
 assert(LAYOUT:exists co,(genv_cenv main_ge)!_policy=Some co /\ field_offset main_ge _args(co_members co)=OK(88,Full)).
 { apply field_lookup_sound;vm_compute;reflexivity. }
 destruct LAYOUT as[co[CO FIELD]].
 replace(Ptrofs.repr 88)with(Ptrofs.add Ptrofs.zero(Ptrofs.repr 88))by(rewrite Ptrofs.add_zero_l;reflexivity).
 eapply struct_location_value.
 - eapply location_read_value;[apply global_location_value;[exact GLOBAL|apply main_policy_binding]|].
   apply deref_loc_copy;reflexivity.
 - reflexivity.
 - exact CO.
 - exact FIELD.
Qed.
Lemma policy_arguments_value e le m argv ofs : e!_policy__1=None->
 Mem.loadv Mptr m(Vptr main_policy_block(Ptrofs.repr 88))=Some(Vptr argv ofs)->
 expression_value main_ge e le m(Efield(Evar _policy__1 policy_type)_args(tptr(tptr tschar)))(Vptr argv ofs).
Proof.
 intros GLOBAL LOAD;eapply location_read_value;
 [apply policy_arguments_location;exact GLOBAL|eapply deref_loc_value;[reflexivity|exact LOAD]].
Qed.
Lemma executable_pointer_value e le m id argv ofs p : le!id=Some(Vptr argv ofs)->
 Mem.loadv Mptr m(Vptr argv ofs)=Some(address_value p)->
 expression_value main_ge e le m
 (Ederef(Ebinop Oadd(Etempvar id(tptr(tptr tschar)))(Econst_int(Int.repr 0)tint)(tptr(tptr tschar)))(tptr tschar))
 (address_value p).
Proof.
 intros REG LOAD;eapply main_pointer_load;[|exact LOAD].
 eapply binary_expression_value;
 [apply old_expression_value;apply value_temp;exact REG|apply old_expression_value;apply value_int|].
 rewrite argument_pointer_add by lia;rewrite Ptrofs.add_zero;reflexivity.
Qed.
