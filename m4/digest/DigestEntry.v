(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.digest: Function entry, real strlen call and length-first rejection. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Library Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMainNumber Require Import NumberControl.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine ArgumentControl.
From LeanCageDigest Require Import DigestStructure DigestWords DigestValues DigestCharacter.
Import ListNotations.
Open Scope Z_scope.
Definition digest_call_cont le k := Kcall(Some _t'1)f_digest_text empty_env le
 (Kseq digest_length_check(Kseq digest_suffix k)).
Definition digest_returned le n := PTree.set _t'1(Vlong(Int64.repr n))le.
Definition digest_initialized le n := PTree.set _i(Vint Int.zero)(digest_returned le n).
Lemma digest_to_strlen p k m :
 store_path main_ge(fun after=>after=m)(digest_initial(address_value p)k m)4
 (Callstate strlen_definition[address_value p](digest_call_cont(digest_env(address_value p))k)m).
Proof.
 digest_next;[apply digest_entry|].
 change(fn_body f_digest_text)with(Ssequence digest_prefix digest_suffix);digest_route.
 change digest_prefix with(Ssequence digest_strlen digest_length_check);digest_route.
 digest_unfold digest_strlen;digest_next.
 - eapply certified_call_edge.
   + reflexivity.
   + apply old_expression_value;eapply value_function;
     [reflexivity|exact(proj1 argument_strlen_binding)|reflexivity].
   + eapply cons_argument_values;
     [apply old_expression_value;apply value_temp;unfold digest_env;apply PTree.gss|reflexivity|apply no_argument_values].
   + exact(proj2 argument_strlen_binding).
   + reflexivity.
 - apply store_done;reflexivity.
Qed.
Lemma digest_bad_length le k m n : 0<=n<=Int64.max_unsigned->n<>64->
 store_path main_ge(fun after=>after=m)
 (Returnstate(Vlong(Int64.repr n))(digest_call_cont le k)m)4
 (Returnstate(Vint Int.zero)(call_cont k)m).
Proof.
 intros RANGE BAD;unfold digest_call_cont;digest_route;digest_route.
 rewrite digest_length_identity;digest_next.
 - eapply certified_if_edge with(v:=Val.of_bool(negb(n=?64)))(b:=true).
   + apply digest_length_expression;[apply PTree.gss|exact RANGE].
   + rewrite number_bool_value;assert((n=?64)=false)by(apply Z.eqb_neq;exact BAD);rewrite H;reflexivity.
 - digest_next;[apply unchanged_store_edge;eapply edge_return;[apply value_int|reflexivity]|].
   apply store_done;reflexivity.
Qed.
Lemma digest_good_length le k m :
 store_path main_ge(fun after=>after=m)
 (Returnstate(Vlong(Int64.repr 64))(digest_call_cont le k)m)8
 (State f_digest_text digest_loop(Kseq digest_success k)empty_env(digest_initialized le 64)m).
Proof.
 unfold digest_call_cont,digest_initialized,digest_returned;digest_route;digest_route.
 rewrite digest_length_identity;digest_next.
 - eapply certified_if_edge with(v:=Val.of_bool(negb(64=?64)))(b:=false).
   + apply digest_length_expression;[apply PTree.gss|change(0<=64<=18446744073709551615);lia].
   + reflexivity.
 - digest_route;change digest_suffix with(Ssequence digest_init_loop digest_success);digest_route.
   change digest_init_loop with(Ssequence(Sset _i(Econst_int(Int.repr 0)tint))digest_loop);digest_route.
   digest_next;[apply certified_set_edge;apply old_expression_value;apply value_int|].
   digest_route;apply store_done;reflexivity.
Qed.
Lemma digest_initialized_registers p n : digest_registers(digest_initialized(digest_env(address_value p))n)p 0.
Proof. unfold digest_initialized,digest_returned,digest_env,digest_registers;split;WriteAll.lookup. Qed.
