(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.digest: Actual loop control, first rejection and exact returns. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Readers Library Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMainNumber Require Import NumberControl.
From LeanCageMain Require Import Main MainStructure.
From LeanCageDigest Require Import DigestStructure DigestWords DigestValues DigestCharacter.
Open Scope Z_scope.
Definition digest_loop_cont k := Kloop1 digest_body digest_increment k.
Definition digest_character_cont k := Kseq digest_reject(digest_loop_cont k).
Definition digest_advanced le b i := PTree.set _i(Vint(Int.repr(i+1)))(digest_character_env le b).
Lemma digest_loop_to_character le m i k : le!_i=Some(Vint(Int.repr i))->0<=i<64->
 store_path main_ge(fun after=>after=m)(State f_digest_text digest_loop k empty_env le m)5
 (State f_digest_text digest_character(digest_character_cont k)empty_env le m).
Proof.
 intros INDEX RANGE;change digest_loop with(Sloop digest_body digest_increment);digest_route.
 change digest_body with(Ssequence digest_test(Ssequence digest_character digest_reject));digest_route.
 digest_unfold digest_test;digest_next.
 - eapply certified_if_edge with(v:=Val.of_bool(i<?64))(b:=true).
   + apply digest_test_expression;[exact INDEX|lia].
   + rewrite number_bool_value;f_equal;apply Z.ltb_lt;lia.
 - digest_route;digest_route;apply store_done;reflexivity.
Qed.
Lemma digest_character_failure le m b k : digest_hex b=false->
 store_path main_ge(fun after=>after=m)
 (State f_digest_text Sskip(digest_character_cont k)empty_env(digest_character_env le b)m)3
 (Returnstate(Vint Int.zero)(call_cont k)m).
Proof.
 intros BAD;unfold digest_character_cont;digest_route;digest_unfold digest_reject;digest_next.
 - apply unchanged_store_edge;eapply edge_if with(b:=true).
   + eapply value_unary;[apply value_temp;rewrite digest_character_result,BAD;reflexivity|reflexivity].
   + reflexivity.
 - digest_next;[apply unchanged_store_edge;eapply edge_return;[apply value_int|reflexivity]|].
   apply store_done;reflexivity.
Qed.
Lemma digest_character_success le m b i k : le!_i=Some(Vint(Int.repr i))->0<=i<64->digest_hex b=true->
 store_path main_ge(fun after=>after=m)
 (State f_digest_text Sskip(digest_character_cont k)empty_env(digest_character_env le b)m)5
 (State f_digest_text digest_loop k empty_env(digest_advanced le b i)m).
Proof.
 intros INDEX RANGE GOOD;unfold digest_character_cont;digest_route;digest_unfold digest_reject;digest_next.
 - apply unchanged_store_edge;eapply edge_if with(b:=false).
   + eapply value_unary;[apply value_temp;rewrite digest_character_result,GOOD;reflexivity|reflexivity].
   + reflexivity.
 - unfold digest_loop_cont;digest_route;digest_unfold digest_increment;unfold digest_advanced;digest_next.
   + apply certified_set_edge;eapply binary_expression_value.
     * apply old_expression_value;apply value_temp.
       unfold digest_character_env,digest_letters_env,digest_digits_env;
       destruct(digest_digit b);try destruct(97<=?digest_signed b);
       destruct(48<=?digest_signed b);WriteAll.lookup.
     * apply old_expression_value;apply value_int.
     * apply digest_index_increment;exact RANGE.
   + digest_route;apply store_done;reflexivity.
Qed.
Lemma digest_advanced_registers le p i b : digest_registers le p i->digest_registers(digest_advanced le b i)p(i+1).
Proof.
 intros REGS;pose proof(digest_character_registers _ _ _ b REGS)as[PTR INDEX].
 unfold digest_advanced,digest_registers;split;WriteAll.lookup.
Qed.
Lemma digest_loop_finished le m k : le!_i=Some(Vint(Int.repr 64))->
 store_path main_ge(fun after=>after=m)(State f_digest_text digest_loop k empty_env le m)5
 (State f_digest_text Sskip k empty_env le m).
Proof.
 intros INDEX;change digest_loop with(Sloop digest_body digest_increment);digest_route.
 change digest_body with(Ssequence digest_test(Ssequence digest_character digest_reject));digest_route.
 digest_unfold digest_test;digest_next.
 - eapply certified_if_edge with(v:=Val.of_bool(64<?64))(b:=false).
   + apply digest_test_expression;[exact INDEX|lia].
   + reflexivity.
 - digest_route;digest_route;apply store_done;reflexivity.
Qed.
Lemma digest_finish le m k :
 store_path main_ge(fun after=>after=m)(State f_digest_text Sskip(Kseq digest_success k)empty_env le m)2
 (Returnstate(Vint Int.one)(call_cont k)m).
Proof.
 digest_route;digest_unfold digest_success;digest_next;
 [apply unchanged_store_edge;eapply edge_return;[apply value_int|reflexivity]|].
 apply store_done;reflexivity.
Qed.
