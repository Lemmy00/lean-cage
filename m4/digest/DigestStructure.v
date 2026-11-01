(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.digest: Exact source digest syntax, reads and interruption. *)
From Stdlib Require Import List ZArith.
From compcert Require Import Coqlib Maps Integers AST Values Globalenvs Ctypes Ctypesdefs Cop Clight.
From LeanCageMain Require Import Main MainStructure.
Require Import Machine ClightSteps StoreSteps LocalAccess WriteAll.
Import ListNotations.
Definition digest_prefix:=first_statement(fn_body f_digest_text).
Definition digest_suffix:=second_statement(fn_body f_digest_text).
Definition digest_strlen:=first_statement digest_prefix.
Definition digest_length_check:=second_statement digest_prefix.
Definition digest_init_loop:=first_statement digest_suffix.
Definition digest_success:=second_statement digest_suffix.
Definition digest_loop:=second_statement digest_init_loop.
Definition digest_body:=match digest_loop with Sloop b _=>b|_=>Sskip end.
Definition digest_increment:=match digest_loop with Sloop _ inc=>inc|_=>Sskip end.
Definition digest_test:=first_statement digest_body.
Definition digest_character:=first_statement(second_statement digest_body).
Definition digest_reject:=second_statement(second_statement digest_body).
Definition digest_digits:=first_statement digest_character.
Definition digest_letters:=second_statement digest_character.
Theorem digest_structure:
 fn_body f_digest_text=Ssequence digest_prefix digest_suffix /\
 digest_prefix=Ssequence digest_strlen digest_length_check /\
 digest_suffix=Ssequence digest_init_loop digest_success /\
 digest_init_loop=Ssequence(Sset _i(Econst_int(Int.repr 0)tint))digest_loop /\
 digest_loop=Sloop digest_body digest_increment /\
 digest_body=Ssequence digest_test(Ssequence digest_character digest_reject) /\
 digest_character=Ssequence digest_digits digest_letters /\
 fn_vars f_digest_text=[] /\ fn_params f_digest_text=[(_s,tptr tschar)].
Proof. repeat split;reflexivity. Qed.
Theorem digest_length_identity : digest_length_check =
 Sifthenelse(Ebinop One(Etempvar _t'1 tulong)(Econst_int(Int.repr 64)tint)tint)
 (Sreturn(Some(Econst_int(Int.repr 0)tint)))Sskip.
Proof. reflexivity. Qed.
Definition digest_initial p k m := Callstate(Internal f_digest_text)[p]k m.
Definition digest_env p := PTree.set _s p(create_undef_temps(fn_temps f_digest_text)).
Lemma digest_entry ge p k m : store_edge ge(digest_initial p k m)
 (State f_digest_text(fn_body f_digest_text)k empty_env(digest_env p)m).
Proof.
 apply function_entry_source_edge;constructor.
 - constructor.
 - repeat constructor;cbn;intuition discriminate.
 - unfold list_disjoint,var_names;cbn;intros x y A B;
   repeat match goal with H:_ \/ _|-_=>destruct H end;try contradiction;subst;discriminate.
 - constructor.
 - reflexivity.
Qed.
Ltac digest_unfold s := let body := eval cbv [digest_prefix digest_suffix digest_strlen
 digest_length_check digest_init_loop digest_success digest_loop digest_body
 digest_increment digest_test digest_character digest_reject digest_digits digest_letters
 first_statement second_statement f_digest_text] in s in change s with body.
