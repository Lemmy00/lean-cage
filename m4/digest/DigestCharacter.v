(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.digest: Actual repeated reads and short-circuit character tests. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Readers Library Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMainNumber Require Import NumberControl.
From LeanCageMain Require Import Main MainStructure.
From LeanCageDigest Require Import DigestStructure DigestWords DigestValues.
Open Scope Z_scope.
Ltac digest_next := eapply store_next;[reflexivity| |].
Ltac digest_route := digest_next;[apply unchanged_store_edge;WriteAll.structural|].
Definition digest_signed_value b := Vint(Int.sign_ext 8(byte_word b)).
Definition digest_digits_env le b := PTree.set _t'2(Val.of_bool(digest_digit b))
 (if 48<=?digest_signed b then PTree.set _t'7(digest_signed_value b)(PTree.set _t'6(digest_signed_value b)le)
 else PTree.set _t'6(digest_signed_value b)le).
Definition digest_letters_env le b := PTree.set _t'3(Val.of_bool(digest_digit b||digest_letter b))
 (if digest_digit b then le else
 if 97<=?digest_signed b then PTree.set _t'5(digest_signed_value b)(PTree.set _t'4(digest_signed_value b)le)
 else PTree.set _t'4(digest_signed_value b)le).
Definition digest_digits_count b := if 48<=?digest_signed b then 8%nat else 5%nat.
Definition digest_letters_count b := if digest_digit b then 2%nat else if 97<=?digest_signed b then 12%nat else 6%nat.
Lemma digest_digits_source le m p i b k : digest_registers le p i->0<=i<=64->
 Mem.loadv Mint8signed m(Vptr(address_block p)(Ptrofs.add(Ptrofs.repr(address_offset p))(Ptrofs.repr i)))=
 Some(digest_signed_value b)->
 store_path main_ge(fun after=>after=m)(State f_digest_text digest_digits k empty_env le m)
 (digest_digits_count b)(State f_digest_text Sskip k empty_env(digest_digits_env le b)m).
Proof.
 intros REGS RANGE LOAD;destruct REGS as[PTR INDEX].
 unfold digest_digits_count,digest_digits_env,digest_digit;digest_unfold digest_digits.
 destruct(48<=?digest_signed b)eqn:LOW;cbn[andb].
 - digest_route;digest_next.
   + apply certified_set_edge;eapply digest_read_expression;[split;eassumption|exact RANGE|exact LOAD].
   + digest_route;digest_next.
     * eapply certified_if_edge with(v:=Val.of_bool(48<=?digest_signed b))(b:=true).
       -- apply digest_lower_expression;[apply PTree.gss|lia].
       -- rewrite number_bool_value,LOW;reflexivity.
     * digest_route;digest_next.
       -- apply certified_set_edge;eapply digest_read_expression;
          [split;WriteAll.lookup|exact RANGE|exact LOAD].
       -- digest_route;digest_next.
          ++ apply certified_set_edge;apply digest_upper_expression;[apply PTree.gss|lia].
          ++ apply store_done;reflexivity.
 - digest_route;digest_next.
   + apply certified_set_edge;eapply digest_read_expression;[split;eassumption|exact RANGE|exact LOAD].
   + digest_route;digest_next.
     * eapply certified_if_edge with(v:=Val.of_bool(48<=?digest_signed b))(b:=false).
       -- apply digest_lower_expression;[apply PTree.gss|lia].
       -- rewrite number_bool_value,LOW;reflexivity.
     * digest_next;[apply certified_set_edge;apply old_expression_value;apply value_int|].
       apply store_done;reflexivity.
Qed.
Lemma digest_letters_source le m p i b k : digest_registers le p i->0<=i<=64->
 le!_t'2=Some(Val.of_bool(digest_digit b))->
 Mem.loadv Mint8signed m(Vptr(address_block p)(Ptrofs.add(Ptrofs.repr(address_offset p))(Ptrofs.repr i)))=
 Some(digest_signed_value b)->
 store_path main_ge(fun after=>after=m)(State f_digest_text digest_letters k empty_env le m)
 (digest_letters_count b)(State f_digest_text Sskip k empty_env(digest_letters_env le b)m).
Proof.
 intros[PTR INDEX]RANGE DIGIT LOAD;unfold digest_letters_count,digest_letters_env;digest_unfold digest_letters.
 destruct(digest_digit b)eqn:ISDIGIT;cbn[orb].
 - digest_next.
   + eapply certified_if_edge with(v:=Val.of_bool true)(b:=true).
     * apply old_expression_value;apply value_temp;exact DIGIT.
     * reflexivity.
   + digest_next;[apply certified_set_edge;apply old_expression_value;apply value_int|].
     apply store_done;reflexivity.
 - unfold digest_letter;destruct(97<=?digest_signed b)eqn:LOW;cbn[andb].
   + digest_next.
     * eapply certified_if_edge with(v:=Val.of_bool false)(b:=false).
       -- apply old_expression_value;apply value_temp;exact DIGIT.
       -- reflexivity.
     * digest_route;digest_next.
       -- apply certified_set_edge;eapply digest_read_expression;[split;eassumption|exact RANGE|exact LOAD].
       -- digest_route;digest_next.
          ++ eapply certified_if_edge with(v:=Val.of_bool(97<=?digest_signed b))(b:=true).
             ** apply digest_lower_expression;[apply PTree.gss|lia].
             ** rewrite number_bool_value,LOW;reflexivity.
          ++ digest_route;digest_route;digest_next.
             ** apply certified_set_edge;eapply digest_read_expression;
                [split;WriteAll.lookup|exact RANGE|exact LOAD].
             ** digest_route;digest_next.
                --- apply certified_set_edge;apply digest_upper_expression;[apply PTree.gss|lia].
                --- digest_route;digest_next.
                    +++ apply certified_set_edge;eapply cast_expression_value;
                        [apply old_expression_value;apply value_temp;apply PTree.gss|apply number_bool_cast].
                    +++ rewrite PTree.set2;apply store_done;reflexivity.
   + digest_next.
     * eapply certified_if_edge with(v:=Val.of_bool false)(b:=false).
       -- apply old_expression_value;apply value_temp;exact DIGIT.
       -- reflexivity.
     * digest_route;digest_next.
       -- apply certified_set_edge;eapply digest_read_expression;[split;eassumption|exact RANGE|exact LOAD].
       -- digest_route;digest_next.
          ++ eapply certified_if_edge with(v:=Val.of_bool(97<=?digest_signed b))(b:=false).
             ** apply digest_lower_expression;[apply PTree.gss|lia].
             ** rewrite number_bool_value,LOW;reflexivity.
          ++ digest_next;[apply certified_set_edge;eapply cast_expression_value;
             [apply old_expression_value;apply value_int|reflexivity]|].
             apply store_done;reflexivity.
Qed.
Lemma digest_digits_registers le p i b : digest_registers le p i->digest_registers(digest_digits_env le b)p i.
Proof. intros[PTR INDEX];unfold digest_digits_env,digest_registers;destruct(48<=?digest_signed b);split;WriteAll.lookup. Qed.
Lemma digest_letters_registers le p i b : digest_registers le p i->digest_registers(digest_letters_env le b)p i.
Proof.
 intros[PTR INDEX];unfold digest_letters_env,digest_registers;
 destruct(digest_digit b);try destruct(97<=?digest_signed b);split;WriteAll.lookup.
Qed.
Definition digest_character_env le b := digest_letters_env(digest_digits_env le b)b.
Definition digest_character_count b := (2+digest_digits_count b+digest_letters_count b)%nat.
Lemma digest_character_source le m p i b k : digest_registers le p i->0<=i<=64->
 Mem.loadv Mint8signed m(Vptr(address_block p)(Ptrofs.add(Ptrofs.repr(address_offset p))(Ptrofs.repr i)))=
 Some(digest_signed_value b)->
 store_path main_ge(fun after=>after=m)(State f_digest_text digest_character k empty_env le m)
 (digest_character_count b)(State f_digest_text Sskip k empty_env(digest_character_env le b)m).
Proof.
 intros REGS RANGE LOAD;unfold digest_character_count,digest_character_env.
 replace(2+digest_digits_count b+digest_letters_count b)%nat with
 (S(digest_digits_count b+S(digest_letters_count b)))%nat by lia.
 change digest_character with(Ssequence digest_digits digest_letters);digest_route.
 eapply store_path_trans;[eapply digest_digits_source;eassumption|].
 digest_route;apply digest_letters_source with(p:=p)(i:=i);try assumption.
 - apply digest_digits_registers;exact REGS.
 - unfold digest_digits_env;apply PTree.gss.
Qed.
Lemma digest_character_result le b : (digest_character_env le b)!_t'3=Some(Val.of_bool(digest_hex b)).
Proof. unfold digest_character_env,digest_letters_env;rewrite PTree.gss,digest_hex_split;reflexivity. Qed.
Lemma digest_character_registers le p i b : digest_registers le p i->digest_registers(digest_character_env le b)p i.
Proof. intros REGS;apply digest_letters_registers,digest_digits_registers;exact REGS. Qed.
Lemma digest_character_bound b : (digest_character_count b<=22)%nat.
Proof.
 unfold digest_character_count,digest_digits_count,digest_letters_count;
 destruct(48<=?digest_signed b);destruct(digest_digit b);destruct(97<=?digest_signed b);lia.
Qed.
