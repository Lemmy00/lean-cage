(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.digest: Exact source digest syntax, reads and interruption. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Require Import Readers WriteMemory Library.
Import ListNotations.
Open Scope Z_scope.
Lemma digest_character_read m p before byte after : c_string m p(before++byte::after) ->
 Mem.loadv Mint8signed m(Vptr(address_block p)
 (Ptrofs.add(Ptrofs.repr(address_offset p))(Ptrofs.repr(Z.of_nat(length before)))))=
 Some(Vint(Int.sign_ext 8(byte_word byte))).
Proof.
 intros[NONZERO[[OFFSET[SPAN SIZE]]LOAD]].
 rewrite<-app_assoc in LOAD.
 pose proof(load_suffix m(address_block p)(address_offset p)before(byte::after++[Byte.zero])LOAD)as SUFFIX.
 pose proof(load_first m(address_block p)(address_offset p+Z.of_nat(length before))[byte](after++[Byte.zero])SUFFIX)as SINGLE.
 assert(READ:Mem.load Mint8signed m(address_block p)(address_offset p+Z.of_nat(length before))=
 Some(Vint(Int.sign_ext 8(byte_word byte)))).
 { replace(Vint(Int.sign_ext 8(byte_word byte)))with(decode_val Mint8signed[Byte byte]).
   - eapply Mem.loadbytes_load;[exact SINGLE|apply Z.divide_1_l].
   - unfold byte_word;change(Vint(Int.sign_ext 8(Int.repr(Byte.unsigned byte+256*0)))=
     Vint(Int.sign_ext 8(Int.repr(Byte.unsigned byte))));rewrite Z.mul_0_r,Z.add_0_r;reflexivity. }
 rewrite !length_app in SPAN;cbn[length]in SPAN.
 rewrite Ptrofs.add_unsigned.
 rewrite(Ptrofs.unsigned_repr(address_offset p))by(unfold Ptrofs.max_unsigned;lia).
 rewrite(Ptrofs.unsigned_repr(Z.of_nat(length before)))by(unfold Ptrofs.max_unsigned;lia).
 unfold Mem.loadv;rewrite Ptrofs.unsigned_repr by(unfold Ptrofs.max_unsigned;lia).
 destruct(zle _ _)as[BOUND|OVER];[exact READ|change(address_offset p+Z.of_nat(length before)+1>Ptrofs.modulus)in OVER;lia].
Qed.
