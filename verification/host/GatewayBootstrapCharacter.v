(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual signed-char comparison recognizes precisely the slash byte. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Coqlib Integers.
Require Import Readers.
Open Scope Z_scope.

Lemma bootstrap_byte_word_zero_ext byte :
  Int.zero_ext 8 (Readers.byte_word byte) = Readers.byte_word byte.
Proof.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 (Readers.byte_word byte))).
  rewrite <- (Int.repr_unsigned (Readers.byte_word byte)) at 2.
  f_equal; rewrite Int.zero_ext_mod by (change (0 <= 8 < 32); lia).
  unfold Readers.byte_word.
  rewrite Int.unsigned_repr by (pose proof (Byte.unsigned_range byte);
    change Int.max_unsigned with 4294967295; change Byte.modulus with 256 in *; lia).
  change (two_p 8) with 256.
  apply Z.mod_small; pose proof (Byte.unsigned_range byte); change Byte.modulus with 256 in *; lia.
Qed.

Theorem bootstrap_signed_character_slash byte :
  Int.sign_ext 8 (Readers.byte_word byte) = Int.repr 47 <-> byte = Byte.repr 47.
Proof.
  split.
  - intro SAME.
    pose proof (f_equal (Int.zero_ext 8) SAME) as UNSIGNED.
    rewrite Int.zero_ext_sign_ext in UNSIGNED by lia.
    rewrite bootstrap_byte_word_zero_ext in UNSIGNED.
    change (Readers.byte_word byte = Int.repr 47) in UNSIGNED.
    pose proof (f_equal Int.unsigned UNSIGNED) as WORD.
    unfold Readers.byte_word in WORD.
    rewrite Int.unsigned_repr in WORD by (pose proof (Byte.unsigned_range byte);
      change Int.max_unsigned with 4294967295; change Byte.modulus with 256 in *; lia).
    change (Byte.unsigned byte = 47) in WORD.
    rewrite <- (Byte.repr_unsigned byte), WORD; reflexivity.
  - intro SAME; subst byte; reflexivity.
Qed.
