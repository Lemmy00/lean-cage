(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The integer branch's digit, leading-zero and negative-zero
   checks imply the specified canonical decimal value, using the received bytes exactly. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Integers.
From HostGateway Require Import GatewayObjects GatewayNumber.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_integer_digit byte:bool:=
  (48<=?Byte.unsigned byte)&&(Byte.unsigned byte<=?57).
Definition gateway_integer_digits_check bytes:bool:=
  match bytes with
  |[]=>false
  |first::rest=>forallb gateway_integer_digit bytes&&
    ((Nat.eqb(length bytes)1)||negb(Byte.eq first(Byte.repr 48)))
  end.
Definition gateway_integer_check bytes:bool:=
  match bytes with
  |[]=>false
  |first::rest=>if Byte.eq first(Byte.repr 45)then
      gateway_integer_digits_check rest&&negb(match rest with
        |[zero]=>Byte.eq zero(Byte.repr 48)|_=>false end)
    else gateway_integer_digits_check bytes
  end.

Lemma gateway_integer_digit_sound byte:
  gateway_integer_digit byte=true->48<=Byte.unsigned byte<=57.
Proof. unfold gateway_integer_digit;rewrite andb_true_iff,!Z.leb_le;tauto. Qed.

Theorem gateway_integer_digits_check_sound bytes:
  gateway_integer_digits_check bytes=true->gateway_decimal_digits bytes.
Proof.
  destruct bytes as[|first rest];[discriminate|].
  unfold gateway_integer_digits_check;rewrite andb_true_iff,orb_true_iff;intros[DIGITS[ONE|NONZERO]].
  all:split;[discriminate|];split.
  all:try solve[apply Forall_forall;intros byte MEMBER;
    apply gateway_integer_digit_sound;apply forallb_forall with(x:=byte)in DIGITS;assumption].
  - left;apply Nat.eqb_eq;exact ONE.
  - right;intros byte tail SAME;injection SAME as FIRST REST;subst byte tail.
    apply negb_true_iff in NONZERO;intro ZERO.
    assert(SAME_BYTE:first=Byte.repr 48)by(rewrite<-(Byte.repr_unsigned first),ZERO;reflexivity).
    rewrite SAME_BYTE,Byte.eq_true in NONZERO;discriminate.
Qed.

Lemma gateway_decimal_nonzero_first bytes:
  gateway_decimal_digits bytes->bytes<>[Byte.repr 48]->gateway_decimal_value bytes<>0.
Proof.
  intros[NONEMPTY[DIGITS LEADING]]NOTZERO ZERO.
  destruct bytes as[|first rest];[contradiction|].
  pose proof(Forall_inv DIGITS)as FIRST;pose proof(Forall_inv_tail DIGITS)as REST.
  pose proof(gateway_decimal_bounds rest REST)as BOUND.
  cbn[gateway_decimal_value]in ZERO.
  assert(HEAD:Byte.unsigned first=48).
  { assert(POSITIVE:0<10^Z.of_nat(length rest))by(apply Z.pow_pos_nonneg;lia).
    nia. }
  destruct LEADING as[LENGTH|LEADING];[|apply(LEADING first rest eq_refl);exact HEAD].
  destruct rest;[|discriminate].
  assert(SAME_BYTE:first=Byte.repr 48)by(rewrite<-(Byte.repr_unsigned first),HEAD;reflexivity).
  apply NOTZERO;rewrite SAME_BYTE;reflexivity.
Qed.

Theorem gateway_integer_check_sound bytes:
  gateway_integer_check bytes=true->exists value,gateway_decimal bytes value.
Proof.
  destruct bytes as[|first rest];[discriminate|].
  unfold gateway_integer_check.
  destruct(Byte.eq first(Byte.repr 45))eqn:SIGN.
  - rewrite andb_true_iff;intros[DIGITS NONZERO].
    pose proof(gateway_integer_digits_check_sound rest DIGITS)as CANONICAL.
    assert(NOTZERO:rest<>[Byte.repr 48]).
    { intro SAME;subst rest;change(negb true=true)in NONZERO;discriminate. }
    assert(FIRST:first=Byte.repr 45)by(apply Byte.same_if_eq;exact SIGN).
    subst first;exists(-gateway_decimal_value rest);constructor;[exact CANONICAL|].
    eapply gateway_decimal_nonzero_first;eassumption.
  - intro DIGITS;exists(gateway_decimal_value(first::rest));constructor.
    apply gateway_integer_digits_check_sound;exact DIGITS.
Qed.
