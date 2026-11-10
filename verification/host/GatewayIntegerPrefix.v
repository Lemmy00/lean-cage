(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real integer prefix checks and final digit flag combine
   into the canonical decimal condition; signed native bytes retain their wire identity. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers.
From HostGateway Require Import GatewayObjects GatewayIntegerCanonical GatewayIntegerLoop.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_integer_negative bytes:bool:=
  match bytes with []=>false|first::_=>Byte.eq first(Byte.repr 45)end.
Definition gateway_integer_digits bytes:list Byte.int:=
  if gateway_integer_negative bytes then tl bytes else bytes.
Definition gateway_integer_start bytes:Z:=if gateway_integer_negative bytes then 1 else 0.
Definition gateway_integer_head_check bytes:bool:=
  match bytes with
  |[]=>false
  |first::rest=>(Nat.eqb(length rest)0)||negb(Byte.eq first(Byte.repr 48))
  end.
Definition gateway_integer_initial_flag bytes:bool:=
  gateway_integer_head_check(gateway_integer_digits bytes)&&
    negb(gateway_integer_negative bytes&&match gateway_integer_digits bytes with
      |[zero]=>Byte.eq zero(Byte.repr 48)|_=>false end).

Lemma gateway_integer_signed_equal byte constant:
  0<=constant<128->Byte.eq byte(Byte.repr constant)=Z.eqb(Byte.signed byte)constant.
Proof.
  intro CONSTANT;destruct(Z.eq_dec(Byte.unsigned byte)constant)as[SAME|DIFFERENT].
  - assert(BYTE:byte=Byte.repr constant)by(rewrite<-(Byte.repr_unsigned byte),SAME;reflexivity).
    subst byte;rewrite Byte.eq_true,Byte.signed_repr by(change Byte.min_signed with (-128);
      change Byte.max_signed with 127;lia);symmetry;apply Z.eqb_refl.
  - rewrite Byte.eq_false by(intro SAME;apply(f_equal Byte.unsigned)in SAME;
      rewrite Byte.unsigned_repr in SAME by(change Byte.max_unsigned with 255;lia);congruence).
    symmetry;apply Z.eqb_neq;unfold Byte.signed.
    change Byte.half_modulus with 128;change Byte.modulus with 256.
    destruct(zlt(Byte.unsigned byte)128);[exact DIFFERENT|].
    pose proof(Byte.unsigned_range byte);change Byte.modulus with 256 in H;lia.
Qed.

Lemma gateway_integer_word_equal first second:
  0<=first<=32->0<=second<=32->Int64.eq(Int64.repr first)(Int64.repr second)=Z.eqb first second.
Proof.
  intros FIRST SECOND;destruct(Z.eq_dec first second)as[SAME|DIFFERENT].
  - subst second;rewrite Int64.eq_true;apply eq_sym,Z.eqb_refl.
  - rewrite Int64.eq_false.
    + symmetry;apply Z.eqb_neq;exact DIFFERENT.
    + intro SAME;apply(f_equal Int64.unsigned)in SAME;rewrite !Int64.unsigned_repr in SAME by
        (change Int64.max_unsigned with 18446744073709551615;lia);congruence.
Qed.

Lemma gateway_integer_word_less first second:
  0<=first<=32->0<=second<=32->Int64.ltu(Int64.repr first)(Int64.repr second)=(first<?second).
Proof.
  intros FIRST SECOND;unfold Int64.ltu;rewrite !Int64.unsigned_repr by
    (change Int64.max_unsigned with 18446744073709551615;lia).
  destruct(zlt first second);[symmetry;apply Z.ltb_lt|symmetry;apply Z.ltb_ge];lia.
Qed.

Lemma gateway_integer_small_equal first second:
  -128<=first<=127->-128<=second<=127->Int.eq(Int.repr first)(Int.repr second)=Z.eqb first second.
Proof.
  intros FIRST SECOND;destruct(Z.eq_dec first second)as[SAME|DIFFERENT].
  - subst second;rewrite Int.eq_true;apply eq_sym,Z.eqb_refl.
  - rewrite Int.eq_false.
    + symmetry;apply Z.eqb_neq;exact DIFFERENT.
    + intro SAME;apply(f_equal Int.signed)in SAME;rewrite !Int.signed_repr in SAME by
        (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia);congruence.
Qed.

Theorem gateway_integer_checked_flag bytes:
  gateway_integer_initial_flag bytes&&forallb gateway_integer_digit(gateway_integer_digits bytes)=gateway_integer_check bytes.
Proof.
  assert(REORDER:forall first second third:bool,(first&&second)&&third=(third&&first)&&second)
    by(intros[][][];reflexivity).
  destruct bytes as[|first rest];[reflexivity|].
  unfold gateway_integer_initial_flag,gateway_integer_digits,gateway_integer_negative,gateway_integer_check.
  destruct(Byte.eq first(Byte.repr 45))eqn:SIGN.
  - cbn[tl]. destruct rest as[|head tail];[reflexivity|].
    unfold gateway_integer_head_check,gateway_integer_digits_check.
    change(((Nat.eqb(length tail)0||negb(Byte.eq head(Byte.repr 48)))&&
      negb(match tail with[]=>Byte.eq head(Byte.repr 48)|_=>false end))&&
      forallb gateway_integer_digit(head::tail)=
      (forallb gateway_integer_digit(head::tail)&&(Nat.eqb(length tail)0||negb(Byte.eq head(Byte.repr 48))))&&
      negb(match tail with[]=>Byte.eq head(Byte.repr 48)|_=>false end)).
    apply REORDER.
  - unfold gateway_integer_head_check,gateway_integer_digits_check.
    change(((Nat.eqb(length rest)0||negb(Byte.eq first(Byte.repr 48)))&&true)&&
      forallb gateway_integer_digit(first::rest)=
      forallb gateway_integer_digit(first::rest)&&(Nat.eqb(length rest)0||negb(Byte.eq first(Byte.repr 48)))).
    rewrite andb_true_r;apply andb_comm.
Qed.
