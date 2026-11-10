(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Initial chunk widths and actual unsigned machine arithmetic
   are bounded by the number payload, with no overflow before the SDK constructors. *)
From Stdlib Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers Values Memory Ctypes Ctypesdefs Cop.
Open Scope Z_scope.

Definition gateway_number_first_width count:Z:=if Z.eq_dec(count mod 9)0 then 9 else count mod 9.

Lemma gateway_number_first_width_bounds count:
  0<count->1<=gateway_number_first_width count<=9 /\gateway_number_first_width count<=count.
Proof.
  intro POSITIVE;pose proof(Z.mod_pos_bound count 9 ltac:(lia))as MODULO.
  unfold gateway_number_first_width;destruct(Z.eq_dec(count mod 9)0)as[ZERO|NONZERO];split;try lia.
  - destruct(zlt count 9);[rewrite Z.mod_small in ZERO by lia;lia|lia].
  - destruct(zlt count 9);[rewrite Z.mod_small by lia;lia|lia].
Qed.

Lemma gateway_number_subtract ge memory first second:
  sem_binary_operation ge Osub(Vlong(Int64.repr first))tulong(Vlong(Int64.repr second))tulong memory=
    Some(Vlong(Int64.repr(first-second))).
Proof.
  change(Some(Vlong(Int64.sub(Int64.repr first)(Int64.repr second)))=Some(Vlong(Int64.repr(first-second)))).
  unfold Int64.sub;f_equal;f_equal;apply Int64.eqm_samerepr.
  apply Int64.eqm_sub;apply Int64.eqm_unsigned_repr_l;apply Int64.eqm_refl.
Qed.

Lemma gateway_number_remainder ge memory count:
  0<=count<=65536->
  sem_binary_operation ge Omod(Vlong(Int64.repr count))tulong(Vint(Int.repr 9))tint memory=
    Some(Vlong(Int64.repr(count mod 9))).
Proof.
  intro COUNT.
  change (Some (Vlong (Int64.modu (Int64.repr count) (Int64.repr 9))) =
    Some (Vlong (Int64.repr (count mod 9)))).
  unfold Int64.modu;rewrite!Int64.unsigned_repr by(change Int64.max_unsigned with 18446744073709551615;lia);reflexivity.
Qed.

Lemma gateway_number_zero_width memory count:
  0<=count<=65536->
  sem_unary_operation Onotbool(Vlong(Int64.repr count))tulong memory=
    Some(Vint(if Z.eq_dec count 0 then Int.one else Int.zero)).
Proof.
  intro COUNT;change(Some(Val.of_bool(negb(negb(Int64.eq(Int64.repr count)Int64.zero))))=
    Some(Vint(if Z.eq_dec count 0 then Int.one else Int.zero))).
  rewrite Bool.negb_involutive.
  destruct(Z.eq_dec count 0)as[ZERO|NONZERO];[subst count;reflexivity|].
  rewrite Int64.eq_false;[reflexivity|]. intro SAME.
  apply(f_equal Int64.unsigned)in SAME;rewrite Int64.unsigned_repr in SAME by(change Int64.max_unsigned with 18446744073709551615;lia).
  rewrite Int64.unsigned_zero in SAME;congruence.
Qed.
