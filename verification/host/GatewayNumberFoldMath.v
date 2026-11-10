(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Source-selected initial and later nine-digit chunks cover
   the exact remaining digits and compose to their arbitrary-size decimal value. *)
From Stdlib Require Import ZArith List Lia Ring.
From compcert Require Import Coqlib Integers.
From HostGateway Require Import GatewayObjects GatewayNumber GatewayNumberWidth.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_number_remaining_multiple count:
  (count-gateway_number_first_width count)mod 9=0.
Proof.
  pose proof(Z.div_mod count 9 ltac:(lia))as SPLIT.
  unfold gateway_number_first_width;destruct(Z.eq_dec(count mod 9)0)as[ZERO|NONZERO].
  - rewrite ZERO in SPLIT;replace(count-9)with((count/9-1)*9)by lia;apply Z.mod_mul;lia.
  - replace(count-count mod 9)with((count/9)*9)by lia;apply Z.mod_mul;lia.
Qed.

Lemma gateway_number_nine_available {A:Type}(remaining:list A):
  remaining<>[]->Z.of_nat(length remaining)mod 9=0->(9<=length remaining)%nat.
Proof.
  intros NONEMPTY MULTIPLE;destruct(le_lt_dec 9(length remaining));[assumption|].
  rewrite Z.mod_small in MULTIPLE by lia.
  destruct remaining;[contradiction|cbn in MULTIPLE;lia].
Qed.

Lemma gateway_number_skip_nine_multiple {A:Type}(remaining:list A):
  (9<=length remaining)%nat->Z.of_nat(length remaining)mod 9=0->Z.of_nat(length(skipn 9 remaining))mod 9=0.
Proof.
  intros SIZE MULTIPLE;rewrite skipn_length,Nat2Z.inj_sub by lia.
  pose proof(Z.div_mod(Z.of_nat(length remaining))9 ltac:(lia))as SPLIT;rewrite MULTIPLE in SPLIT.
  change((Z.of_nat(length remaining)-9)mod 9=0).
  replace(Z.of_nat(length remaining)-9)with(((Z.of_nat(length remaining))/9-1)*9)by lia;apply Z.mod_mul;lia.
Qed.

Lemma gateway_number_nine_fold accumulator chunk remaining:
  length chunk=9%nat->
  gateway_number_fold accumulator(chunk++remaining)=
    gateway_number_fold(accumulator*1000000000+gateway_decimal_value chunk)remaining.
Proof.
  intro WIDTH;rewrite!gateway_number_fold_exact,gateway_decimal_append,length_app,Nat2Z.inj_add,WIDTH.
  rewrite Z.pow_add_r by lia;change(10^Z.of_nat 9)with 1000000000;ring.
Qed.

Lemma gateway_number_zero_chunk chunk:
  gateway_number_fold 0 chunk=gateway_decimal_value chunk.
Proof. rewrite gateway_number_fold_exact;ring. Qed.
