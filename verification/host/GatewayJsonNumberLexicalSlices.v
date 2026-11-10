(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Numeric source phases read exact suffixes of one retained input byte array. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Clight.
From HostGateway Require Import GatewayValue GatewayIntegerCanonical GatewayIntegerPrefix GatewayJsonNumberLexical
  GatewayJsonNumberSourceIntegerPrefix.
Import ListNotations.
Open Scope Z_scope.

Definition json_number_sign bytes := if gateway_integer_negative bytes then gateway_json_negative else gateway_json_positive.
Definition json_number_sign_prefix bytes := gateway_json_sign_bytes (json_number_sign bytes).

Theorem json_number_unsigned_source bytes :
  bytes = json_number_sign_prefix bytes ++ gateway_integer_digits bytes /\
  gateway_integer_start bytes = Z.of_nat (length (json_number_sign_prefix bytes)).
Proof.
  destruct bytes as [|first rest]; [split; reflexivity |].
  unfold json_number_sign_prefix, json_number_sign, gateway_integer_start, gateway_integer_digits, gateway_integer_negative.
  destruct (Byte.eq first (Byte.repr 45)) eqn:SIGN; cbn; [|split; reflexivity].
  apply Byte.same_if_eq in SIGN; subst first; split; reflexivity.
Qed.

Theorem json_number_lexical_split bytes : json_number_lexical bytes =
  match json_number_take_integer (gateway_integer_digits bytes) with
  | None => None
  | Some (integer, tail) => json_number_finish (json_number_sign bytes) integer tail
  end.
Proof.
  destruct bytes as [|first rest]; [reflexivity |].
  unfold json_number_sign, gateway_integer_digits, gateway_integer_negative; cbn [json_number_lexical].
  destruct (Byte.eq first (Byte.repr 45)); cbn [tl]; apply json_number_integer_after_split.
Qed.

Theorem json_number_integer_slice bytes integer tail :
  json_number_take_integer bytes = Some (integer, tail) -> bytes = integer ++ tail.
Proof.
  destruct bytes as [|first rest]; [discriminate |]. cbn [json_number_take_integer].
  destruct (Byte.eq first (Byte.repr 48)); [intro SAME; inversion SAME; reflexivity |].
  destruct ((49 <=? Byte.unsigned first) && (Byte.unsigned first <=? 57)); [|discriminate].
  pose proof (json_number_take_digits_sound rest) as PARTS.
  destruct (json_number_take_digits rest) as [digits remaining]; destruct PARTS as [REST _].
  intro SAME; inversion SAME; subst; cbn; f_equal; exact REST.
Qed.

Theorem json_number_slice_loads {World} (property : mem -> World -> Prop) object bytes prefix tail :
  bytes = prefix ++ tail ->
  (forall offset byte, nth_error bytes offset = Some byte -> forall memory world, property memory world ->
    Mem.loadv Mint8signed memory (Vptr object (Ptrofs.repr (Z.of_nat offset))) = Some (Vint (Int.repr (Byte.signed byte)))) ->
  forall offset byte, nth_error tail offset = Some byte -> forall memory world, property memory world ->
    Mem.loadv Mint8signed memory (Vptr object (Ptrofs.repr (Z.of_nat (length prefix) + Z.of_nat offset))) =
      Some (Vint (Int.repr (Byte.signed byte))).
Proof.
  intros BYTES LOADS offset byte SELECTED memory world GOOD.
  rewrite <- Nat2Z.inj_add; eapply (LOADS (length prefix + offset)%nat byte); [|exact GOOD].
  rewrite BYTES, nth_error_app2 by lia; replace (length prefix + offset - length prefix)%nat with offset by lia; exact SELECTED.
Qed.

Theorem json_number_slice_length (bytes prefix tail : list Byte.int) : bytes = prefix ++ tail ->
  Z.of_nat (length prefix) + Z.of_nat (length tail) = Z.of_nat (length bytes).
Proof. intro SAME; rewrite SAME, length_app, Nat2Z.inj_add; reflexivity. Qed.
