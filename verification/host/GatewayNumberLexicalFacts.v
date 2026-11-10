(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The validated same-byte JSON parts determine whether the
   actual constructor is an integer or a single decimal-to-binary conversion. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers.
From HostGateway Require Import GatewayValue GatewayIntegerPrefix GatewayJsonNumberLexical GatewayJsonNumberLexicalSlices.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_number_lexical_parts bytes parts:
  json_number_lexical bytes=Some parts->
  gateway_json_integer_part(json_parts_integer parts) /\gateway_json_fraction(json_parts_fraction parts) /\gateway_json_exponent(json_parts_exponent parts).
Proof.
  destruct bytes as[|first rest];[discriminate|]. cbn[json_number_lexical].
  destruct(Byte.eq first(Byte.repr 45));intro PARSED;
    destruct(json_number_integer_after_sound _ _ _ PARSED)as[SIGN[WIRE PARTS]];exact PARTS.
Qed.

Theorem gateway_number_integer_part_digits digits:
  gateway_json_integer_part digits->digits<>[] /\Forall(fun byte=>48<=Byte.unsigned byte<=57)digits.
Proof.
  intros[ZERO|[first[rest[SAME[FIRST REST]]]]];subst digits.
  - split;[discriminate|]. constructor;[change(48<=48<=57);lia|constructor].
  - split;[discriminate|]. constructor;[lia|exact REST].
Qed.

Theorem gateway_number_lexical_integer bytes parts:
  json_number_lexical bytes=Some parts->json_parts_sign parts=GatewayJsonNumberLexicalSlices.json_number_sign bytes->
  gateway_integer_start bytes+Z.of_nat(length(json_parts_integer parts))=Z.of_nat(length bytes)->
  bytes=json_number_sign_prefix bytes++json_parts_integer parts /\gateway_json_integer_part(json_parts_integer parts).
Proof.
  intros PARSED SIGN END.
  destruct(json_number_lexical_sound bytes parts PARSED)as[WIRE VALID].
  destruct(gateway_number_lexical_parts bytes parts PARSED)as[INTEGER[FRACTION EXPONENT]].
  pose proof(proj2(json_number_unsigned_source bytes))as START.
  unfold json_number_parts_wire in WIRE;rewrite SIGN in WIRE.
  change(bytes=json_number_sign_prefix bytes++json_parts_integer parts++json_parts_fraction parts++json_parts_exponent parts)in WIRE.
  rewrite START in END.
  pose proof(f_equal(fun value:list Byte.int=>Z.of_nat(length value))WIRE)as LENGTH.
  cbv beta in LENGTH.
  rewrite!length_app,!Nat2Z.inj_add in LENGTH.
  assert(FRACTION_EMPTY:json_parts_fraction parts=[])by(apply length_zero_iff_nil;lia).
  assert(EXPONENT_EMPTY:json_parts_exponent parts=[])by(apply length_zero_iff_nil;lia).
  split;[rewrite FRACTION_EMPTY,EXPONENT_EMPTY,!app_nil_r in WIRE;exact WIRE|exact INTEGER].
Qed.

Theorem gateway_number_lexical_integer_semantics decimal_float bytes parts:
  json_number_lexical bytes=Some parts->json_parts_sign parts=GatewayJsonNumberLexicalSlices.json_number_sign bytes->
  gateway_integer_start bytes+Z.of_nat(length(json_parts_integer parts))=Z.of_nat(length bytes)->
  gateway_scalar_semantics decimal_float 9 bytes
    (GatewayObjects.gateway_long_object(if gateway_integer_negative bytes then -GatewayObjects.gateway_decimal_value(json_parts_integer parts)
      else GatewayObjects.gateway_decimal_value(json_parts_integer parts))).
Proof.
  intros PARSED SIGN END;destruct(gateway_number_lexical_integer bytes parts PARSED SIGN END)as[BYTES INTEGER].
  assert(SEMANTICS:gateway_scalar_semantics decimal_float 9
    (json_number_sign_prefix bytes++json_parts_integer parts)
    (GatewayObjects.gateway_long_object(gateway_json_signed(GatewayJsonNumberLexicalSlices.json_number_sign bytes)
      (GatewayObjects.gateway_decimal_value(json_parts_integer parts)))))by(apply gateway_scalar_json_integer;exact INTEGER).
  rewrite<-BYTES in SEMANTICS.
  unfold GatewayJsonNumberLexicalSlices.json_number_sign in SEMANTICS;destruct(gateway_integer_negative bytes);exact SEMANTICS.
Qed.

Theorem gateway_number_lexical_float bytes parts:
  json_number_lexical bytes=Some parts->json_parts_sign parts=GatewayJsonNumberLexicalSlices.json_number_sign bytes->
  gateway_integer_start bytes+Z.of_nat(length(json_parts_integer parts))<>Z.of_nat(length bytes)->
  gateway_json_float_marker bytes.
Proof.
  intros PARSED SIGN DIFFERENT.
  destruct(json_number_lexical_sound bytes parts PARSED)as[WIRE VALID].
  destruct(gateway_number_lexical_parts bytes parts PARSED)as[INTEGER[FRACTION EXPONENT]].
  assert(NONEMPTY:json_parts_fraction parts<>[] \/json_parts_exponent parts<>[]).
  { destruct(json_parts_fraction parts)as[|f fs]eqn:FRACTION_BYTES;[|left;discriminate].
    right;intro EMPTY;apply DIFFERENT.
    unfold json_number_parts_wire in WIRE;rewrite FRACTION_BYTES,EMPTY,SIGN,!app_nil_r in WIRE.
    change(bytes=json_number_sign_prefix bytes++json_parts_integer parts)in WIRE.
    rewrite(proj2(json_number_unsigned_source bytes)).
    pose proof(f_equal(fun value:list Byte.int=>Z.of_nat(length value))WIRE)as LENGTH.
    cbv beta in LENGTH.
    rewrite length_app,Nat2Z.inj_add in LENGTH;lia. }
  destruct parts as[sign integer fraction exponent];cbn in *.
  rewrite WIRE;unfold json_number_parts_wire,gateway_json_float_marker;cbn.
  destruct FRACTION.
  - destruct EXPONENT.
    + destruct NONEMPTY;contradiction.
    + destruct H as[LOWER|UPPER];subst marker.
      * right;right;apply in_or_app;right;apply in_or_app;right;cbn;left;reflexivity.
      * right;left;apply in_or_app;right;apply in_or_app;right;cbn;left;reflexivity.
  - left;apply in_or_app;right;apply in_or_app;right;cbn;left;reflexivity.
Qed.
