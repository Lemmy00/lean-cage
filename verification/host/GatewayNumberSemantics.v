(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Integer-only JSON tokens retain their exact integer object kind. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Floats.
From HostGateway Require Import GatewayValue GatewayObjects.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_integer_part_digits bytes :gateway_json_integer_part bytes ->
  Forall(fun byte=>48<=Byte.unsigned byte<=57)bytes.
Proof.
  intros[ZERO|[first[rest[BYTES[FIRST REST]]]]];subst bytes.
  - constructor;[change(48<=48<=57);lia|constructor].
  - constructor;[lia|exact REST].
Qed.

Lemma gateway_json_integer_byte sign digits byte :gateway_json_integer_part digits ->
  In byte(gateway_json_sign_bytes sign++digits) ->Byte.unsigned byte=45 \/48<=Byte.unsigned byte<=57.
Proof.
  intros INTEGER MEMBER;apply in_app_iff in MEMBER;destruct MEMBER as[SIGN|DIGIT].
  - destruct sign;cbn in SIGN;[contradiction|]. destruct SIGN as[SAME|IMPOSSIBLE];[subst byte;left;reflexivity|contradiction].
  - right;pose proof(gateway_integer_part_digits _ INTEGER)as DIGITS.
    apply Forall_forall with(x:=byte)in DIGITS;assumption.
Qed.

Theorem gateway_json_integer_no_float_marker sign digits :gateway_json_integer_part digits ->
  ~gateway_json_float_marker(gateway_json_sign_bytes sign++digits).
Proof.
  intros INTEGER[DOT|[UPPER|LOWER]].
  - pose proof(gateway_json_integer_byte sign digits(Byte.repr 46)INTEGER DOT)as RANGE.
    change(46=45 \/48<=46<=57)in RANGE;lia.
  - pose proof(gateway_json_integer_byte sign digits(Byte.repr 69)INTEGER UPPER)as RANGE.
    change(69=45 \/48<=69<=57)in RANGE;lia.
  - pose proof(gateway_json_integer_byte sign digits(Byte.repr 101)INTEGER LOWER)as RANGE.
    change(101=45 \/48<=101<=57)in RANGE;lia.
Qed.

Theorem gateway_json_integer_scalar_kind decimal_float sign digits value :
  gateway_json_integer_part digits ->
  gateway_scalar_semantics decimal_float 9(gateway_json_sign_bytes sign++digits)value ->
  exists integer,value=gateway_long_object integer.
Proof.
  intros INTEGER SCALAR;inversion SCALAR;subst;try(eexists;reflexivity).
  exfalso;eapply gateway_json_integer_no_float_marker;[exact INTEGER|eassumption].
Qed.
