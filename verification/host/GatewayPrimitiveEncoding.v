(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Primitive tree framing consumes the same decoded tag byte. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayImport GatewayWordData GatewayWordsMemory GatewayWordReceipt GatewayWordValues GatewayValue.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Lemma gateway_actual_tag_encoding byte tag :
  Byte.unsigned byte=Z.of_nat tag ->
  LeanCage_Host_GatewayWords_Encoding(Nat_of_nat 1)(Nat_of_nat tag)(gateway_wire_bytes[byte]).
Proof.
  intro TAG;pose proof(gateway_decoded_encoding[byte])as ENCODED.
  rewrite gateway_decoded_single,TAG,Nat2Z.id in ENCODED;exact ENCODED.
Qed.

Theorem gateway_null_source_encoding byte :
  Byte.unsigned byte=0 ->
  LeanCage_Host_GatewayResponseWords_SourceEncoded
    (LeanCage_Host_GatewayResponseCode_Subject_value LeanCage_Host_GatewayResponseCode_Value_null)
    (gateway_wire_bytes[byte]).
Proof.
  intro TAG;eapply LeanCage_Host_GatewayResponseWords_SourceEncoded_null.
  exact(gateway_actual_tag_encoding byte 0 TAG).
Qed.

Theorem gateway_boolean_source_encoding byte(flag:bool) :
  Byte.unsigned byte=(if flag then 2 else 1) ->
  LeanCage_Host_GatewayResponseWords_SourceEncoded
    (LeanCage_Host_GatewayResponseCode_Subject_value
      (LeanCage_Host_GatewayResponseCode_Value_boolean(if flag then Bool_true else Bool_false)))
    (gateway_wire_bytes[byte]).
Proof.
  intro TAG;eapply LeanCage_Host_GatewayResponseWords_SourceEncoded_boolean.
  destruct flag;[exact(gateway_actual_tag_encoding byte 2 TAG)|exact(gateway_actual_tag_encoding byte 1 TAG)].
Qed.
