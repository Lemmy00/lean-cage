(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual indexed acceptance supplies the required files and optional output layouts. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers Values.
From HostGateway Require Import GatewayObjects GatewayValidationFields GatewayOutcomeValidationPaths GatewayOutcomeMetadata.
Import ListNotations.

Lemma gateway_validation_dictionary_layout description kind :
  gateway_object_kind description = Some kind -> gateway_builtin_accepts gateway_dict_kind kind = true ->
  exists fields, description = gateway_dict_object fields.
Proof.
  destruct description; cbn; intros KIND ACCEPT; try discriminate; inversion KIND; subst; try discriminate; eauto.
Qed.

Lemma gateway_validation_unicode_layout description kind :
  gateway_object_kind description = Some kind -> gateway_builtin_accepts gateway_unicode_kind kind = true ->
  exists characters, description = gateway_unicode_object characters.
Proof.
  destruct description; cbn; intros KIND ACCEPT; try discriminate; inversion KIND; subst; try discriminate; eauto.
Qed.

Theorem gateway_validated_files_dictionary none captured fields :
  gateway_validated_field none captured fields 10 ->
  exists field contents,
    gateway_dictionary_lookup [102; 105; 108; 101; 115] fields = Some field /\
    gateway_object_values captured (gateway_dictionary_value field) = Some (gateway_dict_object contents).
Proof.
  intros (characters &field &description &kind &NAME &LOOKUP &DESCRIPTION &KIND &ACCEPT).
  change (Some [102; 105; 108; 101; 115] = Some characters) in NAME; inversion NAME; subst characters.
  destruct ACCEPT as [[OPTIONAL SAME] |ACCEPT]; [discriminate OPTIONAL |].
  change (gateway_builtin_accepts gateway_dict_kind kind = true) in ACCEPT.
  destruct (gateway_validation_dictionary_layout description kind KIND ACCEPT) as [contents SAME]; subst description.
  exists field, contents; auto.
Qed.

Theorem gateway_validated_optional_output none captured fields :
  gateway_validated_field none captured fields 11 ->
  exists field,
    gateway_dictionary_lookup gateway_outcome_output_name fields = Some field /\
    (gateway_dictionary_value field = Vptr none Ptrofs.zero \/
      exists characters, gateway_object_values captured (gateway_dictionary_value field) = Some (gateway_unicode_object characters)).
Proof.
  intros (characters &field &description &kind &NAME &LOOKUP &DESCRIPTION &KIND &ACCEPT).
  change (Some gateway_outcome_output_name = Some characters) in NAME; inversion NAME; subst characters.
  exists field; split; [exact LOOKUP |].
  destruct ACCEPT as [[OPTIONAL SAME] |ACCEPT]; [left; exact SAME |right].
  change (gateway_builtin_accepts gateway_unicode_kind kind = true) in ACCEPT.
  destruct (gateway_validation_unicode_layout description kind KIND ACCEPT) as [characters SAME]; subst description; eauto.
Qed.
