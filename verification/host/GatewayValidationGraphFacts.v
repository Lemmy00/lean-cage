(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Validation borrows actual children of the same received graph. *)
From Stdlib Require Import List.
From compcert Require Import Values Memory.
From HostGateway Require Import GatewayMachine GatewayObjects GatewayReferences GatewayOutcomeValidationContext GatewayBuiltinValidation.
Import ListNotations.

Theorem gateway_validation_captured_builtin {World} python objects decimal_float ledger held reserved captured original protected source environment
    memory world pointer :
  @gateway_outcome_validation_context World python objects decimal_float ledger held reserved captured original protected source environment memory world ->
  gateway_object_reachable captured original pointer ->
  exists description kind object offset,
    gateway_object_values captured pointer = Some description /\ gateway_object_kind description = Some kind /\ pointer = Vptr object offset.
Proof.
  intros CONTEXT REACHED.
  destruct (gateway_validation_reachable_builtin _ _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT REACHED)
    as [ROOT [description [kind [object [offset [VALUE [KIND [SAME POINTER]]]]]]]].
  exists description, kind, object, offset; split; [|auto].
  rewrite <- (gateway_validation_snapshot _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT pointer REACHED); exact VALUE.
Qed.

Theorem gateway_validation_dictionary_field_reachable captured original dictionary fields field :
  gateway_object_reachable captured original dictionary ->
  gateway_object_values captured dictionary = Some (gateway_dict_object fields) -> In field fields ->
  gateway_object_reachable captured original (gateway_dictionary_key field) /\
    gateway_object_reachable captured original (gateway_dictionary_value field).
Proof.
  intros REACHED FIELDS MEMBER; split; eapply gateway_reachable_child; [exact REACHED |exact FIELDS | |exact REACHED |exact FIELDS |];
    unfold gateway_object_children, gateway_dictionary_children; apply in_flat_map; exists field; cbn; auto.
Qed.
