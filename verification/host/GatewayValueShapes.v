(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Shared wire lists retain every parsed builtin element and key;
   actual pointer-table observations select the same decoded container shape. *)
From Stdlib Require Import List.
From HostGateway Require Import GatewayImport GatewayObjects GatewayValue.
Import ListNotations.
Local Close Scope lean_scope.

Lemma gateway_wire_values_injective first second:
  gateway_wire_values first=gateway_wire_values second->first=second.
Proof.
  revert second;induction first as[|head tail IH];intros[|other rest]SAME;cbn in SAME;try discriminate;[reflexivity|].
  injection SAME as HEAD TAIL;subst other;f_equal;apply IH;exact TAIL.
Qed.

Lemma gateway_wire_fields_injective first second:
  gateway_wire_fields first=gateway_wire_fields second->first=second.
Proof.
  revert second;induction first as[|[key value]tail IH];intros[|[other_key other_value]rest]SAME;
    cbn in SAME;try discriminate;[reflexivity|].
  injection SAME as KEY VALUE TAIL;subst other_key other_value;f_equal;apply IH;exact TAIL.
Qed.

Theorem gateway_array_heap_from_value decimal_float heap pointer pointers values:
  gateway_object_values heap pointer=Some(gateway_list_object pointers)->
  gateway_value_heap decimal_float heap pointer
    (LeanCage_Host_GatewayResponseCode_Value_array(gateway_wire_values values))->
  gateway_array_heap decimal_float heap pointers values.
Proof.
  intros LOOKUP VALUE;inversion VALUE;subst.
  match goal with ARRAY:gateway_array_heap _ _ ?actual ?decoded|-_=>
    assert(actual=pointers)by congruence;
    assert(decoded=values)by(apply gateway_wire_values_injective;congruence);
    congruence
  end.
Qed.

Theorem gateway_dictionary_heap_from_value decimal_float heap pointer fields values:
  gateway_object_values heap pointer=Some(gateway_dict_object fields)->
  gateway_value_heap decimal_float heap pointer
    (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields values))->
  gateway_dictionary_heap decimal_float heap fields values.
Proof.
  intros LOOKUP VALUE;inversion VALUE;subst.
  match goal with FIELDS:gateway_dictionary_heap _ _ ?actual ?decoded|-_=>
    assert(actual=fields)by congruence;
    assert(decoded=values)by(apply gateway_wire_fields_injective;congruence);
    congruence
  end.
Qed.
