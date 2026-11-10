(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The shared empty-object value describes an actual empty builtin
   pointer table, rather than an independently assumed constructor shape. *)
From Stdlib Require Import List.
From HostGateway Require Import GatewayImport GatewayObjects GatewayValue GatewayValueShapes.
Import ListNotations.
Local Close Scope lean_scope.

Lemma gateway_empty_dictionary_lookup decimal_float heap pointer:
  gateway_value_heap decimal_float heap pointer
    (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields[]))->
  gateway_object_values heap pointer=Some(gateway_dict_object[]).
Proof.
  intro VALUE;inversion VALUE;subst.
  assert(EMPTY_VALUES:values=[]).
  { apply gateway_wire_fields_injective;change(gateway_wire_fields values=List_nil_inst1 (Prod_inst3 gateway_wire_value gateway_wire_value));exact H. }
  subst values.
  match goal with ARRAY:gateway_dictionary_heap _ _ fields []|-_=>
    pose proof(gateway_heap_dictionary_lengths _ _ _ _ ARRAY)as EMPTY
  end.
  destruct fields;[assumption|discriminate].
Qed.
