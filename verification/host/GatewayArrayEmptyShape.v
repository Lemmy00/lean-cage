(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The shared empty-array value describes an actual empty builtin
   pointer table, rather than an independently assumed constructor shape. *)
From Stdlib Require Import List.
From HostGateway Require Import GatewayImport GatewayObjects GatewayValue GatewayValueShapes.
Import ListNotations.
Local Close Scope lean_scope.

Lemma gateway_empty_array_lookup decimal_float heap pointer:
  gateway_value_heap decimal_float heap pointer
    (LeanCage_Host_GatewayResponseCode_Value_array(gateway_wire_values[]))->
  gateway_object_values heap pointer=Some(gateway_list_object[]).
Proof.
  intro VALUE;inversion VALUE;subst.
  assert(EMPTY_VALUES:values=[]).
  { apply gateway_wire_values_injective;change(gateway_wire_values values=List_nil_inst1 gateway_wire_value);exact H. }
  subst values.
  match goal with ARRAY:gateway_array_heap _ _ objects []|-_=>
    pose proof(gateway_heap_array_lengths _ _ _ _ ARRAY)as EMPTY
  end.
  destruct objects;[assumption|discriminate].
Qed.
