(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The held dictionary is an actual mutable ancestor of recursive
   key/value calls; their source-produced exclusions prevent cycles through it. *)
From Stdlib Require Import List.
From HostGateway Require Import GatewayImport GatewayObjects GatewayValue GatewayObjectThreads
  GatewayReferenceAncestors GatewayReferenceGraphCapture.
Import ListNotations.
Local Close Scope lean_scope.

Lemma gateway_reference_dictionary_target held ticket parent values initial fields:
  gateway_object_values initial parent=Some(gateway_dict_object fields)->
  gateway_reference_mutable_target
    (held++[gateway_reference_graph_capture ticket parent
      (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields values))initial])parent.
Proof.
  intro LOOKUP;exists(gateway_reference_graph_capture ticket parent
    (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields values))initial),
    (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields values)),initial,(gateway_dict_object fields);split.
  - apply in_or_app;right;left;reflexivity.
  - split;[reflexivity|]. split;[exact LOOKUP|]. split;[exact I|reflexivity].
Qed.
