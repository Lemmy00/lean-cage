(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A source parser result retains exact older owners and a private
   snapshot of its decoded graph; no mutable older container can occur below a new leaf. *)
From Stdlib Require Import List.
From compcert Require Import Values Memory Clight.
From HostGateway Require Import GatewayImport GatewayPython GatewayObjects GatewayReferences GatewayValue GatewayObjectThreads
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceThreads GatewayReferenceNormalForm
  GatewayReferenceContainerScope GatewayReferenceGraphCapture GatewayReferenceValueProperties.
Import ListNotations.
Local Close Scope lean_scope.

Inductive gateway_wire_leaf:gateway_wire_value->Prop:=
|gateway_wire_null_leaf:gateway_wire_leaf LeanCage_Host_GatewayResponseCode_Value_null
|gateway_wire_boolean_leaf:forall flag,gateway_wire_leaf(LeanCage_Host_GatewayResponseCode_Value_boolean flag)
|gateway_wire_scalar_leaf:forall tag bytes,gateway_wire_leaf(LeanCage_Host_GatewayResponseCode_Value_scalar tag bytes).

Lemma gateway_value_leaf_shape decimal_float heap pointer wire:
  gateway_value_heap decimal_float heap pointer wire->gateway_wire_leaf wire->
  exists value,gateway_object_values heap pointer=Some value /\gateway_object_children value=[] /\
    ~gateway_mutable_container value.
Proof.
  intros VALUE LEAF;destruct VALUE;inversion LEAF;subst.
  - exists gateway_none_object;split;[exact H|]. split;[reflexivity|intros BAD;exact BAD].
  - exists(gateway_bool_object value);split;[exact H|]. split;[reflexivity|intros BAD;exact BAD].
  - exists value;split;[exact H|]. inversion H0;subst;split;try reflexivity;intros BAD;exact BAD.
Qed.

Record gateway_reference_decoded {World}(python:World->python_world)(objects:World->gateway_object_heap)decimal_float
    (ge:Clight.genv)context initial held wire ticket pointer final memory world:Prop:={
  gateway_decoded_formed:gateway_reference_ledger_well_formed final;
  gateway_decoded_entries:gateway_reference_result_entries context initial final ticket pointer;
  gateway_decoded_fresh_ticket:(gateway_reference_next initial<=ticket)%nat;
  gateway_decoded_owner:gateway_reference_owns final(gateway_reference_result(gateway_reference_depth context))
    ticket pointer;
  gateway_decoded_bound:gateway_reference_source_bound ge(Returnstate pointer context memory)final;
  gateway_decoded_scope:gateway_reference_scope python objects decimal_float final
    (held++[gateway_reference_graph_capture ticket pointer wire(objects world)])world;
  gateway_decoded_value:gateway_value_heap decimal_float(objects world)pointer wire;
  gateway_decoded_avoids:gateway_reference_avoids_old_mutable held(objects world)pointer
}.

Theorem gateway_reference_decoded_held_ticket_bound {World}python objects decimal_float ge context initial held captured wire ticket pointer final memory world:
  @gateway_reference_decoded World python objects decimal_float ge context initial held wire ticket pointer final memory world->
  In captured held->gateway_held_ticket captured<gateway_reference_next final.
Proof.
  intros DECODED MEMBER.
  pose proof(gateway_reference_capture_member _ _ _ _ _ _ _ (gateway_decoded_scope _ _ _ _ _ _ _ _ _ _ _ _ _ DECODED)
    ltac:(apply in_or_app;left;exact MEMBER))as[[owner OWNED]REST].
  pose proof(gateway_decoded_formed _ _ _ _ _ _ _ _ _ _ _ _ _ DECODED)as[UNIQUE[PLACES BOUNDS]].
  exact(proj1(Forall_forall _ _)BOUNDS _ OWNED).
Qed.

Theorem gateway_reference_leaf_receipt {World}python objects decimal_float ge context initial held captured wire ticket pointer final memory world:
  gateway_reference_ledger_well_formed final->
  gateway_reference_result_entries context initial final ticket pointer->
  (gateway_reference_next initial<=ticket)%nat->
  gateway_reference_source_bound ge(Returnstate pointer context memory)final->
  gateway_reference_owns final(gateway_reference_result(gateway_reference_depth context))ticket pointer->
  @gateway_reference_scope World python objects decimal_float final(held++[captured])world->
  gateway_held_object captured=pointer->gateway_held_ticket captured=ticket->
  gateway_value_heap decimal_float(objects world)pointer wire->gateway_wire_leaf wire->
  gateway_reference_decoded python objects decimal_float ge context initial held wire ticket pointer final memory world.
Proof.
  intros FORMED ENTRIES FRESH BOUND OWNER SCOPE POINTER TICKET VALUE LEAF.
  assert(OLD_SCOPE:gateway_reference_scope python objects decimal_float final held world).
  { eapply gateway_reference_scope_sublist;[exact SCOPE|intros previous MEMBER;apply in_or_app;left;exact MEMBER]. }
  constructor;try assumption.
  - pose proof(gateway_reference_graph_result python objects decimal_float final held captured world wire SCOPE
      ltac:(rewrite POINTER;exact VALUE))as GRAPH.
    rewrite POINTER,TICKET in GRAPH;exact GRAPH.
  - destruct(gateway_value_leaf_shape _ _ _ _ VALUE LEAF)as[description[LOOKUP[CHILDREN IMMUTABLE]]].
    eapply gateway_reference_leaf_excludes_old_mutable;eassumption.
Qed.
