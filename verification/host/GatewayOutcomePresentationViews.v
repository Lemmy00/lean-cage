(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The original copy and metadata keep their exact received views
   through the observed presentation callback. *)
From Stdlib Require Import List Lia.
From compcert Require Import Values.
From HostGateway Require Import GatewayPython GatewayObjects GatewayReferences GatewayValue GatewayValueFrame GatewayValueOwnership
  GatewayContainerGraph GatewayGraphSnapshots GatewayObjectThreads GatewayReferenceLedger GatewayReferenceHeld GatewayReferenceThreads
  GatewayOutcomeFields GatewayOutcomeMetadata GatewayPresentationContext.
Import ListNotations.
Local Close Scope lean_scope.

Lemma gateway_graph_region_subtree heap next_heap root child:
  gateway_graph_region_frame heap next_heap root ->gateway_object_reachable heap root child ->
  gateway_graph_region_frame heap next_heap child.
Proof. intros FRAME REACHED object CHILD;apply FRAME;eapply gateway_reachable_trans;eassumption. Qed.

Lemma gateway_outcome_field_graph_child heap dictionary fields field:
  gateway_object_values heap dictionary=Some(gateway_dict_object fields) ->In field fields ->
  gateway_object_reachable heap dictionary(gateway_dictionary_key field) /\
  gateway_object_reachable heap dictionary(gateway_dictionary_value field).
Proof.
  intros VALUE MEMBER;split;eapply gateway_reachable_child;[constructor|exact VALUE| |constructor|exact VALUE|].
  all:unfold gateway_object_children,gateway_dictionary_children;apply in_flat_map;exists field;split;[exact MEMBER|];cbn;auto.
Qed.

Theorem gateway_outcome_fields_snapshot {World}python objects decimal_float dictionary fields wires world next:
  @gateway_outcome_fields_view World python objects decimal_float dictionary fields wires world ->
  (0<python_native_strong(python next)dictionary)%nat ->
  gateway_graph_region_frame(objects world)(objects next)dictionary ->
  gateway_outcome_fields_view python objects decimal_float dictionary fields wires next.
Proof.
  intros VIEW OWNED FRAME.
  pose proof(gateway_outcome_fields_value _ _ _ _ _ _ _ VIEW)as VALUE.
  constructor;[exact OWNED|apply(proj1(FRAME dictionary(gateway_reachable_root _ _)));exact VALUE|
    exact(proj2(FRAME dictionary(gateway_reachable_root _ _)))|].
  assert(ROOTS:forall field,In field fields->gateway_graph_region_frame(objects world)(objects next)(gateway_dictionary_key field) /\
    gateway_graph_region_frame(objects world)(objects next)(gateway_dictionary_value field)).
  { intros field MEMBER;destruct(gateway_outcome_field_graph_child _ _ _ _ VALUE MEMBER)as[KEY ITEM];split;
      eapply gateway_graph_region_subtree;eassumption. }
  pose proof(gateway_outcome_fields_received _ _ _ _ _ _ _ VIEW)as RECEIVED.
  clear VIEW VALUE FRAME;induction RECEIVED;[constructor|].
  destruct(ROOTS x ltac:(left;reflexivity))as[KEY_FRAME ITEM_FRAME].
  destruct H as[[KEY_PRIVATE[KEY_DESTROY KEY_VALUE]][OUTPUT|[ITEM_PRIVATE[ITEM_DESTROY ITEM_VALUE]]]].
  - constructor.
    + split;[|left;exact OUTPUT]. destruct(gateway_graph_frame_tree _ _ _ KEY_DESTROY KEY_FRAME)as[PRIVATE DESTROY].
      exact(conj PRIVATE(conj DESTROY(gateway_graph_frame_value _ _ _ _ _ KEY_FRAME KEY_VALUE))).
    + apply IHRECEIVED;intros field MEMBER;apply ROOTS;right;exact MEMBER.
  - constructor.
    + split.
      * destruct(gateway_graph_frame_tree _ _ _ KEY_DESTROY KEY_FRAME)as[PRIVATE DESTROY].
        exact(conj PRIVATE(conj DESTROY(gateway_graph_frame_value _ _ _ _ _ KEY_FRAME KEY_VALUE))).
      * right;destruct(gateway_graph_frame_tree _ _ _ ITEM_DESTROY ITEM_FRAME)as[PRIVATE DESTROY].
        exact(conj PRIVATE(conj DESTROY(gateway_graph_frame_value _ _ _ _ _ ITEM_FRAME ITEM_VALUE))).
    + apply IHRECEIVED;intros field MEMBER;apply ROOTS;right;exact MEMBER.
Qed.

Theorem gateway_outcome_metadata_snapshot {World}python objects decimal_float dictionary fields field metadata wire world next:
  @gateway_outcome_metadata_view World python objects decimal_float dictionary fields field metadata wire world ->
  (0<python_native_strong(python next)dictionary)%nat ->
  gateway_graph_region_frame(objects world)(objects next)dictionary ->
  gateway_outcome_metadata_view python objects decimal_float dictionary fields field metadata wire next.
Proof.
  intros VIEW OWNED FRAME.
  pose proof(gateway_outcome_view_fields _ _ _ _ _ _ _ _ _ VIEW)as VALUE.
  pose proof(gateway_outcome_view_metadata _ _ _ _ _ _ _ _ _ VIEW)as LOOKUP.
  pose proof(gateway_outcome_view_value _ _ _ _ _ _ _ _ _ VIEW)as META.
  assert(REACHED:gateway_object_reachable(objects world)dictionary metadata).
  { rewrite<-META;exact(proj2(gateway_outcome_field_graph_child _ _ _ _ VALUE(proj1(gateway_dictionary_lookup_member _ _ _ LOOKUP)))). }
  pose proof(gateway_graph_region_subtree _ _ _ _ FRAME REACHED)as META_FRAME.
  destruct(gateway_graph_frame_tree _ _ _ (gateway_outcome_view_destructible _ _ _ _ _ _ _ _ _ VIEW)META_FRAME)as[PRIVATE DESTROY].
  constructor;[exact OWNED|apply(proj1(FRAME dictionary(gateway_reachable_root _ _)));exact VALUE|
    exact(proj2(FRAME dictionary(gateway_reachable_root _ _)))|exact LOOKUP|exact META|exact PRIVATE|exact DESTROY|].
  eapply gateway_graph_frame_value;[exact META_FRAME|exact(gateway_outcome_view_wire _ _ _ _ _ _ _ _ _ VIEW)].
Qed.

Lemma gateway_presentation_context_held {World}python objects decimal_float ledger held observed reserved captured protected source
    array displacement child memory world:
  @gateway_presentation_context World python objects decimal_float ledger held reserved captured protected source
    array displacement child memory world ->gateway_reference_scope python objects decimal_float ledger observed world ->
  gateway_presentation_context python objects decimal_float ledger observed reserved captured protected source array displacement child memory world.
Proof. intros[READY SCOPE BUDGET OWNED FRAME LOAD IMMUTABLE REACHED]OBSERVED;constructor;assumption. Qed.
