(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Dictionary insertion inputs follow from the same held parent,
   key and value snapshots, retaining aliases and excluding old mutable ancestors. *)
From Stdlib Require Import List.
From HostGateway Require Import GatewayImport GatewayPython GatewayObjects GatewayReferences GatewayValue GatewayValueFrame
  GatewayObjectThreads GatewayGraphSnapshots GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceThreads
  GatewayReferenceContainerScope GatewayReferenceGraphCapture GatewayReferenceValueProperties GatewayReferenceSnapshotInputs GatewayContainerGraph.
Import ListNotations.
Local Close Scope lean_scope.

Lemma gateway_graph_snapshot_dictionary decimal_float initial current parent fields values:
  gateway_object_values initial parent=Some(gateway_dict_object fields)->
  gateway_graph_snapshot initial current parent->gateway_dictionary_heap decimal_float initial fields values->
  gateway_dictionary_heap decimal_float current fields values.
Proof.
  intros LOOKUP SNAPSHOT FIELDS.
  destruct(gateway_value_tree_map decimal_float initial current)as[_[_ MAP]].
  eapply MAP;[exact FIELDS| |].
  - intros field MEMBER;split;eapply gateway_reachable_child;[constructor|exact LOOKUP| |constructor|exact LOOKUP|];
      unfold gateway_object_children,gateway_dictionary_children;apply in_flat_map;exists field;split;
      [exact MEMBER|left;reflexivity|exact MEMBER|right;left;reflexivity].
  - intros pointer value REACHED VALUE;rewrite SNAPSHOT by exact REACHED;exact VALUE.
Qed.

Lemma gateway_graph_snapshot_dictionary_no_cycle initial current parent fields:
  gateway_object_values initial parent=Some(gateway_dict_object fields)->
  gateway_destructible initial parent->gateway_graph_snapshot initial current parent->
  (forall pointer,In pointer(gateway_dictionary_children fields)->~gateway_object_reachable initial pointer parent)->
  forall pointer,In pointer(gateway_dictionary_children fields)->~gateway_object_reachable current pointer parent.
Proof.
  intros LOOKUP DESTROY SNAPSHOT ACYCLIC pointer MEMBER REACHED;apply(ACYCLIC pointer MEMBER).
  assert(CHILD:gateway_object_reachable initial parent pointer).
  { eapply gateway_reachable_child;[constructor|exact LOOKUP|exact MEMBER]. }
  eapply gateway_graph_snapshot_backward;[|eapply gateway_graph_snapshot_subtree;[exact SNAPSHOT|exact CHILD]|exact REACHED].
  intros object LATER;apply DESTROY;eapply gateway_reachable_trans;eassumption.
Qed.

Theorem gateway_reference_dictionary_snapshot_inputs {World}python objects decimal_float ledger held world
    owner ticket parent fields entries parent_initial key_ticket key key_value key_initial characters child_ticket child child_value child_initial:
  @gateway_reference_scope World python objects decimal_float ledger
    (held++[gateway_reference_graph_capture ticket parent
      (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields entries))parent_initial;
      gateway_reference_graph_capture key_ticket key key_value key_initial;
      gateway_reference_graph_capture child_ticket child child_value child_initial])world->
  gateway_reference_owns ledger owner ticket parent->
  gateway_reference_graphs_only held->gateway_reference_snapshots_avoid held parent->
  gateway_object_values parent_initial parent=Some(gateway_dict_object fields)->
  gateway_dictionary_heap decimal_float parent_initial fields entries->
  gateway_object_values key_initial key=Some(gateway_unicode_object characters)->
  gateway_dictionary_lookup characters fields=None->
  (forall pointer,In pointer(gateway_dictionary_children fields)->~gateway_object_reachable parent_initial pointer parent)->
  ~gateway_object_reachable key_initial key parent->~gateway_object_reachable child_initial child parent->
  gateway_reference_scope python objects decimal_float ledger
    (held++[gateway_reference_graph_capture key_ticket key key_value key_initial;
      gateway_reference_graph_capture child_ticket child child_value child_initial])world /\
  gateway_rooted(python world)(objects world)key /\gateway_rooted(python world)(objects world)child /\
  gateway_private_tree(objects world)parent /\gateway_destructible(objects world)parent /\
  gateway_object_values(objects world)parent=Some(gateway_dict_object fields) /\
  gateway_dictionary_heap decimal_float(objects world)fields entries /\
  gateway_object_values(objects world)key=Some(gateway_unicode_object characters) /\
  gateway_dictionary_lookup characters fields=None /\
  gateway_private_tree(objects world)key /\gateway_destructible(objects world)key /\
  gateway_value_heap decimal_float(objects world)key key_value /\
  gateway_private_tree(objects world)child /\gateway_destructible(objects world)child /\
  gateway_value_heap decimal_float(objects world)child child_value /\
  (forall pointer,In pointer(gateway_dictionary_children fields++[key;child])->~gateway_object_reachable(objects world)pointer parent) /\
  (forall captured,In captured(held++[gateway_reference_graph_capture key_ticket key key_value key_initial;
      gateway_reference_graph_capture child_ticket child child_value child_initial])->
    ~gateway_object_reachable(objects world)(gateway_held_object captured)parent).
Proof.
  intros SCOPE OWNED GRAPHS OUTSIDE LOOKUP FIELDS KEY_LOOKUP UNIQUE ACYCLIC KEY_OUTSIDE CHILD_OUTSIDE.
  set(parent_capture:=gateway_reference_graph_capture ticket parent
    (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields entries))parent_initial).
  set(key_capture:=gateway_reference_graph_capture key_ticket key key_value key_initial).
  set(child_capture:=gateway_reference_graph_capture child_ticket child child_value child_initial).
  assert(PARENT_MEMBER:In parent_capture(held++[parent_capture;key_capture;child_capture]))by(apply in_or_app;right;left;reflexivity).
  assert(KEY_MEMBER:In key_capture(held++[parent_capture;key_capture;child_capture]))by(apply in_or_app;right;right;left;reflexivity).
  assert(CHILD_MEMBER:In child_capture(held++[parent_capture;key_capture;child_capture]))by(apply in_or_app;right;right;right;left;reflexivity).
  destruct(gateway_reference_capture_member _ _ _ _ _ _ _ SCOPE PARENT_MEMBER)
    as[PARENT_OWNED[PRIVATE[DESTROY[PARENT_VALUE[PARENT_DESTROY PARENT_SNAPSHOT]]]]].
  destruct(gateway_reference_capture_member _ _ _ _ _ _ _ SCOPE KEY_MEMBER)
    as[[key_owner KEY_OWNED][KEY_PRIVATE[KEY_DESTROY[KEY_VALUE[KEY_INITIAL_DESTROY KEY_SNAPSHOT]]]]].
  destruct(gateway_reference_capture_member _ _ _ _ _ _ _ SCOPE CHILD_MEMBER)
    as[[child_owner CHILD_OWNED][CHILD_PRIVATE[CHILD_DESTROY[CHILD_VALUE[CHILD_INITIAL_DESTROY CHILD_SNAPSHOT]]]]].
  assert(KEY_FREE:~gateway_object_reachable(objects world)key parent).
  { eapply gateway_reference_graph_exclusion;[exact SCOPE|exact KEY_MEMBER|exact KEY_OUTSIDE]. }
  assert(CHILD_FREE:~gateway_object_reachable(objects world)child parent).
  { eapply gateway_reference_graph_exclusion;[exact SCOPE|exact CHILD_MEMBER|exact CHILD_OUTSIDE]. }
  split.
  - eapply gateway_reference_scope_sublist;[exact SCOPE|]. intros captured MEMBER.
    apply in_app_or in MEMBER;apply in_or_app;destruct MEMBER as[OLD|[SAME|[SAME|EMPTY]]];
      [left;exact OLD|right;right;left;exact SAME|right;right;right;left;exact SAME|contradiction].
  - split;[eapply gateway_reference_owned_rooted;[exact(proj1 SCOPE)|exact KEY_OWNED]|].
    split;[eapply gateway_reference_owned_rooted;[exact(proj1 SCOPE)|exact CHILD_OWNED]|].
    split;[exact PRIVATE|]. split;[exact DESTROY|]. split.
    + rewrite PARENT_SNAPSHOT by constructor;exact LOOKUP.
    + split;[eapply gateway_graph_snapshot_dictionary;eassumption|]. split.
      * rewrite KEY_SNAPSHOT by constructor;exact KEY_LOOKUP.
      * split;[exact UNIQUE|]. split;[exact KEY_PRIVATE|]. split;[exact KEY_DESTROY|]. split;[exact KEY_VALUE|].
        split;[exact CHILD_PRIVATE|]. split;[exact CHILD_DESTROY|]. split;[exact CHILD_VALUE|]. split.
        -- intros pointer MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|[SAME|EMPTY]]].
           ++ eapply gateway_graph_snapshot_dictionary_no_cycle;eassumption.
           ++ subst pointer;exact KEY_FREE.
           ++ subst pointer;exact CHILD_FREE.
           ++ contradiction.
        -- intros captured MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|[SAME|EMPTY]]].
           ++ eapply gateway_reference_snapshots_exclude;[|exact GRAPHS|exact OUTSIDE|exact OLD].
              eapply gateway_reference_scope_sublist;[exact SCOPE|intros previous IN;apply in_or_app;left;exact IN].
           ++ subst captured;exact KEY_FREE.
           ++ subst captured;exact CHILD_FREE.
           ++ contradiction.
Qed.
