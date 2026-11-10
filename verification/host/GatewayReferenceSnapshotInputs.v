(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual held snapshots justify mutation separation at a
   recursive append, rather than a separate assumed safe heap history. *)
From Stdlib Require Import List.
From HostGateway Require Import GatewayImport GatewayPython GatewayObjects GatewayReferences GatewayValue GatewayValueFrame
  GatewayObjectThreads GatewayGraphSnapshots GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceThreads
  GatewayReferenceContainerScope GatewayReferenceGraphCapture GatewayReferenceValueProperties GatewayContainerGraph.
Import ListNotations.
Local Close Scope lean_scope.

Definition gateway_reference_snapshots_avoid held excluded:Prop:=
  forall captured,In captured held->forall wire initial,
    gateway_held_view captured=gateway_held_graph_value wire initial->
    ~gateway_object_reachable initial(gateway_held_object captured)excluded.

Lemma gateway_reference_snapshots_exclude {World}python objects decimal_float ledger held world captured excluded:
  @gateway_reference_scope World python objects decimal_float ledger held world->
  gateway_reference_graphs_only held->gateway_reference_snapshots_avoid held excluded->In captured held->
  ~gateway_object_reachable(objects world)(gateway_held_object captured)excluded.
Proof.
  intros SCOPE GRAPHS AVOID MEMBER;destruct(GRAPHS captured MEMBER)as[wire[initial VIEW]].
  destruct captured as[ticket pointer description];cbn in VIEW|-*;subst description.
  eapply gateway_reference_graph_exclusion;[exact SCOPE|exact MEMBER|apply(AVOID _ MEMBER wire initial);reflexivity].
Qed.

Lemma gateway_graph_snapshot_subtree initial current root child:
  gateway_graph_snapshot initial current root->gateway_object_reachable initial root child->
  gateway_graph_snapshot initial current child.
Proof. intros SNAPSHOT REACHED pointer LATER;apply SNAPSHOT;eapply gateway_reachable_trans;eassumption. Qed.

Lemma gateway_graph_snapshot_array decimal_float initial current parent pointers values:
  gateway_object_values initial parent=Some(gateway_list_object pointers)->
  gateway_graph_snapshot initial current parent->gateway_array_heap decimal_float initial pointers values->
  gateway_array_heap decimal_float current pointers values.
Proof.
  intros LOOKUP SNAPSHOT ARRAY.
  destruct(gateway_value_tree_map decimal_float initial current)as[_[MAP _]].
  eapply MAP;[exact ARRAY| |].
  - intros pointer MEMBER;eapply gateway_reachable_child;[constructor|exact LOOKUP|exact MEMBER].
  - intros pointer value REACHED VALUE;rewrite SNAPSHOT by exact REACHED;exact VALUE.
Qed.

Lemma gateway_graph_snapshot_no_cycle initial current parent pointers:
  gateway_object_values initial parent=Some(gateway_list_object pointers)->
  gateway_destructible initial parent->gateway_graph_snapshot initial current parent->
  (forall pointer,In pointer pointers->~gateway_object_reachable initial pointer parent)->
  forall pointer,In pointer pointers->~gateway_object_reachable current pointer parent.
Proof.
  intros LOOKUP DESTROY SNAPSHOT ACYCLIC pointer MEMBER REACHED;apply(ACYCLIC pointer MEMBER).
  assert(CHILD:gateway_object_reachable initial parent pointer).
  { eapply gateway_reachable_child;[constructor|exact LOOKUP|exact MEMBER]. }
  eapply gateway_graph_snapshot_backward;[|eapply gateway_graph_snapshot_subtree;[exact SNAPSHOT|exact CHILD]|exact REACHED].
  intros object LATER;apply DESTROY;eapply gateway_reachable_trans;eassumption.
Qed.

Theorem gateway_reference_array_snapshot_inputs {World}python objects decimal_float ledger held world
    owner ticket parent pointers values parent_initial child_ticket child child_value child_initial:
  @gateway_reference_scope World python objects decimal_float ledger
    (held++[gateway_reference_graph_capture ticket parent
      (LeanCage_Host_GatewayResponseCode_Value_array(gateway_wire_values values))parent_initial;
      gateway_reference_graph_capture child_ticket child child_value child_initial])world->
  gateway_reference_owns ledger owner ticket parent->
  gateway_reference_graphs_only held->gateway_reference_snapshots_avoid held parent->
  gateway_object_values parent_initial parent=Some(gateway_list_object pointers)->
  gateway_array_heap decimal_float parent_initial pointers values->
  (forall pointer,In pointer pointers->~gateway_object_reachable parent_initial pointer parent)->
  ~gateway_object_reachable child_initial child parent->
  gateway_reference_scope python objects decimal_float ledger
    (held++[gateway_reference_graph_capture child_ticket child child_value child_initial])world /\
  gateway_rooted(python world)(objects world)child /\
  gateway_private_tree(objects world)parent /\gateway_destructible(objects world)parent /\
  gateway_object_values(objects world)parent=Some(gateway_list_object pointers) /\
  gateway_array_heap decimal_float(objects world)pointers values /\
  gateway_private_tree(objects world)child /\gateway_destructible(objects world)child /\
  gateway_value_heap decimal_float(objects world)child child_value /\
  (forall pointer,In pointer(pointers++[child])->~gateway_object_reachable(objects world)pointer parent) /\
  (forall captured,In captured(held++[gateway_reference_graph_capture child_ticket child child_value child_initial])->
    ~gateway_object_reachable(objects world)(gateway_held_object captured)parent).
Proof.
  intros SCOPE OWNED GRAPHS OUTSIDE LOOKUP ARRAY ACYCLIC CHILD_OUTSIDE.
  set(parent_capture:=gateway_reference_graph_capture ticket parent
    (LeanCage_Host_GatewayResponseCode_Value_array(gateway_wire_values values))parent_initial).
  set(child_capture:=gateway_reference_graph_capture child_ticket child child_value child_initial).
  assert(PARENT_MEMBER:In parent_capture(held++[parent_capture;child_capture]))by(apply in_or_app;right;left;reflexivity).
  assert(CHILD_MEMBER:In child_capture(held++[parent_capture;child_capture]))by(apply in_or_app;right;right;left;reflexivity).
  destruct(gateway_reference_capture_member _ _ _ _ _ _ _ SCOPE PARENT_MEMBER)
    as[PARENT_OWNED[PRIVATE[DESTROY[PARENT_VALUE[PARENT_DESTROY PARENT_SNAPSHOT]]]]].
  destruct(gateway_reference_capture_member _ _ _ _ _ _ _ SCOPE CHILD_MEMBER)
    as[[child_owner CHILD_OWNED][CHILD_PRIVATE[CHILD_DESTROY[CHILD_VALUE[CHILD_INITIAL_DESTROY CHILD_SNAPSHOT]]]]].
  assert(CHILD_FREE:~gateway_object_reachable(objects world)child parent).
  { eapply gateway_reference_graph_exclusion;[exact SCOPE|exact CHILD_MEMBER|exact CHILD_OUTSIDE]. }
  split.
  - eapply gateway_reference_scope_sublist;[exact SCOPE|]. intros captured MEMBER.
    apply in_app_or in MEMBER;apply in_or_app;destruct MEMBER as[OLD|[SAME|EMPTY]];
      [left;exact OLD|right;right;left;exact SAME|contradiction].
  - split;[eapply gateway_reference_owned_rooted;[exact(proj1 SCOPE)|exact CHILD_OWNED]|].
    split;[exact PRIVATE|]. split;[exact DESTROY|]. split.
    + rewrite PARENT_SNAPSHOT by constructor;exact LOOKUP.
    + split;[eapply gateway_graph_snapshot_array;eassumption|].
      split;[exact CHILD_PRIVATE|]. split;[exact CHILD_DESTROY|]. split;[exact CHILD_VALUE|]. split.
      * intros pointer MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|EMPTY]].
        -- eapply gateway_graph_snapshot_no_cycle;eassumption.
        -- subst pointer;exact CHILD_FREE.
        -- contradiction.
      * intros captured MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|EMPTY]].
        -- eapply gateway_reference_snapshots_exclude;[|exact GRAPHS|exact OUTSIDE|exact OLD].
           eapply gateway_reference_scope_sublist;[exact SCOPE|intros previous IN;apply in_or_app;left;exact IN].
        -- subst captured;exact CHILD_FREE.
        -- contradiction.
Qed.
