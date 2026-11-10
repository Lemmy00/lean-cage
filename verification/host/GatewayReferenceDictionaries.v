(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual insertion adds the selected Unicode key and value to
   one private dictionary, preserving exact outside graphs and source reference counts. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers Values Memory.
From HostGateway Require Import GatewayImport GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue
  GatewayValueFrame GatewayValueOwnership GatewayObjectThreads GatewayContainerGraph GatewayReferenceLedger
  GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads.
Import ListNotations.
Local Close Scope lean_scope.

Lemma gateway_dictionary_children_append first second:
  gateway_dictionary_children(first++second)=gateway_dictionary_children first++gateway_dictionary_children second.
Proof. unfold gateway_dictionary_children;apply flat_map_app. Qed.

Lemma gateway_dictionary_heap_append decimal_float heap first first_values second second_values:
  gateway_dictionary_heap decimal_float heap first first_values->gateway_dictionary_heap decimal_float heap second second_values->
  gateway_dictionary_heap decimal_float heap(first++second)(first_values++second_values).
Proof. intros FIRST SECOND;induction FIRST;cbn;[exact SECOND|constructor;assumption]. Qed.

Lemma gateway_dictionary_heap_region_map decimal_float heap next_heap fields values:
  gateway_dictionary_heap decimal_float heap fields values->
  (forall pointer,In pointer(gateway_dictionary_children fields)->gateway_graph_region_frame heap next_heap pointer)->
  gateway_dictionary_heap decimal_float next_heap fields values.
Proof.
  intros FIELDS;induction FIELDS;intro FRAME;constructor.
  - eapply gateway_graph_frame_value;[apply FRAME;cbn[gateway_dictionary_children];left;reflexivity|exact H].
  - eapply gateway_graph_frame_value;[apply FRAME;cbn[gateway_dictionary_children];right;left;reflexivity|exact H0].
  - apply IHFIELDS;intros pointer MEMBER;apply FRAME;cbn[gateway_dictionary_children];right;right;exact MEMBER.
Qed.

Theorem gateway_reference_actual_dictionary_insert {World Event}(backend:gateway_backend World Event)
    python objects(containers:gateway_container_runtime backend python objects)
    decimal_float ledger held before world parent fields entries key characters key_value child child_value after next observed:
  gateway_reference_scope python objects decimal_float ledger held world->
  gateway_objects_ready(python world)(objects world)before->
  (0<python_native_strong(python world)parent)%nat->gateway_rooted(python world)(objects world)key->
  gateway_rooted(python world)(objects world)child->
  gateway_private_tree(objects world)parent->gateway_destructible(objects world)parent->
  gateway_object_values(objects world)parent=Some(gateway_dict_object fields)->
  gateway_dictionary_heap decimal_float(objects world)fields entries->
  gateway_object_values(objects world)key=Some(gateway_unicode_object characters)->
  gateway_dictionary_lookup characters fields=None->
  gateway_private_tree(objects world)key->gateway_destructible(objects world)key->
  gateway_value_heap decimal_float(objects world)key key_value->
  gateway_private_tree(objects world)child->gateway_destructible(objects world)child->
  gateway_value_heap decimal_float(objects world)child child_value->
  (forall pointer,In pointer(gateway_dictionary_children fields++[key;child])->
    ~gateway_object_reachable(objects world)pointer parent)->
  (forall captured,In captured held->~gateway_object_reachable(objects world)(gateway_held_object captured)parent)->
  gateway_object_operation backend gateway_api_dict_set[parent;key;child]before world(Vint Int.zero)after next observed->
  gateway_reference_scope python objects decimal_float ledger held next /\
  gateway_value_heap decimal_float(objects next)parent
    (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields(entries++[(key_value,child_value)]))) /\
  gateway_private_tree(objects next)parent /\gateway_destructible(objects next)parent /\
  (forall pointer,In pointer(gateway_dictionary_children fields++[key;child])->
    ~gateway_object_reachable(objects next)pointer parent) /\
  gateway_container_return(python world)(objects world)before parent(python next)(objects next)after
    (gateway_dict_object(fields++[{|gateway_dictionary_key:=key;gateway_dictionary_text:=characters;gateway_dictionary_value:=child|}])).
Proof.
  intros SCOPE READY OWNED KEY_ROOT CHILD_ROOT PRIVATE DESTROY LOOKUP FIELDS KEY_LOOKUP UNIQUE KEY_PRIVATE KEY_DESTROY KEY_VALUE
    CHILD_PRIVATE CHILD_DESTROY CHILD_VALUE ACYCLIC OUTSIDE OPERATION.
  assert(ROOT:gateway_rooted(python world)(objects world)parent)by(apply gateway_direct_root;exact OWNED).
  destruct(gateway_runtime_dict_insert _ _ _ containers before world parent fields key characters child after next observed
    READY ROOT KEY_ROOT CHILD_ROOT(PRIVATE parent(gateway_reachable_root _ _))LOOKUP KEY_LOOKUP UNIQUE OPERATION)as[RETURN STRONG].
  assert(ROOT_NEXT:gateway_rooted(python next)(objects next)parent).
  { apply gateway_direct_root;rewrite(gateway_container_references _ _ _ _ _ _ _ _ RETURN parent)by(intro NONE;inversion NONE);exact OWNED. }
  set(new_fields:=fields++[{|gateway_dictionary_key:=key;gateway_dictionary_text:=characters;gateway_dictionary_value:=child|}]).
  assert(NEXT_LOOKUP:gateway_object_values(objects next)parent=Some(gateway_dict_object new_fields)).
  { exact(gateway_container_value _ _ _ _ _ _ _ _ RETURN). }
  assert(CHILDREN_EQUAL:gateway_dictionary_children new_fields=gateway_dictionary_children fields++[key;child]).
  { unfold new_fields;rewrite gateway_dictionary_children_append;reflexivity. }
  assert(PREVIOUS:forall pointer,In pointer(gateway_dictionary_children fields++[key;child])->
    gateway_rooted(python world)(objects world)pointer /\gateway_private_tree(objects world)pointer /\gateway_destructible(objects world)pointer).
  { intros pointer MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|[SAME|EMPTY]]].
    - assert(REACHED:gateway_object_reachable(objects world)parent pointer)by(eapply gateway_reachable_child;[constructor|exact LOOKUP|exact OLD]).
      split;[eapply gateway_reachable_rooted;[exact ROOT|exact REACHED]|].
      split;[eapply gateway_private_reachable;[exact PRIVATE|exact REACHED]|].
      intros target PATH;apply DESTROY;eapply gateway_reachable_trans;eassumption.
    - subst pointer;exact(conj KEY_ROOT(conj KEY_PRIVATE KEY_DESTROY)).
    - subst pointer;exact(conj CHILD_ROOT(conj CHILD_PRIVATE CHILD_DESTROY)).
    - contradiction. }
  assert(FRAMES:forall pointer,In pointer(gateway_dictionary_children fields++[key;child])->gateway_graph_region_frame(objects world)(objects next)pointer).
  { intros pointer MEMBER;destruct(PREVIOUS pointer MEMBER)as[OLD_ROOT[OLD_PRIVATE OLD_DESTROY]].
    assert(NEXT_ROOT:gateway_rooted(python next)(objects next)pointer).
    { eapply gateway_child_root;[exact ROOT_NEXT|exact NEXT_LOOKUP|]. change(In pointer(gateway_dictionary_children new_fields));rewrite CHILDREN_EQUAL;exact MEMBER. }
    eapply gateway_container_region_frame;[exact RETURN|exact OLD_ROOT|exact NEXT_ROOT|exact OLD_PRIVATE|apply ACYCLIC;exact MEMBER]. }
  assert(CHILDREN:forall pointer,In pointer(gateway_object_children(gateway_dict_object new_fields))->
    gateway_private_tree(objects next)pointer /\gateway_destructible(objects next)pointer).
  { intros pointer MEMBER;change(In pointer(gateway_dictionary_children new_fields))in MEMBER;rewrite CHILDREN_EQUAL in MEMBER.
    apply(gateway_graph_frame_tree(objects world)(objects next)pointer);[exact(proj2(proj2(PREVIOUS pointer MEMBER)))|apply FRAMES;exact MEMBER]. }
  destruct(gateway_graph_from_children(objects next)parent(gateway_dict_object new_fields)gateway_dict_kind
    NEXT_LOOKUP(gateway_container_private _ _ _ _ _ _ _ _ RETURN)eq_refl ltac:(unfold gateway_destructor_kind;auto 9)CHILDREN)
    as[NEXT_PRIVATE NEXT_DESTROY].
  split;[eapply gateway_container_keeps_outside_held;eassumption|]. split.
  - apply gateway_heap_dictionary with(fields:=new_fields);[exact NEXT_LOOKUP|]. unfold new_fields;apply gateway_dictionary_heap_append.
    + eapply gateway_dictionary_heap_region_map;[exact FIELDS|]. intros pointer MEMBER;apply FRAMES;apply in_or_app;left;exact MEMBER.
    + constructor;[| |constructor].
      * eapply gateway_graph_frame_value;[apply FRAMES;apply in_or_app;right;left;reflexivity|exact KEY_VALUE].
      * eapply gateway_graph_frame_value;[apply FRAMES;apply in_or_app;right;right;left;reflexivity|exact CHILD_VALUE].
  - split;[exact NEXT_PRIVATE|]. split;[exact NEXT_DESTROY|]. split;[|exact RETURN].
    intros pointer MEMBER REACHED;apply(ACYCLIC pointer MEMBER).
    eapply gateway_graph_frame_reachable_back;[exact(proj2(proj2(PREVIOUS pointer MEMBER)))|apply FRAMES;exact MEMBER|exact REACHED].
Qed.
