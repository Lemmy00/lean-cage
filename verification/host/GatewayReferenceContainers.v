(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual borrowed container operations preserve source reference counts
   and the exact separately owned graph regions. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers Values Memory.
From HostGateway Require Import GatewayImport GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue
  GatewayValueFrame GatewayValueOwnership GatewayObjectThreads GatewayContainerGraph GatewayReferenceLedger
  GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads.
Import ListNotations.
Local Close Scope lean_scope.

Lemma gateway_array_heap_region_map decimal_float heap next_heap pointers values:
  gateway_array_heap decimal_float heap pointers values->
  (forall pointer,In pointer pointers->gateway_graph_region_frame heap next_heap pointer)->
  gateway_array_heap decimal_float next_heap pointers values.
Proof.
  intros ARRAY;induction ARRAY;intro FRAME;constructor.
  - eapply gateway_graph_frame_value;[apply FRAME;left;reflexivity|exact H].
  - apply IHARRAY;intros pointer MEMBER;apply FRAME;right;exact MEMBER.
Qed.

Theorem gateway_reference_actual_append {World Event}(backend:gateway_backend World Event)
    python objects(containers:gateway_container_runtime backend python objects)
    decimal_float ledger held before world parent pointers values child child_value after next observed:
  gateway_reference_scope python objects decimal_float ledger held world->
  gateway_objects_ready(python world)(objects world)before->
  (0<python_native_strong(python world)parent)%nat->gateway_rooted(python world)(objects world)child->
  gateway_private_tree(objects world)parent->gateway_destructible(objects world)parent->
  gateway_object_values(objects world)parent=Some(gateway_list_object pointers)->
  gateway_array_heap decimal_float(objects world)pointers values->
  gateway_private_tree(objects world)child->gateway_destructible(objects world)child->
  gateway_value_heap decimal_float(objects world)child child_value->
  (forall pointer,In pointer(pointers++[child])->~gateway_object_reachable(objects world)pointer parent)->
  (forall captured,In captured held->~gateway_object_reachable(objects world)(gateway_held_object captured)parent)->
  gateway_object_operation backend gateway_api_list_append[parent;child]before world(Vint Int.zero)after next observed->
  gateway_reference_scope python objects decimal_float ledger held next /\
  gateway_value_heap decimal_float(objects next)parent
    (LeanCage_Host_GatewayResponseCode_Value_array(gateway_wire_values(values++[child_value]))) /\
  gateway_private_tree(objects next)parent /\gateway_destructible(objects next)parent /\
  (forall pointer,In pointer(pointers++[child])->~gateway_object_reachable(objects next)pointer parent) /\
  gateway_container_return(python world)(objects world)before parent(python next)(objects next)after
    (gateway_list_object(pointers++[child])).
Proof.
  intros SCOPE READY OWNED CHILD_ROOT PRIVATE DESTROY LOOKUP ARRAY CHILD_PRIVATE CHILD_DESTROY CHILD_VALUE
    ACYCLIC OUTSIDE OPERATION.
  assert(ROOT:gateway_rooted(python world)(objects world)parent)by(apply gateway_direct_root;exact OWNED).
  destruct(gateway_runtime_list_append _ _ _ containers before world parent pointers child after next observed
    READY ROOT CHILD_ROOT (PRIVATE parent(gateway_reachable_root _ _))LOOKUP OPERATION)as[RETURN STRONG].
  assert(ROOT_NEXT:gateway_rooted(python next)(objects next)parent).
  { apply gateway_direct_root;rewrite(gateway_container_references _ _ _ _ _ _ _ _ RETURN parent)by(intro NONE;inversion NONE);exact OWNED. }
  assert(NEXT_LOOKUP:gateway_object_values(objects next)parent=Some(gateway_list_object(pointers++[child]))).
  { exact(gateway_container_value _ _ _ _ _ _ _ _ RETURN). }
  assert(FRAMES:forall pointer,In pointer(pointers++[child])->gateway_graph_region_frame(objects world)(objects next)pointer).
  { intros pointer MEMBER.
    assert(PREVIOUS:gateway_private_tree(objects world)pointer).
    { apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|EMPTY]];[|subst pointer;exact CHILD_PRIVATE|contradiction].
      eapply gateway_private_reachable;[exact PRIVATE|]. eapply gateway_reachable_child;[constructor|exact LOOKUP|exact OLD]. }
    assert(OLD_ROOT:gateway_rooted(python world)(objects world)pointer).
    { apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|EMPTY]];[|subst pointer;exact CHILD_ROOT|contradiction].
      eapply gateway_child_root;[exact ROOT|exact LOOKUP|exact OLD]. }
    assert(NEXT_ROOT:gateway_rooted(python next)(objects next)pointer).
    { eapply gateway_child_root;[exact ROOT_NEXT|exact NEXT_LOOKUP|exact MEMBER]. }
    eapply gateway_container_region_frame;[exact RETURN|exact OLD_ROOT|exact NEXT_ROOT|exact PREVIOUS|apply ACYCLIC;exact MEMBER]. }
  assert(CHILDREN:forall pointer,In pointer(pointers++[child])->
    gateway_private_tree(objects next)pointer /\gateway_destructible(objects next)pointer).
  { intros pointer MEMBER;apply(gateway_graph_frame_tree(objects world)(objects next)pointer);[|apply FRAMES;exact MEMBER].
    apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|EMPTY]];[|subst pointer;exact CHILD_DESTROY|contradiction].
    intros target REACHED;apply DESTROY;eapply gateway_reachable_trans;[|exact REACHED].
    eapply gateway_reachable_child;[constructor|exact LOOKUP|exact OLD]. }
  destruct(gateway_graph_from_children(objects next)parent(gateway_list_object(pointers++[child]))gateway_list_kind
    NEXT_LOOKUP(gateway_container_private _ _ _ _ _ _ _ _ RETURN)eq_refl ltac:(unfold gateway_destructor_kind;auto 9)CHILDREN)
    as[NEXT_PRIVATE NEXT_DESTROY].
  split;[eapply gateway_container_keeps_outside_held;eassumption|]. split.
  - apply gateway_heap_array with(objects:=pointers++[child]);[exact NEXT_LOOKUP|].
    apply gateway_array_heap_append.
    + eapply gateway_array_heap_region_map;[exact ARRAY|]. intros pointer MEMBER;apply FRAMES;apply in_or_app;left;exact MEMBER.
    + constructor;[|constructor]. eapply gateway_graph_frame_value;[apply FRAMES;apply in_or_app;right;left;reflexivity|exact CHILD_VALUE].
  - split;[exact NEXT_PRIVATE|]. split;[exact NEXT_DESTROY|]. split;[|exact RETURN].
    intros pointer MEMBER REACHED;apply(ACYCLIC pointer MEMBER).
    eapply gateway_graph_frame_reachable_back;[|apply FRAMES;exact MEMBER|exact REACHED].
    apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|EMPTY]];[|subst pointer;exact CHILD_DESTROY|contradiction].
    intros target PATH;apply DESTROY;eapply gateway_reachable_trans;[|exact PATH].
    eapply gateway_reachable_child;[constructor|exact LOOKUP|exact OLD].
Qed.
