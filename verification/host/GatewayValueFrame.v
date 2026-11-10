(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Refcount operations preserve the exact retained wire tree. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory.
From HostGateway Require Import GatewayImport GatewayPython GatewayObjects GatewayReferences GatewayValue.
Import ListNotations.
Local Close Scope lean_scope.

Scheme gateway_value_heap_mut := Induction for gateway_value_heap Sort Prop
with gateway_array_heap_mut := Induction for gateway_array_heap Sort Prop
with gateway_dictionary_heap_mut := Induction for gateway_dictionary_heap Sort Prop.
Combined Scheme gateway_heap_mutual from gateway_value_heap_mut,gateway_array_heap_mut,gateway_dictionary_heap_mut.

Definition gateway_reachable_values_frame heap next_heap root :Prop:=
  forall object value,gateway_object_reachable heap root object ->
    gateway_object_values heap object=Some value ->gateway_object_values next_heap object=Some value.

Lemma gateway_value_tree_map decimal_float heap next_heap :
  (forall object value,gateway_value_heap decimal_float heap object value ->
    forall root,gateway_object_reachable heap root object ->gateway_reachable_values_frame heap next_heap root ->
      gateway_value_heap decimal_float next_heap object value) /\
  (forall objects values,gateway_array_heap decimal_float heap objects values ->
    forall root,(forall object,In object objects->gateway_object_reachable heap root object) ->
      gateway_reachable_values_frame heap next_heap root ->gateway_array_heap decimal_float next_heap objects values) /\
  (forall fields values,gateway_dictionary_heap decimal_float heap fields values ->
    forall root,(forall field,In field fields ->gateway_object_reachable heap root(gateway_dictionary_key field) /\
      gateway_object_reachable heap root(gateway_dictionary_value field)) ->
      gateway_reachable_values_frame heap next_heap root ->gateway_dictionary_heap decimal_float next_heap fields values).
Proof.
  apply gateway_heap_mutual.
  - intros object LOOKUP root REACHED FRAME;constructor;apply FRAME;assumption.
  - intros object value LOOKUP root REACHED FRAME;constructor;apply FRAME;assumption.
  - intros object tag bytes value LOOKUP SCALAR root REACHED FRAME.
    eapply gateway_heap_scalar;[apply FRAME;eassumption|exact SCALAR].
  - intros object objects values LOOKUP ARRAY IH root REACHED FRAME.
    eapply gateway_heap_array;[apply FRAME;eassumption|].
    apply(IH root);[|exact FRAME]. intros child MEMBER.
    eapply gateway_reachable_child;[exact REACHED|exact LOOKUP|exact MEMBER].
  - intros object fields values LOOKUP FIELDS IH root REACHED FRAME.
    eapply gateway_heap_dictionary;[apply FRAME;eassumption|].
    apply(IH root);[|exact FRAME]. intros field MEMBER;split.
    + eapply gateway_reachable_child;[exact REACHED|exact LOOKUP|].
      unfold gateway_object_children,gateway_dictionary_children;apply in_flat_map.
      exists field;split;[exact MEMBER|left;reflexivity].
    + eapply gateway_reachable_child;[exact REACHED|exact LOOKUP|].
      unfold gateway_object_children,gateway_dictionary_children;apply in_flat_map.
      exists field;split;[exact MEMBER|right;left;reflexivity].
  - intros;constructor.
  - intros object value objects values VALUE HEAD ARRAY TAIL root REACHED FRAME.
    constructor.
    + apply(HEAD root);[apply REACHED;left;reflexivity|exact FRAME].
    + apply(TAIL root);[intros child MEMBER;apply REACHED;right;exact MEMBER|exact FRAME].
  - intros;constructor.
  - intros field key value fields values KEY KEY_IH VALUE VALUE_IH FIELDS REST_IH root REACHED FRAME.
    constructor.
    + apply(KEY_IH root);[exact(proj1(REACHED field ltac:(left;reflexivity)))|exact FRAME].
    + apply(VALUE_IH root);[exact(proj2(REACHED field ltac:(left;reflexivity)))|exact FRAME].
    + apply(REST_IH root);[intros child MEMBER;apply REACHED;right;exact MEMBER|exact FRAME].
Qed.

Theorem gateway_value_heap_retained python heap next next_heap decimal_float root value :
  gateway_value_heap decimal_float heap root value ->gateway_private_tree heap root ->
  gateway_rooted python heap root ->gateway_rooted next next_heap root ->
  gateway_objects_frame python heap next next_heap[] ->gateway_object_privacy_frame python heap next next_heap[] ->
  gateway_value_heap decimal_float next_heap root value.
Proof.
  intros VALUE PRIVATE ROOT NEXT FRAME PRIVACY.
  destruct(gateway_value_tree_map decimal_float heap next_heap)as[VALUES _].
  eapply VALUES;[exact VALUE|constructor|]. intros object actual REACHED LOOKUP.
  destruct(gateway_private_tree_frame python heap next next_heap root PRIVATE ROOT NEXT FRAME PRIVACY
    object REACHED)as[_[_[PRESERVED OWNED]]]. apply PRESERVED;exact LOOKUP.
Qed.

(* §FS-host-boundary.caller: Releasing a parsed child cannot change the independently held container. *)
Theorem gateway_reference_retains_parsed_tree python heap before consumed next next_heap after decimal_float root value :
  gateway_reference_return python heap before consumed next next_heap after ->root<>consumed ->
  (0<python_native_strong python root)%nat ->gateway_private_tree heap root ->gateway_destructible heap root ->
  gateway_value_heap decimal_float heap root value ->
  gateway_value_heap decimal_float next_heap root value /\gateway_private_tree next_heap root /\
    gateway_destructible next_heap root /\gateway_rooted next next_heap root.
Proof.
  intros RETURN DIFFERENT OWNED PRIVATE DESTRUCTIBLE VALUE.
  assert(NEXT_OWNED:(0<python_native_strong next root)%nat).
  { rewrite(gateway_reference_others _ _ _ _ _ _ _ RETURN root)by
      (intros[MEMBER|MEMBER];[congruence|contradiction]);exact OWNED. }
  assert(ROOT:gateway_rooted python heap root)by(apply gateway_direct_root;exact OWNED).
  assert(NEXT:gateway_rooted next next_heap root)by(apply gateway_direct_root;exact NEXT_OWNED).
  split.
  - eapply gateway_value_heap_retained;try eassumption.
    + exact(gateway_reference_values _ _ _ _ _ _ _ RETURN).
    + exact(gateway_reference_privacy _ _ _ _ _ _ _ RETURN).
  - destruct(gateway_private_tree_preserved python heap next next_heap root PRIVATE DESTRUCTIBLE ROOT NEXT
      (gateway_reference_values _ _ _ _ _ _ _ RETURN)(gateway_reference_privacy _ _ _ _ _ _ _ RETURN))
      as[AFTER_PRIVATE AFTER_DESTRUCTIBLE]. split;[exact AFTER_PRIVATE|]. split;assumption.
Qed.
