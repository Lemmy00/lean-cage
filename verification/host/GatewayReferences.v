(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Reference release preserves independently rooted parser values. *)
From Stdlib Require Import ZArith Lia List.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects.
Import ListNotations.

Inductive gateway_object_reachable(heap:gateway_object_heap)(root:Values.val):Values.val->Prop:=
| gateway_reachable_root:gateway_object_reachable heap root root
| gateway_reachable_child:forall parent value child,
    gateway_object_reachable heap root parent ->gateway_object_values heap parent=Some value ->
    In child(gateway_object_children value) ->gateway_object_reachable heap root child.

Definition gateway_destructor_kind kind :Prop:=
  kind=gateway_none_kind \/kind=gateway_bool_kind \/kind=gateway_long_kind \/kind=gateway_float_kind \/
  kind=gateway_unicode_kind \/kind=gateway_bytes_kind \/kind=gateway_list_kind \/kind=gateway_dict_kind.

(* Parser constructors return exact builtins. This explicit condition excludes
   arbitrary foreign finalizers; IsInstance success is not a producer of it. *)
Definition gateway_destructible heap root :Prop:=
  forall object,gateway_object_reachable heap root object ->exists value kind,
    gateway_object_values heap object=Some value /\gateway_object_kind value=Some kind /\
    gateway_destructor_kind kind.

Definition gateway_private_tree heap root :Prop:=
  forall object,gateway_object_reachable heap root object ->gateway_object_private heap object=true.

Record gateway_reference_return python heap before object next next_heap after :Prop:={
  gateway_reference_ready:gateway_objects_ready next next_heap after;
  gateway_reference_owned:python_native_strong python object=S(python_native_strong next object);
  gateway_reference_others:gateway_native_references_frame python next[object];
  gateway_reference_values:gateway_objects_frame python heap next next_heap[];
  gateway_reference_privacy:gateway_object_privacy_frame python heap next next_heap[];
  gateway_reference_native:python_private_frame python before after;
  gateway_reference_native_retained:forall block,Mem.valid_block before block ->
    gateway_native_private python block ->gateway_native_private next block
}.

Record gateway_reference_runtime {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(objects:World->gateway_object_heap) :Prop:={
  gateway_runtime_incref_objects:forall before world object result after next observed,
    gateway_objects_ready(python world)(objects world)before ->python_live(python world)object ->
    gateway_object_operation backend gateway_api_incref[object]before world result after next observed ->
    python_incref_return(python world)object before(python next)after /\
    gateway_objects_ready(python next)(objects next)after /\
    gateway_objects_frame(python world)(objects world)(python next)(objects next)[] /\
    gateway_object_privacy_frame(python world)(objects world)(python next)(objects next)[] /\
    gateway_object_values(objects next)object=gateway_object_values(objects world)object /\
    gateway_object_private(objects next)object=gateway_object_private(objects world)object;
  gateway_runtime_decref_objects:forall before world object result after next observed,
    gateway_objects_ready(python world)(objects world)before ->
    (0<python_native_strong(python world)object)%nat ->gateway_destructible(objects world)object ->
    gateway_object_operation backend gateway_api_decref[object]before world result after next observed ->
    gateway_reference_return(python world)(objects world)before object(python next)(objects next)after
}.

Lemma gateway_reachable_trans heap first middle last :
  gateway_object_reachable heap first middle ->gateway_object_reachable heap middle last ->
  gateway_object_reachable heap first last.
Proof.
  intros FIRST LAST;induction LAST;[exact FIRST|]. eapply gateway_reachable_child;eassumption.
Qed.

Lemma gateway_private_reachable heap root child :
  gateway_private_tree heap root ->gateway_object_reachable heap root child ->gateway_private_tree heap child.
Proof. intros PRIVATE REACHED object LATER;apply PRIVATE;eapply gateway_reachable_trans;eassumption. Qed.

Theorem gateway_private_tree_frame python heap next next_heap root :
  gateway_private_tree heap root ->gateway_rooted python heap root ->gateway_rooted next next_heap root ->
  gateway_objects_frame python heap next next_heap[] ->gateway_object_privacy_frame python heap next next_heap[] ->
  forall object,gateway_object_reachable heap root object ->
    gateway_rooted python heap object /\gateway_rooted next next_heap object /\
    (forall value,gateway_object_values heap object=Some value ->gateway_object_values next_heap object=Some value) /\
    gateway_object_private next_heap object=true.
Proof.
  intros PRIVATE ROOT NEXT FRAME PRIVACY object REACHED;induction REACHED.
  - split;[exact ROOT|]. split;[exact NEXT|]. split.
    + intros value LOOK;eapply FRAME;[exact ROOT|exact NEXT|apply PRIVATE;constructor|intro BAD;inversion BAD|exact LOOK].
    + eapply PRIVACY;[exact ROOT|exact NEXT|apply PRIVATE;constructor|intro BAD;inversion BAD].
  - destruct IHREACHED as[OLD_PARENT[NEW_PARENT[VALUES PARENT_PRIVATE]]].
    assert(OLD_CHILD:gateway_rooted python heap child)by(eapply gateway_child_root;eassumption).
    assert(NEW_CHILD:gateway_rooted next next_heap child).
    { eapply gateway_child_root;[exact NEW_PARENT|apply VALUES;exact H|exact H0]. }
    split;[exact OLD_CHILD|]. split;[exact NEW_CHILD|]. split.
    + intros actual LOOK;eapply FRAME;[exact OLD_CHILD|exact NEW_CHILD| |intro BAD;inversion BAD|exact LOOK].
      apply PRIVATE;eapply gateway_reachable_child;eassumption.
    + eapply PRIVACY;[exact OLD_CHILD|exact NEW_CHILD| |intro BAD;inversion BAD].
      apply PRIVATE;eapply gateway_reachable_child;eassumption.
Qed.

Theorem gateway_private_tree_reachable_back python heap next next_heap root :
  gateway_private_tree heap root ->gateway_destructible heap root ->
  gateway_rooted python heap root ->gateway_rooted next next_heap root ->
  gateway_objects_frame python heap next next_heap[] ->gateway_object_privacy_frame python heap next next_heap[] ->
  forall object,gateway_object_reachable next_heap root object ->gateway_object_reachable heap root object.
Proof.
  intros PRIVATE DESTRUCTIBLE ROOT NEXT FRAME PRIVACY object REACHED;induction REACHED.
  - constructor.
  - destruct(DESTRUCTIBLE parent IHREACHED)as[old_value[kind[LOOKUP[KIND SAFE]]]].
    destruct(gateway_private_tree_frame python heap next next_heap root PRIVATE ROOT NEXT FRAME PRIVACY
      parent IHREACHED)as[_[_[VALUES OWNED]]].
    assert(SAME:old_value=value)by(pose proof(VALUES old_value LOOKUP);congruence);subst old_value.
    eapply gateway_reachable_child;eassumption.
Qed.

Theorem gateway_private_tree_preserved python heap next next_heap root :
  gateway_private_tree heap root ->gateway_destructible heap root ->
  gateway_rooted python heap root ->gateway_rooted next next_heap root ->
  gateway_objects_frame python heap next next_heap[] ->gateway_object_privacy_frame python heap next next_heap[] ->
  gateway_private_tree next_heap root /\gateway_destructible next_heap root.
Proof.
  intros PRIVATE DESTRUCTIBLE ROOT NEXT FRAME PRIVACY.
  assert(BACK:forall object,gateway_object_reachable next_heap root object ->gateway_object_reachable heap root object).
  { eapply gateway_private_tree_reachable_back;eassumption. }
  split;intros object REACHED.
  - destruct(gateway_private_tree_frame python heap next next_heap root PRIVATE ROOT NEXT FRAME PRIVACY
      object(BACK object REACHED))as[_[_[_ OWNED]]];exact OWNED.
  - destruct(DESTRUCTIBLE object(BACK object REACHED))as[value[kind[LOOKUP[KIND SAFE]]]].
    destruct(gateway_private_tree_frame python heap next next_heap root PRIVATE ROOT NEXT FRAME PRIVACY
      object(BACK object REACHED))as[_[_[VALUES OWNED]]].
    exists value,kind;split;[apply VALUES;exact LOOKUP|]. split;assumption.
Qed.

Theorem gateway_reference_keeps_independent_tree python heap before consumed next next_heap after root :
  gateway_reference_return python heap before consumed next next_heap after ->root<>consumed ->
  (0<python_native_strong python root)%nat ->gateway_private_tree heap root ->
  forall object,gateway_object_reachable heap root object ->
    gateway_rooted next next_heap object /\
    (forall value,gateway_object_values heap object=Some value ->gateway_object_values next_heap object=Some value) /\
    gateway_object_private next_heap object=true.
Proof.
  intros RETURN DIFFERENT OWNED PRIVATE object REACHABLE.
  assert(NEXT_OWNED:(0<python_native_strong next root)%nat).
  { rewrite(gateway_reference_others _ _ _ _ _ _ _ RETURN root)by
      (intros[MEMBER|MEMBER];[congruence|contradiction]);exact OWNED. }
  destruct(gateway_private_tree_frame python heap next next_heap root PRIVATE
    (gateway_direct_root _ _ _ OWNED)(gateway_direct_root _ _ _ NEXT_OWNED)
    (gateway_reference_values _ _ _ _ _ _ _ RETURN)(gateway_reference_privacy _ _ _ _ _ _ _ RETURN)
    object REACHABLE)as[_[ROOTED[VALUE PRIVACY]]].
  split;[exact ROOTED|]. split;assumption.
Qed.

Definition gateway_mutable_container value :Prop:=
  match value with gateway_list_object _|gateway_dict_object _=>True|_=>False end.

(* Mutable containers are fresh even when an immutable constructor returns a
   cached scalar. The actual reference-release target therefore cannot be its parent. *)
Theorem gateway_constructor_avoids_live_container python heap before result next next_heap after value parent old_value :
  gateway_constructor_return python heap before result next next_heap after value ->
  gateway_objects_ready python heap before ->gateway_rooted python heap parent ->
  gateway_object_values heap parent=Some old_value ->gateway_mutable_container old_value ->result<>parent.
Proof.
  intros RETURN READY ROOT LOOKUP MUTABLE SAME;subst result.
  pose proof(gateway_constructor_alias _ _ _ _ _ _ _ _ RETURN ROOT)as ALIAS.
  assert(VALUE:value=old_value)by congruence;subst value.
  pose proof(gateway_constructor_fresh_container _ _ _ _ _ _ _ _ RETURN)as FRESH.
  destruct READY as[[WORLD_VALID[ROOTS REST]]CLEAR].
  destruct(ROOTS parent ROOT)as[STRONG DESCRIBED].
  destruct old_value;cbn in MUTABLE,FRESH;try contradiction;lia.
Qed.
