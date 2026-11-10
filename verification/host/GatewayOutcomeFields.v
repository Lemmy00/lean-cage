(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The returned fields retain received values beside the observed Path presentation. *)
From Stdlib Require Import List Lia.
From compcert Require Import Values.
From HostGateway Require Import GatewayPython GatewayObjects GatewayReferences GatewayValue GatewayValueFrame GatewayValueOwnership
  GatewayContainerGraph GatewayOutcomeMetadata GatewayReferenceThreads.
Import ListNotations.
Local Close Scope lean_scope.

Definition gateway_outcome_child_view decimal_float heap pointer wire:Prop:=
  gateway_private_tree heap pointer /\gateway_destructible heap pointer /\gateway_value_heap decimal_float heap pointer wire.
Definition gateway_outcome_field_view decimal_float heap(field:gateway_dictionary_entry)(wire:gateway_wire_value*gateway_wire_value):Prop:=
  gateway_outcome_child_view decimal_float heap(gateway_dictionary_key field)(fst wire) /\
  (gateway_dictionary_text field=gateway_outcome_output_name \/
    gateway_outcome_child_view decimal_float heap(gateway_dictionary_value field)(snd wire)).

Lemma gateway_outcome_child_view_frame decimal_float python heap next next_heap pointer wire:
  gateway_outcome_child_view decimal_float heap pointer wire->
  gateway_rooted python heap pointer->gateway_rooted next next_heap pointer->
  gateway_objects_frame python heap next next_heap[]->gateway_object_privacy_frame python heap next next_heap[]->
  gateway_outcome_child_view decimal_float next_heap pointer wire.
Proof.
  intros[PRIVATE[DESTROY VALUE]]ROOT NEXT VALUES PRIVACY.
  destruct(gateway_private_tree_preserved _ _ _ _ _ PRIVATE DESTROY ROOT NEXT VALUES PRIVACY)as[AFTER_PRIVATE AFTER_DESTROY].
  split;[exact AFTER_PRIVATE|]. split;[exact AFTER_DESTROY|]. eapply gateway_value_heap_retained;eassumption.
Qed.

Lemma gateway_outcome_field_views_frame decimal_float python heap next next_heap fields wires:
  Forall2(gateway_outcome_field_view decimal_float heap)fields wires->
  (forall field,In field fields->gateway_rooted python heap(gateway_dictionary_key field) /\
    gateway_rooted next next_heap(gateway_dictionary_key field) /\gateway_rooted python heap(gateway_dictionary_value field) /\
    gateway_rooted next next_heap(gateway_dictionary_value field))->
  gateway_objects_frame python heap next next_heap[]->gateway_object_privacy_frame python heap next next_heap[]->
  Forall2(gateway_outcome_field_view decimal_float next_heap)fields wires.
Proof.
  intros FIELDS;induction FIELDS;intros ROOTS VALUES PRIVACY;[constructor|].
  destruct(ROOTS x ltac:(left;reflexivity))as[KEY_OLD[KEY_NEXT[VALUE_OLD VALUE_NEXT]]].
  destruct H as[KEY[OUTPUT|VALUE]];constructor.
  - split;[eapply gateway_outcome_child_view_frame;eassumption|left;exact OUTPUT].
  - apply IHFIELDS;[intros field MEMBER;apply ROOTS;right;exact MEMBER|exact VALUES|exact PRIVACY].
  - split;[eapply gateway_outcome_child_view_frame;eassumption|right;eapply gateway_outcome_child_view_frame;eassumption].
  - apply IHFIELDS;[intros field MEMBER;apply ROOTS;right;exact MEMBER|exact VALUES|exact PRIVACY].
Qed.

Record gateway_outcome_fields_view {World}(python:World->python_world)(objects:World->gateway_object_heap)
    decimal_float dictionary fields wires world:Prop:={
  gateway_outcome_fields_owner:(0<python_native_strong(python world)dictionary)%nat;
  gateway_outcome_fields_value:gateway_object_values(objects world)dictionary=Some(gateway_dict_object fields);
  gateway_outcome_fields_private:gateway_object_private(objects world)dictionary=true;
  gateway_outcome_fields_received:Forall2(gateway_outcome_field_view decimal_float(objects world))fields wires
}.

Lemma gateway_outcome_dictionary_roots python heap dictionary fields:
  gateway_rooted python heap dictionary->gateway_object_values heap dictionary=Some(gateway_dict_object fields)->
  forall field,In field fields->gateway_rooted python heap(gateway_dictionary_key field) /\
    gateway_rooted python heap(gateway_dictionary_value field).
Proof.
  intros ROOT FIELDS field MEMBER;split;eapply gateway_child_root;[exact ROOT|exact FIELDS| |exact ROOT|exact FIELDS|].
  all:unfold gateway_object_children,gateway_dictionary_children;apply in_flat_map;exists field;split;[exact MEMBER|];cbn;auto.
Qed.

Theorem gateway_outcome_fields_view_kept {World}python objects decimal_float dictionary fields wires world next:
  @gateway_outcome_fields_view World python objects decimal_float dictionary fields wires world->
  (0<python_native_strong(python next)dictionary)%nat->
  gateway_objects_frame(python world)(objects world)(python next)(objects next)[]->
  gateway_object_privacy_frame(python world)(objects world)(python next)(objects next)[]->gateway_outcome_fields_view python objects decimal_float dictionary fields wires next.
Proof.
  intros VIEW OWNED VALUES PRIVACY.
  assert(ROOT:gateway_rooted(python world)(objects world)dictionary)by(constructor;exact(gateway_outcome_fields_owner _ _ _ _ _ _ _ VIEW)).
  assert(NEXT:gateway_rooted(python next)(objects next)dictionary)by(constructor;exact OWNED).
  assert(FIELDS:gateway_object_values(objects next)dictionary=Some(gateway_dict_object fields)).
  { eapply VALUES;[exact ROOT|exact NEXT|exact(gateway_outcome_fields_private _ _ _ _ _ _ _ VIEW)|
      intros EMPTY;inversion EMPTY|exact(gateway_outcome_fields_value _ _ _ _ _ _ _ VIEW)]. }
  constructor;[exact OWNED|exact FIELDS| |].
  - eapply PRIVACY;[exact ROOT|exact NEXT|exact(gateway_outcome_fields_private _ _ _ _ _ _ _ VIEW)|
      intros EMPTY;inversion EMPTY].
  - eapply gateway_outcome_field_views_frame;[exact(gateway_outcome_fields_received _ _ _ _ _ _ _ VIEW)| | |].
    + intros field MEMBER;destruct(gateway_outcome_dictionary_roots _ _ _ _ ROOT(gateway_outcome_fields_value _ _ _ _ _ _ _ VIEW)field MEMBER)as[KEY VALUE].
      destruct(gateway_outcome_dictionary_roots _ _ _ _ NEXT FIELDS field MEMBER)as[NEXT_KEY NEXT_VALUE];exact(conj KEY(conj NEXT_KEY(conj VALUE NEXT_VALUE))).
    + exact VALUES.
    + exact PRIVACY.
Qed.

Theorem gateway_outcome_fields_view_frame {World}python objects decimal_float dictionary fields wires world next:
  @gateway_outcome_fields_view World python objects decimal_float dictionary fields wires world->
  gateway_reference_thread_effect python objects world next->gateway_outcome_fields_view python objects decimal_float dictionary fields wires next.
Proof.
  intros VIEW EFFECT;eapply gateway_outcome_fields_view_kept;[exact VIEW| | |].
  - pose proof(gateway_outcome_fields_owner _ _ _ _ _ _ _ VIEW).
    pose proof(gateway_reference_thread_counts _ _ _ _ EFFECT dictionary);lia.
  - exact(gateway_reference_thread_values _ _ _ _ EFFECT).
  - exact(gateway_reference_thread_privacy _ _ _ _ EFFECT).
Qed.

Lemma gateway_outcome_child_subtree heap dictionary fields field pointer:
  gateway_object_values heap dictionary=Some(gateway_dict_object fields)->In field fields->
  (pointer=gateway_dictionary_key field \/pointer=gateway_dictionary_value field)->
  gateway_private_tree heap dictionary->gateway_destructible heap dictionary->
  gateway_private_tree heap pointer /\gateway_destructible heap pointer.
Proof.
  intros VALUE MEMBER WHICH PRIVATE DESTROY.
  assert(CHILD:gateway_object_reachable heap dictionary pointer).
  { eapply gateway_reachable_child;[constructor|exact VALUE|].
    unfold gateway_object_children,gateway_dictionary_children;apply in_flat_map;exists field;split;[exact MEMBER|].
    destruct WHICH as[SAME|SAME];subst pointer;cbn;auto. }
  split;intros object REACHED.
  - apply PRIVATE;eapply gateway_reachable_trans;eassumption.
  - apply DESTROY;eapply gateway_reachable_trans;eassumption.
Qed.

Theorem gateway_received_dictionary_field_views decimal_float heap dictionary fields wires:
  gateway_object_values heap dictionary=Some(gateway_dict_object fields)->gateway_private_tree heap dictionary->gateway_destructible heap dictionary->
  gateway_dictionary_heap decimal_float heap fields wires->Forall2(gateway_outcome_field_view decimal_float heap)fields wires.
Proof.
  intros VALUE PRIVATE DESTROY RECEIVED.
  assert(CHILDREN:forall field,In field fields->
    gateway_private_tree heap(gateway_dictionary_key field) /\gateway_destructible heap(gateway_dictionary_key field) /\
    gateway_private_tree heap(gateway_dictionary_value field) /\gateway_destructible heap(gateway_dictionary_value field)).
  { intros field MEMBER;destruct(gateway_outcome_child_subtree _ _ _ _ _ VALUE MEMBER ltac:(left;reflexivity)PRIVATE DESTROY)as[KEY KEY_SAFE].
    destruct(gateway_outcome_child_subtree _ _ _ _ _ VALUE MEMBER ltac:(right;reflexivity)PRIVATE DESTROY)as[ITEM ITEM_SAFE];tauto. }
  clear VALUE PRIVATE DESTROY;induction RECEIVED;[constructor|].
  destruct(CHILDREN field ltac:(left;reflexivity))as[KEY_PRIVATE[KEY_SAFE[ITEM_PRIVATE ITEM_SAFE]]].
  constructor.
  - split;[exact(conj KEY_PRIVATE(conj KEY_SAFE H))|right;exact(conj ITEM_PRIVATE(conj ITEM_SAFE H0))].
  - apply IHRECEIVED;intros child MEMBER;apply CHILDREN;right;exact MEMBER.
Qed.
