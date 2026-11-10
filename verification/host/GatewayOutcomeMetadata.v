(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Output presentation preserves the original managed metadata subtree. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue GatewayValueFrame
  GatewayValueOwnership GatewayContainerGraph GatewayPresentationRuntime GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceThreads.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition gateway_outcome_output_name:list Z:=[111;117;116;112;117;116].
Definition gateway_outcome_json_name:list Z:=[106;115;111;110].
Fixpoint gateway_outcome_replace text pointer(fields:list gateway_dictionary_entry):list gateway_dictionary_entry:=
  match fields with
  |[]=>[]
  |field::rest=>
    (if list_eq_dec Z.eq_dec(gateway_dictionary_text field)text then
      {|gateway_dictionary_key:=gateway_dictionary_key field;gateway_dictionary_text:=gateway_dictionary_text field;
        gateway_dictionary_value:=pointer|}else field)::gateway_outcome_replace text pointer rest
  end.

Lemma gateway_outcome_replace_keys text pointer fields:
  map gateway_dictionary_text(gateway_outcome_replace text pointer fields)=map gateway_dictionary_text fields.
Proof. induction fields as[|field rest IH];cbn;[reflexivity|];destruct list_eq_dec;cbn;rewrite IH;reflexivity. Qed.

Theorem gateway_outcome_replace_other text query pointer fields:
  query<>text->gateway_dictionary_lookup query(gateway_outcome_replace text pointer fields)=gateway_dictionary_lookup query fields.
Proof.
  intro DIFFERENT;induction fields as[|field rest IH];[reflexivity|].
  unfold gateway_dictionary_lookup in *;cbn[gateway_outcome_replace find].
  destruct(list_eq_dec Z.eq_dec(gateway_dictionary_text field)text)as[SAME|OTHER];cbn[gateway_dictionary_text].
  - destruct(list_eq_dec Z.eq_dec(gateway_dictionary_text field)query)as[QUERY|NOT_QUERY];[congruence|exact IH].
  - destruct(list_eq_dec Z.eq_dec(gateway_dictionary_text field)query);[reflexivity|exact IH].
Qed.

Record gateway_outcome_update_return {World}(python:World->python_world)(objects:World->gateway_object_heap)
    (storage:World->block->Prop)(protected:block->Z->Prop)dictionary fields value before world after next:Prop:={
  gateway_outcome_update_ready:gateway_objects_ready(python next)(objects next)after;
  gateway_outcome_update_fields:gateway_object_values(objects next)dictionary=
    Some(gateway_dict_object(gateway_outcome_replace gateway_outcome_output_name value fields));
  gateway_outcome_update_private:gateway_object_private(objects next)dictionary=true;
  gateway_outcome_update_counts:gateway_native_references_frame(python world)(python next)[];
  gateway_outcome_update_values:gateway_objects_frame(python world)(objects world)(python next)(objects next)[dictionary];
  gateway_outcome_update_privacy:gateway_object_privacy_frame(python world)(objects world)(python next)(objects next)[dictionary];
  gateway_outcome_update_memory:Mem.unchanged_on protected before after;
  gateway_outcome_update_storage:forall object position,protected object position->storage next object
}.

(* Only an existing output field in the still-private copy is replaced. Its old
   value is an immutable constructor value; the new callback result is arbitrary. *)
Record gateway_outcome_update_runtime {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(objects:World->gateway_object_heap)(storage:World->block->Prop):Prop:={
  gateway_outcome_update_operation:forall dictionary fields field value name before world after next observed protected,
    gateway_objects_ready(python world)(objects world)before->
    gateway_presentation_owned_region storage world before protected->
    (0<python_native_strong(python world)dictionary)%nat->
    gateway_object_values(objects world)dictionary=Some(gateway_dict_object fields)->
    gateway_object_private(objects world)dictionary=true->
    gateway_dictionary_lookup gateway_outcome_output_name fields=Some field->
    gateway_presentation_immutable(objects world)(gateway_dictionary_value field)->
    python_live(python world)value->(0<python_native_strong(python world)value)%nat->
    gateway_object_name before name gateway_outcome_output_name->
    gateway_object_operation backend gateway_api_dict_set_string[dictionary;name;value]
      before world(Vint Int.zero)after next observed->
    gateway_outcome_update_return python objects storage protected dictionary fields value before world after next
}.

Lemma gateway_outcome_except_graph python heap next next_heap root excluded:
  gateway_rooted python heap root->gateway_rooted next next_heap root->gateway_private_tree heap root->
  ~gateway_object_reachable heap root excluded->
  gateway_objects_frame python heap next next_heap[excluded]->
  gateway_object_privacy_frame python heap next next_heap[excluded]->gateway_graph_region_frame heap next_heap root.
Proof.
  intros ROOT NEXT PRIVATE OUTSIDE VALUES PRIVACY object REACHED.
  assert(REGION:forall pointer,gateway_object_reachable heap root pointer->
    gateway_rooted next next_heap pointer /\
    (forall value,gateway_object_values heap pointer=Some value->gateway_object_values next_heap pointer=Some value) /\
    gateway_object_private next_heap pointer=true).
  { intros pointer REACH;induction REACH.
    - assert(DIFFERENT:root<>excluded)by(intro SAME;subst root;apply OUTSIDE;constructor).
      split;[exact NEXT|]. split.
      + intros old LOOKUP;apply VALUES;[exact ROOT|exact NEXT|apply PRIVATE;constructor|
          intros[SAME|EMPTY];[congruence|contradiction]|exact LOOKUP].
      + apply PRIVACY;[exact ROOT|exact NEXT|apply PRIVATE;constructor|intros[SAME|EMPTY];[congruence|contradiction]].
    - destruct IHREACH as[PARENT[PARENT_VALUE PARENT_PRIVATE]].
      assert(OLD:gateway_rooted python heap child).
      { eapply gateway_child_root;[eapply gateway_reachable_rooted;[exact ROOT|exact REACH]|exact H|exact H0]. }
      assert(NEW:gateway_rooted next next_heap child).
      { eapply gateway_child_root;[exact PARENT|apply PARENT_VALUE;exact H|exact H0]. }
      assert(CHILD:gateway_object_reachable heap root child)by(eapply gateway_reachable_child;eassumption).
      assert(DIFFERENT:child<>excluded)by(intro SAME;subst child;apply OUTSIDE;exact CHILD).
      split;[exact NEW|]. split.
      + intros old LOOKUP;apply VALUES;[exact OLD|exact NEW|apply PRIVATE;exact CHILD|
          intros[SAME|EMPTY];[congruence|contradiction]|exact LOOKUP].
      + apply PRIVACY;[exact OLD|exact NEW|apply PRIVATE;exact CHILD|intros[SAME|EMPTY];[congruence|contradiction]]. }
  exact(proj2(REGION object REACHED)).
Qed.

Theorem gateway_actual_output_update_keeps_metadata {World Event}(backend:gateway_backend World Event)
    python objects storage(update:gateway_outcome_update_runtime backend python objects storage)
    dictionary fields output_field value name metadata_field metadata wire decimal_float before world after next observed protected:
  gateway_objects_ready(python world)(objects world)before->
  gateway_presentation_owned_region storage world before protected->
  (0<python_native_strong(python world)dictionary)%nat->
  gateway_object_values(objects world)dictionary=Some(gateway_dict_object fields)->
  gateway_object_private(objects world)dictionary=true->
  gateway_dictionary_lookup gateway_outcome_output_name fields=Some output_field->
  gateway_presentation_immutable(objects world)(gateway_dictionary_value output_field)->
  python_live(python world)value->(0<python_native_strong(python world)value)%nat->
  gateway_object_name before name gateway_outcome_output_name->
  gateway_dictionary_lookup gateway_outcome_json_name fields=Some metadata_field->
  gateway_dictionary_value metadata_field=metadata->gateway_private_tree(objects world)metadata->
  gateway_destructible(objects world)metadata->gateway_value_heap decimal_float(objects world)metadata wire->
  ~gateway_object_reachable(objects world)metadata dictionary->
  gateway_object_operation backend gateway_api_dict_set_string[dictionary;name;value]
    before world(Vint Int.zero)after next observed->
  gateway_outcome_update_return python objects storage protected dictionary fields value before world after next /\
  gateway_dictionary_lookup gateway_outcome_json_name(gateway_outcome_replace gateway_outcome_output_name value fields)=Some metadata_field /\
  gateway_rooted(python next)(objects next)metadata /\
  gateway_private_tree(objects next)metadata /\gateway_destructible(objects next)metadata /\
  gateway_value_heap decimal_float(objects next)metadata wire /\
  gateway_graph_region_frame(objects world)(objects next)metadata.
Proof.
  intros READY STORAGE OWNED FIELDS PRIVATE OUTPUT IMMUTABLE LIVE CREDIT NAME METADATA META_VALUE META_PRIVATE META_DESTROY WIRE OUTSIDE OPERATION.
  pose proof(gateway_outcome_update_operation backend python objects storage update dictionary fields output_field value name before world after next observed
    protected READY STORAGE OWNED FIELDS PRIVATE OUTPUT IMMUTABLE LIVE CREDIT NAME OPERATION)as EFFECT.
  assert(LOOKUP:gateway_dictionary_lookup gateway_outcome_json_name(gateway_outcome_replace gateway_outcome_output_name value fields)=Some metadata_field).
  { rewrite gateway_outcome_replace_other;[exact METADATA|discriminate]. }
  assert(OLD_ROOT:gateway_rooted(python world)(objects world)metadata).
  { eapply gateway_child_root;[constructor;exact OWNED|exact FIELDS|].
    unfold gateway_object_children,gateway_dictionary_children;apply in_flat_map;exists metadata_field;split;
      [exact(proj1(gateway_dictionary_lookup_member _ _ _ METADATA))|rewrite META_VALUE;right;left;reflexivity]. }
  assert(NEXT_ROOT:gateway_rooted(python next)(objects next)metadata).
  { eapply gateway_child_root.
    - constructor;rewrite(gateway_outcome_update_counts _ _ _ _ _ _ _ _ _ _ _ EFFECT dictionary)
        by(intros EMPTY;inversion EMPTY);exact OWNED.
    - exact(gateway_outcome_update_fields _ _ _ _ _ _ _ _ _ _ _ EFFECT).
    - unfold gateway_object_children,gateway_dictionary_children;apply in_flat_map;exists metadata_field;split;
        [exact(proj1(gateway_dictionary_lookup_member _ _ _ LOOKUP))|rewrite META_VALUE;right;left;reflexivity]. }
  pose proof(gateway_outcome_except_graph _ _ _ _ _ _ OLD_ROOT NEXT_ROOT META_PRIVATE OUTSIDE
    (gateway_outcome_update_values _ _ _ _ _ _ _ _ _ _ _ EFFECT)
    (gateway_outcome_update_privacy _ _ _ _ _ _ _ _ _ _ _ EFFECT))as FRAME.
  destruct(gateway_graph_frame_tree _ _ _ META_DESTROY FRAME)as[AFTER_PRIVATE AFTER_DESTROY].
  split;[exact EFFECT|]. split;[exact LOOKUP|]. split;[exact NEXT_ROOT|]. split;[exact AFTER_PRIVATE|].
  split;[exact AFTER_DESTROY|]. split;[eapply gateway_graph_frame_value;eassumption|exact FRAME].
Qed.

Theorem gateway_outcome_copy_not_in_original python heap memory original copy next next_heap after fields:
  gateway_objects_ready python heap memory->gateway_rooted python heap original->
  gateway_constructor_return python heap memory copy next next_heap after(gateway_dict_object fields)->
  ~gateway_object_reachable heap original copy.
Proof.
  intros READY ROOT RETURN REACHED.
  assert(COPY_ROOT:gateway_rooted python heap copy)by(eapply gateway_reachable_rooted;eassumption).
  pose proof(proj1(proj2(proj1 READY))copy COPY_ROOT)as[POSITIVE VALUE].
  pose proof(gateway_constructor_fresh_container _ _ _ _ _ _ _ _ RETURN)as FRESH;cbn in FRESH;lia.
Qed.

Record gateway_outcome_metadata_view {World}(python:World->python_world)(objects:World->gateway_object_heap)
    decimal_float dictionary fields metadata_field metadata wire world:Prop:={
  gateway_outcome_view_owner:(0<python_native_strong(python world)dictionary)%nat;
  gateway_outcome_view_fields:gateway_object_values(objects world)dictionary=Some(gateway_dict_object fields);
  gateway_outcome_view_private:gateway_object_private(objects world)dictionary=true;
  gateway_outcome_view_metadata:gateway_dictionary_lookup gateway_outcome_json_name fields=Some metadata_field;
  gateway_outcome_view_value:gateway_dictionary_value metadata_field=metadata;
  gateway_outcome_view_tree:gateway_private_tree(objects world)metadata;
  gateway_outcome_view_destructible:gateway_destructible(objects world)metadata;
  gateway_outcome_view_wire:gateway_value_heap decimal_float(objects world)metadata wire
}.

Lemma gateway_outcome_view_metadata_rooted {World}python objects decimal_float dictionary fields metadata_field metadata wire world:
  @gateway_outcome_metadata_view World python objects decimal_float dictionary fields metadata_field metadata wire world->
  gateway_rooted(python world)(objects world)metadata.
Proof.
  intro VIEW;eapply gateway_child_root.
  - constructor;exact(gateway_outcome_view_owner _ _ _ _ _ _ _ _ _ VIEW).
  - exact(gateway_outcome_view_fields _ _ _ _ _ _ _ _ _ VIEW).
  - unfold gateway_object_children,gateway_dictionary_children;apply in_flat_map;exists metadata_field;split.
    + exact(proj1(gateway_dictionary_lookup_member _ _ _(gateway_outcome_view_metadata _ _ _ _ _ _ _ _ _ VIEW))).
    + rewrite(gateway_outcome_view_value _ _ _ _ _ _ _ _ _ VIEW);right;left;reflexivity.
Qed.

Theorem gateway_outcome_metadata_view_kept {World}python objects decimal_float dictionary fields metadata_field metadata wire world next:
  @gateway_outcome_metadata_view World python objects decimal_float dictionary fields metadata_field metadata wire world->
  (0<python_native_strong(python next)dictionary)%nat->
  gateway_objects_frame(python world)(objects world)(python next)(objects next)[]->
  gateway_object_privacy_frame(python world)(objects world)(python next)(objects next)[]->
  gateway_outcome_metadata_view python objects decimal_float dictionary fields metadata_field metadata wire next.
Proof.
  intros VIEW OWNED VALUES PRIVACY.
  assert(ROOT:gateway_rooted(python world)(objects world)dictionary)
    by(constructor;exact(gateway_outcome_view_owner _ _ _ _ _ _ _ _ _ VIEW)).
  assert(NEXT_ROOT:gateway_rooted(python next)(objects next)dictionary)by(constructor;exact OWNED).
  assert(FIELDS:gateway_object_values(objects next)dictionary=Some(gateway_dict_object fields)).
  { eapply VALUES;
      [exact ROOT|exact NEXT_ROOT|exact(gateway_outcome_view_private _ _ _ _ _ _ _ _ _ VIEW)|
       intros EMPTY;inversion EMPTY|exact(gateway_outcome_view_fields _ _ _ _ _ _ _ _ _ VIEW)]. }
  assert(PRIVATE:gateway_object_private(objects next)dictionary=true).
  { eapply PRIVACY;
      [exact ROOT|exact NEXT_ROOT|exact(gateway_outcome_view_private _ _ _ _ _ _ _ _ _ VIEW)|intros EMPTY;inversion EMPTY]. }
  assert(OLD_METADATA:gateway_rooted(python world)(objects world)metadata)by(eapply gateway_outcome_view_metadata_rooted;exact VIEW).
  assert(NEXT_METADATA:gateway_rooted(python next)(objects next)metadata).
  { eapply gateway_child_root;[exact NEXT_ROOT|exact FIELDS|].
    unfold gateway_object_children,gateway_dictionary_children;apply in_flat_map;exists metadata_field;split.
    - exact(proj1(gateway_dictionary_lookup_member _ _ _(gateway_outcome_view_metadata _ _ _ _ _ _ _ _ _ VIEW))).
    - rewrite(gateway_outcome_view_value _ _ _ _ _ _ _ _ _ VIEW);right;left;reflexivity. }
  destruct(gateway_private_tree_preserved _ _ _ _ _(gateway_outcome_view_tree _ _ _ _ _ _ _ _ _ VIEW)
    (gateway_outcome_view_destructible _ _ _ _ _ _ _ _ _ VIEW)OLD_METADATA NEXT_METADATA
    VALUES
    PRIVACY)as[META_PRIVATE META_DESTROY].
  constructor;try assumption.
  - exact(gateway_outcome_view_metadata _ _ _ _ _ _ _ _ _ VIEW).
  - exact(gateway_outcome_view_value _ _ _ _ _ _ _ _ _ VIEW).
  - eapply gateway_value_heap_retained;
      [exact(gateway_outcome_view_wire _ _ _ _ _ _ _ _ _ VIEW)|exact(gateway_outcome_view_tree _ _ _ _ _ _ _ _ _ VIEW)|
       exact OLD_METADATA|exact NEXT_METADATA|exact VALUES|
       exact PRIVACY].
Qed.

Theorem gateway_outcome_metadata_view_frame {World}python objects decimal_float dictionary fields metadata_field metadata wire world next:
  @gateway_outcome_metadata_view World python objects decimal_float dictionary fields metadata_field metadata wire world->
  GatewayReferenceThreads.gateway_reference_thread_effect python objects world next->
  gateway_outcome_metadata_view python objects decimal_float dictionary fields metadata_field metadata wire next.
Proof.
  intros VIEW EFFECT;eapply gateway_outcome_metadata_view_kept;[exact VIEW| | |].
  - pose proof(gateway_outcome_view_owner _ _ _ _ _ _ _ _ _ VIEW).
    pose proof(GatewayReferenceThreads.gateway_reference_thread_counts _ _ _ _ EFFECT dictionary);lia.
  - exact(GatewayReferenceThreads.gateway_reference_thread_values _ _ _ _ EFFECT).
  - exact(GatewayReferenceThreads.gateway_reference_thread_privacy _ _ _ _ EFFECT).
Qed.
