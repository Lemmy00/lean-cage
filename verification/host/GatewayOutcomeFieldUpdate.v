(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Output replacement retains every other received field without freezing presentation. *)
From Stdlib Require Import List Lia ZArith.
From compcert Require Import Integers Values Memory.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue GatewayValueFrame GatewayContainerGraph
  GatewayOutcomeMetadata GatewayPresentationRuntime GatewayOutcomeFields GatewayReferenceThreads.
Import ListNotations.
Local Close Scope lean_scope.

Definition gateway_outcome_replaced_field text value(field:gateway_dictionary_entry):gateway_dictionary_entry:=
  if list_eq_dec Z.eq_dec(gateway_dictionary_text field)text then
    {|gateway_dictionary_key:=gateway_dictionary_key field;gateway_dictionary_text:=gateway_dictionary_text field;
      gateway_dictionary_value:=value|}else field.

Lemma gateway_outcome_replace_map text value fields:
  gateway_outcome_replace text value fields=map(gateway_outcome_replaced_field text value)fields.
Proof. induction fields;cbn;[reflexivity|rewrite IHfields;reflexivity]. Qed.
Lemma gateway_outcome_replaced_key text value field:
  gateway_dictionary_key(gateway_outcome_replaced_field text value field)=gateway_dictionary_key field.
Proof. unfold gateway_outcome_replaced_field;destruct list_eq_dec;reflexivity. Qed.
Lemma gateway_outcome_replaced_text text value field:
  gateway_dictionary_text(gateway_outcome_replaced_field text value field)=gateway_dictionary_text field.
Proof. unfold gateway_outcome_replaced_field;destruct list_eq_dec;reflexivity. Qed.
Lemma gateway_outcome_replaced_other text value field:
  gateway_dictionary_text field<>text->gateway_outcome_replaced_field text value field=field.
Proof. intro OTHER;unfold gateway_outcome_replaced_field;destruct list_eq_dec;[contradiction|reflexivity]. Qed.

Lemma gateway_outcome_child_view_except decimal_float python heap next next_heap pointer wire excluded:
  gateway_outcome_child_view decimal_float heap pointer wire->gateway_rooted python heap pointer->gateway_rooted next next_heap pointer->
  ~gateway_object_reachable heap pointer excluded->
  gateway_objects_frame python heap next next_heap[excluded]->gateway_object_privacy_frame python heap next next_heap[excluded]->
  gateway_outcome_child_view decimal_float next_heap pointer wire.
Proof.
  intros[PRIVATE[DESTROY VALUE]]ROOT NEXT OUTSIDE VALUES PRIVACY.
  pose proof(gateway_outcome_except_graph _ _ _ _ _ _ ROOT NEXT PRIVATE OUTSIDE VALUES PRIVACY)as FRAME.
  destruct(gateway_graph_frame_tree _ _ _ DESTROY FRAME)as[AFTER_PRIVATE AFTER_DESTROY].
  split;[exact AFTER_PRIVATE|]. split;[exact AFTER_DESTROY|]. eapply gateway_graph_frame_value;eassumption.
Qed.

Lemma gateway_outcome_field_update_views decimal_float python heap next next_heap value excluded fields wires:
  Forall2(gateway_outcome_field_view decimal_float heap)fields wires->
  (forall field,In field fields->
    gateway_rooted python heap(gateway_dictionary_key field) /\
    gateway_rooted next next_heap(gateway_dictionary_key field) /\
    ~gateway_object_reachable heap(gateway_dictionary_key field)excluded /\
    (gateway_dictionary_text field=gateway_outcome_output_name \/
      gateway_rooted python heap(gateway_dictionary_value field) /\
      gateway_rooted next next_heap(gateway_dictionary_value field) /\
      ~gateway_object_reachable heap(gateway_dictionary_value field)excluded))->
  gateway_objects_frame python heap next next_heap[excluded]->gateway_object_privacy_frame python heap next next_heap[excluded]->
  Forall2(gateway_outcome_field_view decimal_float next_heap)
    (gateway_outcome_replace gateway_outcome_output_name value fields)wires.
Proof.
  intro FIELDS;induction FIELDS;intros ROOTS VALUES PRIVACY;[constructor|].
  rewrite gateway_outcome_replace_map;cbn[map];rewrite<-gateway_outcome_replace_map.
  destruct(ROOTS x ltac:(left;reflexivity))as[KEY_OLD[KEY_NEXT[KEY_OUTSIDE VALUE_ROOTS]]].
  destruct H as[KEY VALUE];constructor.
  - split.
    + rewrite gateway_outcome_replaced_key;eapply gateway_outcome_child_view_except;eassumption.
    + destruct(list_eq_dec Z.eq_dec(gateway_dictionary_text x)gateway_outcome_output_name)as[OUTPUT|OTHER].
      * left;rewrite gateway_outcome_replaced_text;exact OUTPUT.
      * rewrite gateway_outcome_replaced_other by exact OTHER.
        destruct VALUE as[IMPOSSIBLE|VALUE];[contradiction|].
        destruct VALUE_ROOTS as[IMPOSSIBLE|[OLD[NEXT OUTSIDE]]];[contradiction|].
        right;eapply gateway_outcome_child_view_except;eassumption.
  - apply IHFIELDS;[intros field MEMBER;apply ROOTS;right;exact MEMBER|exact VALUES|exact PRIVACY].
Qed.

Theorem gateway_actual_output_update_keeps_received_fields {World Event}(backend:gateway_backend World Event)
    python objects storage(update:gateway_outcome_update_runtime backend python objects storage)
    decimal_float dictionary fields wires output_field value name before world after next observed protected:
  gateway_objects_ready(python world)(objects world)before->gateway_presentation_owned_region storage world before protected->
  gateway_outcome_fields_view python objects decimal_float dictionary fields wires world->
  gateway_dictionary_lookup gateway_outcome_output_name fields=Some output_field->
  gateway_presentation_immutable(objects world)(gateway_dictionary_value output_field)->
  python_live(python world)value->(0<python_native_strong(python world)value)%nat->
  gateway_object_name before name gateway_outcome_output_name->
  (forall field,In field fields->~gateway_object_reachable(objects world)(gateway_dictionary_key field)dictionary /\
    (gateway_dictionary_text field=gateway_outcome_output_name \/
      ~gateway_object_reachable(objects world)(gateway_dictionary_value field)dictionary))->
  gateway_object_operation backend gateway_api_dict_set_string[dictionary;name;value]
    before world(Vint Int.zero)after next observed->
  gateway_outcome_update_return python objects storage protected dictionary fields value before world after next /\
  gateway_outcome_fields_view python objects decimal_float dictionary
    (gateway_outcome_replace gateway_outcome_output_name value fields)wires next.
Proof.
  intros READY STORAGE VIEW OUTPUT IMMUTABLE LIVE CREDIT NAME OUTSIDE OPERATION.
  pose proof(gateway_outcome_update_operation backend python objects storage update dictionary fields output_field value name before world after next observed
    protected READY STORAGE(gateway_outcome_fields_owner _ _ _ _ _ _ _ VIEW)(gateway_outcome_fields_value _ _ _ _ _ _ _ VIEW)
    (gateway_outcome_fields_private _ _ _ _ _ _ _ VIEW)OUTPUT IMMUTABLE LIVE CREDIT NAME OPERATION)as EFFECT.
  assert(OWNED:(0<python_native_strong(python next)dictionary)%nat).
  { rewrite(gateway_outcome_update_counts _ _ _ _ _ _ _ _ _ _ _ EFFECT dictionary)by(intros EMPTY;inversion EMPTY).
    exact(gateway_outcome_fields_owner _ _ _ _ _ _ _ VIEW). }
  assert(ROOT:gateway_rooted(python world)(objects world)dictionary)by(constructor;exact(gateway_outcome_fields_owner _ _ _ _ _ _ _ VIEW)).
  assert(NEXT:gateway_rooted(python next)(objects next)dictionary)by(constructor;exact OWNED).
  split;[exact EFFECT|]. constructor;[exact OWNED|exact(gateway_outcome_update_fields _ _ _ _ _ _ _ _ _ _ _ EFFECT)|
    exact(gateway_outcome_update_private _ _ _ _ _ _ _ _ _ _ _ EFFECT)|].
  eapply gateway_outcome_field_update_views;[exact(gateway_outcome_fields_received _ _ _ _ _ _ _ VIEW)| | |].
  - intros field MEMBER.
    destruct(gateway_outcome_dictionary_roots _ _ _ _ ROOT(gateway_outcome_fields_value _ _ _ _ _ _ _ VIEW)field MEMBER)as[KEY_OLD VALUE_OLD].
    assert(NEW_MEMBER:In(gateway_outcome_replaced_field gateway_outcome_output_name value field)
      (gateway_outcome_replace gateway_outcome_output_name value fields)).
    { rewrite gateway_outcome_replace_map;apply in_map;exact MEMBER. }
    destruct(gateway_outcome_dictionary_roots _ _ _ _ NEXT(gateway_outcome_update_fields _ _ _ _ _ _ _ _ _ _ _ EFFECT)
      _ NEW_MEMBER)as[KEY_NEXT VALUE_NEXT].
    rewrite gateway_outcome_replaced_key in KEY_NEXT.
    destruct(OUTSIDE field MEMBER)as[KEY_OUTSIDE[OUTPUT_FIELD|VALUE_OUTSIDE]].
    + exact(conj KEY_OLD(conj KEY_NEXT(conj KEY_OUTSIDE(or_introl OUTPUT_FIELD)))).
    + destruct(list_eq_dec Z.eq_dec(gateway_dictionary_text field)gateway_outcome_output_name)as[IS_OUTPUT|OTHER].
      * exact(conj KEY_OLD(conj KEY_NEXT(conj KEY_OUTSIDE(or_introl IS_OUTPUT)))).
      * rewrite gateway_outcome_replaced_other in VALUE_NEXT by exact OTHER.
        exact(conj KEY_OLD(conj KEY_NEXT(conj KEY_OUTSIDE(or_intror(conj VALUE_OLD(conj VALUE_NEXT VALUE_OUTSIDE)))))).
  - exact(gateway_outcome_update_values _ _ _ _ _ _ _ _ _ _ _ EFFECT).
  - exact(gateway_outcome_update_privacy _ _ _ _ _ _ _ _ _ _ _ EFFECT).
Qed.
