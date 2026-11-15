(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Iterator checks read the SAME actual borrowed outputs. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewayObjects GatewayDictionaryIteration.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_dictionary_next_output_loads fields position key value before after :
  position <> key -> position <> value -> key <> value ->
  (forall field, In field fields ->
    (exists object offset, gateway_dictionary_key field = Vptr object offset) /\
    (exists object offset, gateway_dictionary_value field = Vptr object offset)) ->
  gateway_dictionary_next_outputs fields position key value before (Vint Int.one) after ->
  exists field cursor,
    In field fields /\ 0 < Int64.signed cursor /\
    Mem.load Mint64 after position 0 = Some (Vlong cursor) /\
    Mem.load Mptr after key 0 = Some (gateway_dictionary_key field) /\
    Mem.load Mptr after value 0 = Some (gateway_dictionary_value field).
Proof.
  intros POSITION_KEY POSITION_VALUE KEY_VALUE POINTERS OUTPUT.
  inversion OUTPUT as [memory |memory after_position after_key final field cursor MEMBER RANGE STORE_POSITION STORE_KEY STORE_VALUE];
    subst; try discriminate.
  destruct (POINTERS field MEMBER) as [[key_object [key_offset KEY]] [value_object [value_offset VALUE]]].
  exists field, cursor; split; [exact MEMBER |split; [exact RANGE |split]].
  - erewrite Mem.load_store_other; [|exact STORE_VALUE |left; congruence].
    erewrite Mem.load_store_other; [|exact STORE_KEY |left; congruence].
    pose proof (Mem.load_store_same _ _ _ _ _ _ STORE_POSITION) as LOAD; exact LOAD.
  - split.
    + erewrite Mem.load_store_other; [|exact STORE_VALUE |left; exact KEY_VALUE].
      rewrite KEY in STORE_KEY |- *; exact (Mem.load_store_same _ _ _ _ _ _ STORE_KEY).
    + rewrite VALUE in STORE_VALUE |- *; exact (Mem.load_store_same _ _ _ _ _ _ STORE_VALUE).
Qed.

Theorem gateway_dictionary_field_pointer_outputs python heap memory dictionary fields :
  gateway_objects_ready python heap memory -> gateway_rooted python heap dictionary ->
  gateway_object_values heap dictionary = Some (gateway_dict_object fields) ->
  forall field, In field fields ->
    (exists object offset, gateway_dictionary_key field = Vptr object offset) /\
    (exists object offset, gateway_dictionary_value field = Vptr object offset).
Proof.
  intros [[VALID [LIVE [BYTES [DICT ADDRESS]]]] REST] ROOT FIELDS field MEMBER.
  assert (CHILDREN : forall pointer, In pointer [gateway_dictionary_key field; gateway_dictionary_value field] ->
    gateway_rooted python heap pointer).
  { intros pointer CHILD; eapply gateway_child_root; [exact ROOT |exact FIELDS |].
    unfold gateway_object_children, gateway_dictionary_children; apply in_flat_map; exists field; auto. }
  split.
  - destruct (ADDRESS (gateway_dictionary_key field) (CHILDREN _ ltac:(left; reflexivity))) as [object [offset [SAME POINTER]]]; eauto.
  - destruct (ADDRESS (gateway_dictionary_value field) (CHILDREN _ ltac:(right; left; reflexivity))) as [object [offset [SAME POINTER]]]; eauto.
Qed.
