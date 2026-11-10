(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Typed parser and writer trees admit only their actual scalar tags. *)
From Stdlib Require Import List.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayImport GatewayValue GatewayCanonicalBytes.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope nat_scope.

Definition gateway_canonical_scalar_tag tag : Prop := In tag [3; 4; 5; 6; 9].

Inductive gateway_canonical_subject : LeanCage_Host_GatewayResponseCode_Subject -> Prop :=
| gateway_canonical_null : gateway_canonical_subject
    (LeanCage_Host_GatewayResponseCode_Subject_value LeanCage_Host_GatewayResponseCode_Value_null)
| gateway_canonical_boolean : forall flag, gateway_canonical_subject
    (LeanCage_Host_GatewayResponseCode_Subject_value (LeanCage_Host_GatewayResponseCode_Value_boolean flag))
| gateway_canonical_scalar : forall tag payload, gateway_canonical_scalar_tag (nat_of_Nat tag) ->
    gateway_canonical_subject (LeanCage_Host_GatewayResponseCode_Subject_value
      (LeanCage_Host_GatewayResponseCode_Value_scalar tag payload))
| gateway_canonical_array : forall values,
    gateway_canonical_subject (LeanCage_Host_GatewayResponseCode_Subject_values values) ->
    gateway_canonical_subject (LeanCage_Host_GatewayResponseCode_Subject_value
      (LeanCage_Host_GatewayResponseCode_Value_array values))
| gateway_canonical_object : forall fields,
    gateway_canonical_subject (LeanCage_Host_GatewayResponseCode_Subject_fields fields) ->
    gateway_canonical_subject (LeanCage_Host_GatewayResponseCode_Subject_value
      (LeanCage_Host_GatewayResponseCode_Value_object fields))
| gateway_canonical_values_nil : gateway_canonical_subject
    (LeanCage_Host_GatewayResponseCode_Subject_values (List_nil_inst1 _))
| gateway_canonical_values_cons : forall value values,
    gateway_canonical_subject (LeanCage_Host_GatewayResponseCode_Subject_value value) ->
    gateway_canonical_subject (LeanCage_Host_GatewayResponseCode_Subject_values values) ->
    gateway_canonical_subject (LeanCage_Host_GatewayResponseCode_Subject_values (List_cons_inst1 _ value values))
| gateway_canonical_fields_nil : gateway_canonical_subject
    (LeanCage_Host_GatewayResponseCode_Subject_fields (List_nil_inst1 _))
| gateway_canonical_fields_cons : forall key value fields,
    gateway_canonical_subject (LeanCage_Host_GatewayResponseCode_Subject_value key) ->
    gateway_canonical_subject (LeanCage_Host_GatewayResponseCode_Subject_value value) ->
    gateway_canonical_subject (LeanCage_Host_GatewayResponseCode_Subject_fields fields) ->
    gateway_canonical_subject (LeanCage_Host_GatewayResponseCode_Subject_fields
      (List_cons_inst1 _ (Prod_mk_inst3 _ _ key value) fields)).

Lemma gateway_scalar_semantics_canonical decimal_float tag payload value :
  gateway_scalar_semantics decimal_float tag payload value -> gateway_canonical_scalar_tag tag.
Proof.
  intro SEMANTICS; inversion SEMANTICS; subst; unfold gateway_canonical_scalar_tag; simpl; tauto.
Qed.

Fixpoint gateway_heap_value_canonical decimal_float heap object wire
    (value : gateway_value_heap decimal_float heap object wire) {struct value} :
    gateway_canonical_subject (LeanCage_Host_GatewayResponseCode_Subject_value wire)
with gateway_heap_array_canonical decimal_float heap objects values
    (array : gateway_array_heap decimal_float heap objects values) {struct array} :
    gateway_canonical_subject (LeanCage_Host_GatewayResponseCode_Subject_values (gateway_wire_values values))
with gateway_heap_dictionary_canonical decimal_float heap fields values
    (dictionary : gateway_dictionary_heap decimal_float heap fields values) {struct dictionary} :
    gateway_canonical_subject (LeanCage_Host_GatewayResponseCode_Subject_fields (gateway_wire_fields values)).
Proof.
  - destruct value.
    + constructor.
    + constructor.
    + unfold gateway_wire_scalar; constructor; rewrite nat2Natid.
      eapply gateway_scalar_semantics_canonical; eassumption.
    + constructor; eapply gateway_heap_array_canonical; eassumption.
    + constructor; eapply gateway_heap_dictionary_canonical; eassumption.
  - destruct array; cbn [gateway_wire_values].
    + constructor.
    + constructor; [eapply gateway_heap_value_canonical |eapply gateway_heap_array_canonical]; eassumption.
  - destruct dictionary; cbn [gateway_wire_fields].
    + constructor.
    + constructor; [eapply gateway_heap_value_canonical |eapply gateway_heap_value_canonical |
        eapply gateway_heap_dictionary_canonical]; eassumption.
Defined.
