(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Native heap descriptions retain the shared wire tree and
   scalar bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Floats Values Memory.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayImport GatewayWordData GatewayWordReceipt GatewayObjects.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition gateway_wire_value :=LeanCage_Host_GatewayResponseCode_Value.
Definition gateway_wire_bytes bytes :=gateway_imported_nats(gateway_byte_naturals bytes).
Definition gateway_wire_scalar tag bytes :=
  LeanCage_Host_GatewayResponseCode_Value_scalar(Nat_of_nat tag)(gateway_wire_bytes bytes).
Fixpoint gateway_wire_values (values:list gateway_wire_value) :List_inst1 gateway_wire_value:=
  match values with[]=>List_nil_inst1 _|first::rest=>List_cons_inst1 _ first(gateway_wire_values rest)end.
Fixpoint gateway_wire_fields (fields:list(gateway_wire_value*gateway_wire_value))
    :List_inst1(Prod_inst3 gateway_wire_value gateway_wire_value):=
  match fields with
  |[]=>List_nil_inst1 _
  |(key,value)::rest=>List_cons_inst1 _ (Prod_mk_inst3 _ _ key value)(gateway_wire_fields rest)
  end.

Inductive gateway_json_sign :=gateway_json_positive|gateway_json_negative.
Definition gateway_json_signed sign value :Z:=
  match sign with gateway_json_positive=>value|gateway_json_negative=>-value end.
Definition gateway_json_sign_bytes sign :list Byte.int:=
  match sign with gateway_json_positive=>[]|gateway_json_negative=>[Byte.repr 45]end.
Definition gateway_json_digits bytes :Prop:=
  bytes<>[] /\Forall(fun byte=>48<=Byte.unsigned byte<=57)bytes.
Definition gateway_json_integer_part bytes :Prop:=
  bytes=[Byte.repr 48] \/exists first rest,bytes=first::rest /\49<=Byte.unsigned first<=57 /\
    Forall(fun byte=>48<=Byte.unsigned byte<=57)rest.
Inductive gateway_json_fraction :list Byte.int->Prop:=
| gateway_json_no_fraction:gateway_json_fraction[]
| gateway_json_fraction_digits:forall digits,gateway_json_digits digits ->
    gateway_json_fraction(Byte.repr 46::digits).
Inductive gateway_json_exponent :list Byte.int->Prop:=
| gateway_json_no_exponent:gateway_json_exponent[]
| gateway_json_exponent_digits:forall marker sign digits,
    (marker=Byte.repr 101 \/marker=Byte.repr 69) ->
    (sign=[] \/sign=[Byte.repr 43] \/sign=[Byte.repr 45]) ->gateway_json_digits digits ->
    gateway_json_exponent(marker::sign++digits).
Inductive gateway_json_number :list Byte.int->Prop:=
| gateway_json_number_parts:forall sign integer fraction exponent,
    gateway_json_integer_part integer ->gateway_json_fraction fraction ->gateway_json_exponent exponent ->
    gateway_json_number(gateway_json_sign_bytes sign++integer++fraction++exponent).

Definition gateway_json_float_marker bytes :Prop:=
  In(Byte.repr 46)bytes \/In(Byte.repr 69)bytes \/In(Byte.repr 101)bytes.

Inductive gateway_scalar_semantics (decimal_float:list Z->float->Prop)
    :nat->list Byte.int->gateway_object_value->Prop:=
| gateway_scalar_integer:forall bytes value,gateway_decimal bytes value ->
    gateway_scalar_semantics decimal_float 3 bytes(gateway_long_object value)
| gateway_scalar_unicode:forall bytes characters,gateway_utf8_text bytes characters ->
    gateway_scalar_semantics decimal_float 4 bytes(gateway_unicode_object characters)
| gateway_scalar_raw_bytes:forall bytes,gateway_scalar_semantics decimal_float 5 bytes(gateway_bytes_object bytes)
| gateway_scalar_filesystem:forall bytes characters,~In Byte.zero bytes ->gateway_filesystem_text bytes characters ->
    gateway_scalar_semantics decimal_float 6 bytes(gateway_unicode_object characters)
| gateway_scalar_json_integer:forall sign digits,
    gateway_json_integer_part digits ->
    gateway_scalar_semantics decimal_float 9(gateway_json_sign_bytes sign++digits)
      (gateway_long_object(gateway_json_signed sign(gateway_decimal_value digits)))
| gateway_scalar_json_float:forall bytes characters value,
    gateway_json_number bytes ->gateway_json_float_marker bytes ->
    gateway_utf8_text bytes characters ->decimal_float characters value ->
    gateway_scalar_semantics decimal_float 9 bytes(gateway_float_object value).

Inductive gateway_value_heap (decimal_float:list Z->float->Prop)(heap:gateway_object_heap)
    :Values.val->gateway_wire_value->Prop:=
| gateway_heap_null:forall object,gateway_object_values heap object=Some gateway_none_object ->
    gateway_value_heap decimal_float heap object LeanCage_Host_GatewayResponseCode_Value_null
| gateway_heap_boolean:forall object value,gateway_object_values heap object=Some(gateway_bool_object value) ->
    gateway_value_heap decimal_float heap object
      (LeanCage_Host_GatewayResponseCode_Value_boolean(if value then Bool_true else Bool_false))
| gateway_heap_scalar:forall object tag bytes value,
    gateway_object_values heap object=Some value ->gateway_scalar_semantics decimal_float tag bytes value ->
    gateway_value_heap decimal_float heap object(gateway_wire_scalar tag bytes)
| gateway_heap_array:forall object objects values,
    gateway_object_values heap object=Some(gateway_list_object objects) ->
    gateway_array_heap decimal_float heap objects values ->
    gateway_value_heap decimal_float heap object(LeanCage_Host_GatewayResponseCode_Value_array(gateway_wire_values values))
| gateway_heap_dictionary:forall object fields values,
    gateway_object_values heap object=Some(gateway_dict_object fields) ->
    gateway_dictionary_heap decimal_float heap fields values ->
    gateway_value_heap decimal_float heap object(LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields values))
with gateway_array_heap (decimal_float:list Z->float->Prop)(heap:gateway_object_heap)
    :list Values.val->list gateway_wire_value->Prop:=
| gateway_heap_array_nil:gateway_array_heap decimal_float heap[][]
| gateway_heap_array_cons:forall object value objects values,
    gateway_value_heap decimal_float heap object value ->gateway_array_heap decimal_float heap objects values ->
    gateway_array_heap decimal_float heap(object::objects)(value::values)
with gateway_dictionary_heap (decimal_float:list Z->float->Prop)(heap:gateway_object_heap)
    :list gateway_dictionary_entry->list(gateway_wire_value*gateway_wire_value)->Prop:=
| gateway_heap_dictionary_nil:gateway_dictionary_heap decimal_float heap[][]
| gateway_heap_dictionary_cons:forall field key value fields values,
    gateway_value_heap decimal_float heap(gateway_dictionary_key field)key ->
    gateway_value_heap decimal_float heap(gateway_dictionary_value field)value ->
    gateway_dictionary_heap decimal_float heap fields values ->
    gateway_dictionary_heap decimal_float heap(field::fields)((key,value)::values).

Theorem gateway_scalar_layout_is_builtin decimal_float tag bytes value :
  gateway_scalar_semantics decimal_float tag bytes value ->
  exists kind,gateway_object_kind value=Some kind /\
    (kind=gateway_long_kind \/kind=gateway_float_kind \/kind=gateway_unicode_kind \/kind=gateway_bytes_kind).
Proof. intro SCALAR;inversion SCALAR;subst;(eexists;split;[reflexivity|auto]). Qed.

Theorem gateway_constructed_scalar_describes_shared_value python heap memory result next next_heap after
    decimal_float api arguments tag bytes value :
  gateway_constructor_return python heap memory result next next_heap after value ->
  gateway_constructor_request decimal_float heap memory api arguments value ->
  gateway_scalar_semantics decimal_float tag bytes value ->
  gateway_value_heap decimal_float next_heap result(gateway_wire_scalar tag bytes).
Proof.
  intros RETURN REQUEST SCALAR;eapply gateway_heap_scalar;[|exact SCALAR].
  exact(gateway_constructor_value _ _ _ _ _ _ _ _ RETURN).
Qed.

Theorem gateway_heap_array_lengths decimal_float heap objects values :
  gateway_array_heap decimal_float heap objects values ->length objects=length values.
Proof. intro ARRAY;induction ARRAY;cbn;congruence. Qed.
Theorem gateway_heap_dictionary_lengths decimal_float heap fields values :
  gateway_dictionary_heap decimal_float heap fields values ->length fields=length values.
Proof. intro FIELDS;induction FIELDS;cbn;congruence. Qed.
