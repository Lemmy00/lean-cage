(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Exact layouts come from individual object constructors. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers Floats AST Values Memory Memdata Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayPython GatewayMachine GatewayRuntime GatewayRegistry.
Import ListNotations.
Open Scope Z_scope.

Inductive gateway_builtin_kind :=
| gateway_none_kind | gateway_bool_kind | gateway_long_kind | gateway_float_kind
| gateway_unicode_kind | gateway_bytes_kind | gateway_list_kind | gateway_dict_kind
| gateway_outcome_kind | gateway_path_kind.

Record gateway_dictionary_entry := {
  gateway_dictionary_key : Values.val;
  gateway_dictionary_text : list Z;
  gateway_dictionary_value : Values.val
}.

Inductive gateway_object_value :=
| gateway_none_object
| gateway_bool_object (value:bool)
| gateway_long_object (value:Z)
| gateway_float_object (value:float)
| gateway_unicode_object (characters:list Z)
| gateway_bytes_object (bytes:list Byte.int)
| gateway_list_object (values:list Values.val)
| gateway_dict_object (fields:list gateway_dictionary_entry)
| gateway_outcome_object
| gateway_path_object (path:list Byte.int)
| gateway_foreign_object.

Definition gateway_object_kind value : option gateway_builtin_kind :=
  match value with
  |gateway_none_object=>Some gateway_none_kind
  |gateway_bool_object _=>Some gateway_bool_kind
  |gateway_long_object _=>Some gateway_long_kind
  |gateway_float_object _=>Some gateway_float_kind
  |gateway_unicode_object _=>Some gateway_unicode_kind
  |gateway_bytes_object _=>Some gateway_bytes_kind
  |gateway_list_object _=>Some gateway_list_kind
  |gateway_dict_object _=>Some gateway_dict_kind
  |gateway_outcome_object=>Some gateway_outcome_kind
  |gateway_path_object _=>Some gateway_path_kind
  |gateway_foreign_object=>None
  end.

Definition gateway_dictionary_children fields : list Values.val :=
  flat_map(fun field=>[gateway_dictionary_key field;gateway_dictionary_value field])fields.

Definition gateway_object_children value : list Values.val :=
  match value with
  |gateway_list_object values=>values
  |gateway_dict_object fields=>gateway_dictionary_children fields
  |_=>[]
  end.

Record gateway_object_heap := {
  gateway_object_values : Values.val->option gateway_object_value;
  gateway_object_private : Values.val->bool
}.

Definition gateway_exact_kind heap object kind :Prop:=
  exists value,gateway_object_values heap object=Some value /\gateway_object_kind value=Some kind.

Inductive gateway_rooted (python:python_world)(heap:gateway_object_heap) : Values.val->Prop :=
| gateway_direct_root:forall object,(0<python_native_strong python object)%nat ->gateway_rooted python heap object
| gateway_child_root:forall parent value child,
    gateway_rooted python heap parent ->gateway_object_values heap parent=Some value ->
    In child(gateway_object_children value) ->gateway_rooted python heap child.

Definition gateway_objects_valid python heap memory :Prop:=
  python_world_valid python memory /\
  (forall object,gateway_rooted python heap object ->python_live python object) /\
  (forall object bytes,gateway_rooted python heap object ->
    gateway_object_values heap object=Some(gateway_bytes_object bytes) ->
    exists storage,python_values python object=Some(python_byte_value storage) /\
      python_bytes_contents storage=bytes) /\
  (forall object fields,gateway_rooted python heap object ->
    gateway_object_values heap object=Some(gateway_dict_object fields) ->
    Forall(fun field=>gateway_object_values heap(gateway_dictionary_key field)=
      Some(gateway_unicode_object(gateway_dictionary_text field)))fields /\
      NoDup(map gateway_dictionary_text fields)) /\
  (forall object,gateway_rooted python heap object ->exists block offset,
    object=Vptr block offset /\Mem.weak_valid_pointer memory block(Ptrofs.unsigned offset)=true).

Definition gateway_objects_frame python heap next next_heap except :Prop:=
  forall object value,gateway_rooted python heap object ->gateway_rooted next next_heap object ->
    gateway_object_private heap object=true ->~In object except ->
    gateway_object_values heap object=Some value ->gateway_object_values next_heap object=Some value.

Definition gateway_object_privacy_frame python heap next next_heap except :Prop:=
  forall object,gateway_rooted python heap object ->gateway_rooted next next_heap object ->
    gateway_object_private heap object=true ->~In object except ->gateway_object_private next_heap object=true.

Definition gateway_native_references_frame before after except :Prop:=
  forall object,~In object except ->python_native_strong after object=python_native_strong before object.

Definition gateway_native_private python block :Prop:=~python_runtime_owned python block.

Record gateway_constructor_return python heap memory result next next_heap after value :Prop:={
  gateway_constructor_pointer:exists block offset,result=Vptr block offset;
  gateway_constructor_value:gateway_object_values next_heap result=Some value;
  gateway_constructor_private:gateway_object_private next_heap result=true;
  gateway_constructor_alias:gateway_rooted python heap result ->
    gateway_object_values heap result=Some value;
  gateway_constructor_fresh_container:match value with
    |gateway_list_object _|gateway_dict_object _=>python_strong python result=0%nat
    |_=>True end;
  gateway_constructor_owned:python_native_strong next result=S(python_native_strong python result);
  gateway_constructor_strong:python_strong next result=S(python_strong python result);
  gateway_constructor_refs:gateway_native_references_frame python next[result];
  gateway_constructor_gil:python_gil next=true;
  gateway_constructor_clear:python_pending next=None;
  gateway_constructor_frame:gateway_objects_frame python heap next next_heap[result];
  gateway_constructor_privacy:gateway_object_privacy_frame python heap next next_heap[result];
  gateway_constructor_native:python_private_frame python memory after;
  gateway_constructor_native_retained:forall block,Mem.valid_block memory block ->
    gateway_native_private python block ->gateway_native_private next block;
  gateway_constructor_valid:gateway_objects_valid next next_heap after
}.

(* IsInstance may consult an unrelated object's __class__. Its positive result
   is deliberately not a producer of exact native layout. *)
Definition gateway_builtin_accepts expected actual :bool:=
  match expected,actual with
  |gateway_none_kind,gateway_none_kind|gateway_bool_kind,gateway_bool_kind
  |gateway_long_kind,gateway_long_kind|gateway_long_kind,gateway_bool_kind
  |gateway_float_kind,gateway_float_kind|gateway_unicode_kind,gateway_unicode_kind
  |gateway_bytes_kind,gateway_bytes_kind|gateway_list_kind,gateway_list_kind
  |gateway_dict_kind,gateway_dict_kind|gateway_outcome_kind,gateway_outcome_kind
  |gateway_path_kind,gateway_path_kind=>true
  |_,_=>false
  end.

Inductive gateway_instance_result heap object expected :int->Prop:=
| gateway_instance_known:forall value actual,
    gateway_object_values heap object=Some value ->gateway_object_kind value=Some actual ->
    gateway_instance_result heap object expected
      (if gateway_builtin_accepts expected actual then Int.one else Int.zero)
| gateway_instance_spoofable:forall result,
    (forall value,gateway_object_values heap object=Some value ->gateway_object_kind value=None) ->
    (result=Int.zero \/result=Int.one) ->gateway_instance_result heap object expected result
| gateway_instance_exception:gateway_instance_result heap object expected(Int.neg Int.one).

Theorem gateway_constructed_layout python heap memory result next next_heap after value kind :
  gateway_constructor_return python heap memory result next next_heap after value ->
  gateway_object_kind value=Some kind ->gateway_exact_kind next_heap result kind.
Proof. intros RETURN KIND;exists value;split;[exact(gateway_constructor_value _ _ _ _ _ _ _ _ RETURN)|exact KIND]. Qed.

Theorem gateway_constructed_root python heap memory result next next_heap after value :
  gateway_constructor_return python heap memory result next next_heap after value ->
  gateway_rooted next next_heap result /\python_live next result.
Proof.
  intro RETURN.
  assert(ROOT:gateway_rooted next next_heap result).
  { constructor;rewrite(gateway_constructor_owned _ _ _ _ _ _ _ _ RETURN);lia. }
  split;[exact ROOT|]. destruct(gateway_constructor_valid _ _ _ _ _ _ _ _ RETURN)as[_[LIVE _]].
  apply LIVE;exact ROOT.
Qed.

Theorem gateway_instance_can_spoof object expected :
  exists heap,gateway_instance_result heap object expected Int.one /\
    forall kind,~gateway_exact_kind heap object kind.
Proof.
  exists{|gateway_object_values:=fun _=>Some gateway_foreign_object;gateway_object_private:=fun _=>false|}.
  split.
  - apply gateway_instance_spoofable;[intros value SAME;inversion SAME;reflexivity|auto].
  - intros kind[value[SAME KIND]];inversion SAME;subst value;discriminate.
Qed.

(* Exact extern definitions come from the current checked C/SDK declarations. *)
Inductive gateway_object_api :=
| gateway_api_incref | gateway_api_bool | gateway_api_long_signed | gateway_api_long_unsigned
| gateway_api_long_string | gateway_api_float_string | gateway_api_number_multiply
| gateway_api_number_add | gateway_api_number_negative | gateway_api_unicode_utf8
| gateway_api_unicode_fs | gateway_api_bytes | gateway_api_list_new | gateway_api_dict_new
| gateway_api_list_append | gateway_api_dict_contains | gateway_api_dict_set
| gateway_api_dict_get_string | gateway_api_dict_set_string | gateway_api_dict_copy
| gateway_api_dict_next | gateway_api_is_instance | gateway_api_generic_alloc | gateway_api_decref.

Definition gateway_object_api_ident api :ident:=
  match api with
  |gateway_api_incref=>_Py_IncRef|gateway_api_bool=>_PyBool_FromLong
  |gateway_api_long_signed=>_PyLong_FromLong|gateway_api_long_unsigned=>_PyLong_FromUnsignedLong
  |gateway_api_long_string=>_PyLong_FromString|gateway_api_float_string=>_PyFloat_FromString
  |gateway_api_number_multiply=>_PyNumber_Multiply|gateway_api_number_add=>_PyNumber_Add
  |gateway_api_number_negative=>_PyNumber_Negative|gateway_api_unicode_utf8=>_PyUnicode_DecodeUTF8
  |gateway_api_unicode_fs=>_PyUnicode_DecodeFSDefaultAndSize|gateway_api_bytes=>_PyBytes_FromStringAndSize
  |gateway_api_list_new=>_PyList_New|gateway_api_dict_new=>_PyDict_New
  |gateway_api_list_append=>_PyList_Append|gateway_api_dict_contains=>_PyDict_Contains
  |gateway_api_dict_set=>_PyDict_SetItem|gateway_api_dict_get_string=>_PyDict_GetItemString
  |gateway_api_dict_set_string=>_PyDict_SetItemString|gateway_api_dict_copy=>_PyDict_Copy
  |gateway_api_dict_next=>_PyDict_Next|gateway_api_is_instance=>_PyObject_IsInstance
  |gateway_api_generic_alloc=>_PyType_GenericAlloc|gateway_api_decref=>_Py_DecRef
  end.

Definition gateway_object_api_definition api :option(Ctypes.fundef Clight.function):=
  match gateway_program_definition(gateway_object_api_ident api)global_definitions with
  |Some(Gfun(External external types result convention))=>Some(External external types result convention)
  |_=>None
  end.

Definition gateway_object_operation {World Event}(backend:gateway_backend World Event)api arguments
    before world result after next observed :Prop:=
  exists definition,gateway_object_api_definition api=Some definition /\
    gateway_runtime_operation backend definition arguments before world result after next observed.

Theorem gateway_object_operation_actual {World Event}(backend:gateway_backend World Event)ge api
    external types result_type convention arguments continuation before world result after next observed :
  gateway_object_api_definition api=Some(External external types result_type convention) ->
  gateway_step backend ge
    (gateway_live(Callstate(External external types result_type convention)arguments continuation before)world)
    (gateway_primitive observed)(gateway_live(Returnstate result continuation after)next) ->
  gateway_object_operation backend api arguments before world result after next observed.
Proof. intros DEFINITION STEP;inversion STEP;subst;eexists;split;[exact DEFINITION|cbn[gateway_runtime_operation];eassumption]. Qed.

(* §FS-host-boundary.caller: Strict UTF-8 and the supported filesystem codec keep byte
   provenance. *)
Inductive gateway_utf8_character : list Byte.int->Z->Prop :=
| gateway_utf8_ascii:forall first,Byte.unsigned first<128 ->
    gateway_utf8_character[first](Byte.unsigned first)
| gateway_utf8_two:forall first second,
    194<=Byte.unsigned first<=223 ->128<=Byte.unsigned second<=191 ->
    gateway_utf8_character[first;second]
      (64*(Byte.unsigned first-192)+(Byte.unsigned second-128))
| gateway_utf8_three:forall first second third codepoint,
    224<=Byte.unsigned first<=239 ->128<=Byte.unsigned second<=191 ->
    128<=Byte.unsigned third<=191 ->
    codepoint=4096*(Byte.unsigned first-224)+64*(Byte.unsigned second-128)+(Byte.unsigned third-128) ->
    2048<=codepoint ->~(55296<=codepoint<=57343) ->
    gateway_utf8_character[first;second;third]codepoint
| gateway_utf8_four:forall first second third fourth codepoint,
    240<=Byte.unsigned first<=244 ->128<=Byte.unsigned second<=191 ->
    128<=Byte.unsigned third<=191 ->128<=Byte.unsigned fourth<=191 ->
    codepoint=262144*(Byte.unsigned first-240)+4096*(Byte.unsigned second-128)+
      64*(Byte.unsigned third-128)+(Byte.unsigned fourth-128) ->
    65536<=codepoint<=1114111 ->gateway_utf8_character[first;second;third;fourth]codepoint.

Inductive gateway_utf8_text :list Byte.int->list Z->Prop:=
| gateway_utf8_empty:gateway_utf8_text[][]
| gateway_utf8_next:forall encoded codepoint bytes characters,
    gateway_utf8_character encoded codepoint ->gateway_utf8_text bytes characters ->
    gateway_utf8_text(encoded++bytes)(codepoint::characters).

Inductive gateway_filesystem_text :list Byte.int->list Z->Prop:=
| gateway_filesystem_empty:gateway_filesystem_text[][]
| gateway_filesystem_unicode:forall encoded codepoint bytes characters,
    gateway_utf8_character encoded codepoint ->gateway_filesystem_text bytes characters ->
    gateway_filesystem_text(encoded++bytes)(codepoint::characters)
| gateway_filesystem_escape:forall first rest characters,
    128<=Byte.unsigned first ->
    (forall encoded codepoint later,gateway_utf8_character encoded codepoint ->
      first::rest<>encoded++later) ->gateway_filesystem_text rest characters ->
    gateway_filesystem_text(first::rest)((56320+Byte.unsigned first)::characters).

Fixpoint gateway_decimal_value (bytes:list Byte.int) :Z:=
  match bytes with[]=>0|first::rest=>
    (Byte.unsigned first-48)*10^Z.of_nat(length rest)+gateway_decimal_value rest end.
Definition gateway_decimal_digits bytes :Prop:=
  bytes<>[] /\Forall(fun byte=>48<=Byte.unsigned byte<=57)bytes /\
  (length bytes=1%nat \/forall first rest,bytes=first::rest ->Byte.unsigned first<>48).
Inductive gateway_decimal :list Byte.int->Z->Prop:=
| gateway_decimal_positive:forall bytes,gateway_decimal_digits bytes ->
    gateway_decimal bytes(gateway_decimal_value bytes)
| gateway_decimal_negative:forall bytes,gateway_decimal_digits bytes ->gateway_decimal_value bytes<>0 ->
    gateway_decimal(Byte.repr 45::bytes)(-gateway_decimal_value bytes).

Definition gateway_object_input memory pointer bytes :Prop:=
  exists block offset,pointer=Vptr block offset /\Mem.valid_block memory block /\
    Ptrofs.unsigned offset+Z.of_nat(length bytes)<=Ptrofs.modulus /\
    Mem.loadbytes memory block(Ptrofs.unsigned offset)(Z.of_nat(length bytes))=Some(inj_bytes bytes).
Definition gateway_object_cstring memory pointer bytes :Prop:=
  gateway_object_input memory pointer(bytes++[Byte.zero]).

Definition gateway_unicode_strict_mode memory errors :Prop:=
  errors=Vnullptr \/gateway_object_cstring memory errors(map Byte.repr[115;116;114;105;99;116]).

(* The float relation denotes one CPython decimal-to-binary conversion. It does
   not certify the application's lexical scan or the chunked integer helper. *)
Inductive gateway_constructor_request (decimal_float:list Z->float->Prop)
    heap memory :gateway_object_api->list val->gateway_object_value->Prop:=
| gateway_request_bool:forall (value:bool),
    gateway_constructor_request decimal_float heap memory gateway_api_bool
      [Vlong(if value then Int64.one else Int64.zero)](gateway_bool_object value)
| gateway_request_long_signed:forall value,
    gateway_constructor_request decimal_float heap memory gateway_api_long_signed
      [Vlong value](gateway_long_object(Int64.signed value))
| gateway_request_long_unsigned:forall value,
    gateway_constructor_request decimal_float heap memory gateway_api_long_unsigned
      [Vlong value](gateway_long_object(Int64.unsigned value))
| gateway_request_long_string:forall pointer bytes value,
    gateway_object_cstring memory pointer bytes ->gateway_decimal bytes value ->
    gateway_constructor_request decimal_float heap memory gateway_api_long_string
      [pointer;Vnullptr;Vint(Int.repr 10)](gateway_long_object value)
| gateway_request_float_string:forall object characters value,
    gateway_object_values heap object=Some(gateway_unicode_object characters) ->
    decimal_float characters value ->
    gateway_constructor_request decimal_float heap memory gateway_api_float_string
      [object](gateway_float_object value)
| gateway_request_multiply:forall left right first second,
    gateway_object_values heap left=Some(gateway_long_object first) ->
    gateway_object_values heap right=Some(gateway_long_object second) ->
    gateway_constructor_request decimal_float heap memory gateway_api_number_multiply
      [left;right](gateway_long_object(first*second))
| gateway_request_add:forall left right first second,
    gateway_object_values heap left=Some(gateway_long_object first) ->
    gateway_object_values heap right=Some(gateway_long_object second) ->
    gateway_constructor_request decimal_float heap memory gateway_api_number_add
      [left;right](gateway_long_object(first+second))
| gateway_request_negative:forall object value,
    gateway_object_values heap object=Some(gateway_long_object value) ->
    gateway_constructor_request decimal_float heap memory gateway_api_number_negative
      [object](gateway_long_object(-value))
| gateway_request_unicode_utf8:forall pointer bytes characters errors,
    gateway_object_input memory pointer bytes ->gateway_utf8_text bytes characters ->
    Z.of_nat(length bytes)<=Int64.max_signed ->gateway_unicode_strict_mode memory errors ->
    gateway_constructor_request decimal_float heap memory gateway_api_unicode_utf8
      [pointer;Vlong(Int64.repr(Z.of_nat(length bytes)));errors](gateway_unicode_object characters)
| gateway_request_unicode_filesystem:forall pointer bytes characters,
    gateway_object_input memory pointer bytes ->gateway_filesystem_text bytes characters ->
    Z.of_nat(length bytes)<=Int64.max_signed ->
    gateway_constructor_request decimal_float heap memory gateway_api_unicode_fs
      [pointer;Vlong(Int64.repr(Z.of_nat(length bytes)))](gateway_unicode_object characters)
| gateway_request_bytes:forall pointer bytes,
    gateway_object_input memory pointer bytes ->Z.of_nat(length bytes)<=Int64.max_signed ->
    gateway_constructor_request decimal_float heap memory gateway_api_bytes
      [pointer;Vlong(Int64.repr(Z.of_nat(length bytes)))](gateway_bytes_object bytes)
| gateway_request_dictionary_copy:forall object fields,
    gateway_object_values heap object=Some(gateway_dict_object fields) ->
    gateway_constructor_request decimal_float heap memory gateway_api_dict_copy
      [object](gateway_dict_object fields)
| gateway_request_list:gateway_constructor_request decimal_float heap memory gateway_api_list_new
    [Vlong Int64.zero](gateway_list_object[])
| gateway_request_dictionary:gateway_constructor_request decimal_float heap memory gateway_api_dict_new
    [](gateway_dict_object[]).

Definition gateway_objects_ready python heap memory :Prop:=
  gateway_objects_valid python heap memory /\python_gil python=true /\python_pending python=None.

Definition gateway_constructor_roots python heap api arguments :Prop:=
  match api,arguments with
  |gateway_api_float_string,[object]|gateway_api_number_negative,[object]|gateway_api_dict_copy,[object]=>
    gateway_rooted python heap object
  |gateway_api_number_add,[first;second]|gateway_api_number_multiply,[first;second]=>
    gateway_rooted python heap first /\gateway_rooted python heap second
  |_,_=>True
  end.

Record gateway_objects_runtime {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(objects:World->gateway_object_heap)
    (decimal_float:list Z->float->Prop) :Prop:={
  gateway_runtime_constructor:forall api arguments before world result after next observed value,
    gateway_objects_ready(python world)(objects world)before ->
    gateway_constructor_request decimal_float(objects world)before api arguments value ->
    gateway_constructor_roots(python world)(objects world)api arguments ->
    gateway_object_operation backend api arguments before world result after next observed ->
    result<>Vnullptr ->
    gateway_constructor_return(python world)(objects world)before result(python next)(objects next)after value;
  gateway_runtime_utf8_constructor:forall before world pointer bytes errors result after next observed,
    gateway_objects_ready(python world)(objects world)before ->
    gateway_object_input before pointer bytes ->Z.of_nat(length bytes)<=Int64.max_signed ->
    gateway_unicode_strict_mode before errors ->
    gateway_object_operation backend gateway_api_unicode_utf8
      [pointer;Vlong(Int64.repr(Z.of_nat(length bytes)));errors]before world result after next observed ->
    result<>Vnullptr ->exists characters,gateway_utf8_text bytes characters /\
      gateway_constructor_return(python world)(objects world)before result(python next)(objects next)after
        (gateway_unicode_object characters);
  gateway_runtime_filesystem_constructor:forall before world pointer bytes result after next observed,
    gateway_objects_ready(python world)(objects world)before ->
    gateway_object_input before pointer bytes ->Z.of_nat(length bytes)<=Int64.max_signed ->
    gateway_object_operation backend gateway_api_unicode_fs
      [pointer;Vlong(Int64.repr(Z.of_nat(length bytes)))]before world result after next observed ->
    result<>Vnullptr ->exists characters,gateway_filesystem_text bytes characters /\
      gateway_constructor_return(python world)(objects world)before result(python next)(objects next)after
        (gateway_unicode_object characters);
  gateway_runtime_float_constructor:forall before world text characters result after next observed,
    gateway_objects_ready(python world)(objects world)before ->
    gateway_rooted(python world)(objects world)text ->
    gateway_object_values(objects world)text=Some(gateway_unicode_object characters) ->
    gateway_object_operation backend gateway_api_float_string[text]before world result after next observed ->
    result<>Vnullptr ->exists value,decimal_float characters value /\
      gateway_constructor_return(python world)(objects world)before result(python next)(objects next)after
        (gateway_float_object value)
}.

Theorem gateway_actual_constructor_has_exact_layout {World Event}(backend:gateway_backend World Event)
    python objects decimal_float api arguments before world result after next observed value kind :
  gateway_objects_runtime backend python objects decimal_float ->
  gateway_objects_ready(python world)(objects world)before ->
  gateway_constructor_request decimal_float(objects world)before api arguments value ->
  gateway_constructor_roots(python world)(objects world)api arguments ->
  gateway_object_operation backend api arguments before world result after next observed ->
  result<>Vnullptr ->gateway_object_kind value=Some kind ->
  gateway_exact_kind(objects next)result kind /\gateway_rooted(python next)(objects next)result.
Proof.
  intros LAW READY REQUEST ROOTS OPERATION NONNULL KIND.
  pose proof(gateway_runtime_constructor _ _ _ _ LAW _ _ _ _ _ _ _ _ _
    READY REQUEST ROOTS OPERATION NONNULL)as RETURN.
  split.
  - eapply gateway_constructed_layout;[exact RETURN|exact KIND].
  - exact(proj1(gateway_constructed_root _ _ _ _ _ _ _ _ RETURN)).
Qed.

Definition gateway_dictionary_lookup text fields :=
  find(fun field=>if list_eq_dec Z.eq_dec(gateway_dictionary_text field)text then true else false)fields.
Definition gateway_object_name memory pointer characters :Prop:=
  exists bytes,gateway_object_cstring memory pointer bytes /\~In Byte.zero bytes /\
    gateway_utf8_text bytes characters.

Record gateway_observer_return python heap memory next next_heap after :Prop:={
  gateway_observer_ready:gateway_objects_ready next next_heap after;
  gateway_observer_references:gateway_native_references_frame python next[];
  gateway_observer_values:gateway_objects_frame python heap next next_heap[];
  gateway_observer_privacy:gateway_object_privacy_frame python heap next next_heap[];
  gateway_observer_native:python_private_frame python memory after;
  gateway_observer_native_retained:forall block,Mem.valid_block memory block ->
    gateway_native_private python block ->gateway_native_private next block
}.

Record gateway_container_return python heap memory container next next_heap after value :Prop:={
  gateway_container_value:gateway_object_values next_heap container=Some value;
  gateway_container_private:gateway_object_private next_heap container=true;
  gateway_container_ready:gateway_objects_ready next next_heap after;
  gateway_container_references:gateway_native_references_frame python next[];
  gateway_container_values:gateway_objects_frame python heap next next_heap[container];
  gateway_container_privacy:gateway_object_privacy_frame python heap next next_heap[container];
  gateway_container_native:python_private_frame python memory after;
  gateway_container_native_retained:forall block,Mem.valid_block memory block ->
    gateway_native_private python block ->gateway_native_private next block
}.

Record gateway_container_runtime {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(objects:World->gateway_object_heap) :Prop:={
  gateway_runtime_list_append:forall before world container values child after next observed,
    gateway_objects_ready(python world)(objects world)before ->
    gateway_rooted(python world)(objects world)container ->gateway_rooted(python world)(objects world)child ->
    gateway_object_private(objects world)container=true ->
    gateway_object_values(objects world)container=Some(gateway_list_object values) ->
    gateway_object_operation backend gateway_api_list_append[container;child]before world
      (Vint Int.zero)after next observed ->
    gateway_container_return(python world)(objects world)before container(python next)(objects next)after
      (gateway_list_object(values++[child])) /\
    python_strong(python next)child=S(python_strong(python world)child);
  gateway_runtime_dict_contains:forall before world dictionary fields key characters result after next observed,
    gateway_objects_ready(python world)(objects world)before ->
    gateway_rooted(python world)(objects world)dictionary ->gateway_rooted(python world)(objects world)key ->
    gateway_object_values(objects world)dictionary=Some(gateway_dict_object fields) ->
    gateway_object_values(objects world)key=Some(gateway_unicode_object characters) ->
    gateway_object_operation backend gateway_api_dict_contains[dictionary;key]before world
      (Vint result)after next observed ->
    (result=Int.zero /\gateway_dictionary_lookup characters fields=None \/
     result=Int.one /\gateway_dictionary_lookup characters fields<>None \/result=Int.neg Int.one) /\
    (result<>Int.neg Int.one ->gateway_observer_return(python world)(objects world)before
      (python next)(objects next)after);
  gateway_runtime_dict_insert:forall before world dictionary fields key characters value after next observed,
    gateway_objects_ready(python world)(objects world)before ->
    gateway_rooted(python world)(objects world)dictionary ->gateway_rooted(python world)(objects world)key ->
    gateway_rooted(python world)(objects world)value ->gateway_object_private(objects world)dictionary=true ->
    gateway_object_values(objects world)dictionary=Some(gateway_dict_object fields) ->
    gateway_object_values(objects world)key=Some(gateway_unicode_object characters) ->
    gateway_dictionary_lookup characters fields=None ->
    gateway_object_operation backend gateway_api_dict_set[dictionary;key;value]before world
      (Vint Int.zero)after next observed ->
    gateway_container_return(python world)(objects world)before dictionary(python next)(objects next)after
      (gateway_dict_object(fields++[{|gateway_dictionary_key:=key;gateway_dictionary_text:=characters;
        gateway_dictionary_value:=value|}])) /\
    (forall object,python_strong(python next)object=
      (python_strong(python world)object+count_occ Val.eq[key;value]object)%nat);
  gateway_runtime_dict_lookup:forall before world dictionary fields name characters result after next observed,
    gateway_objects_ready(python world)(objects world)before ->
    gateway_rooted(python world)(objects world)dictionary ->
    gateway_object_values(objects world)dictionary=Some(gateway_dict_object fields) ->
    gateway_object_name before name characters ->
    gateway_object_operation backend gateway_api_dict_get_string[dictionary;name]before world
      result after next observed ->result<>Vnullptr ->
    exists field,gateway_dictionary_lookup characters fields=Some field /\
      result=gateway_dictionary_value field /\gateway_observer_return(python world)(objects world)before
        (python next)(objects next)after
}.

Theorem gateway_dictionary_lookup_member characters fields field :
  gateway_dictionary_lookup characters fields=Some field ->
  In field fields /\gateway_dictionary_text field=characters.
Proof.
  intro LOOK;apply find_some in LOOK;destruct LOOK as[MEMBER TEXT];split;[exact MEMBER|].
  destruct(list_eq_dec Z.eq_dec(gateway_dictionary_text field)characters);[assumption|discriminate].
Qed.

Theorem gateway_actual_dictionary_item_is_reachable {World Event}(backend:gateway_backend World Event)
    python objects before world dictionary fields name characters result after next observed :
  gateway_container_runtime backend python objects ->
  gateway_objects_ready(python world)(objects world)before ->
  gateway_rooted(python world)(objects world)dictionary ->
  gateway_object_values(objects world)dictionary=Some(gateway_dict_object fields) ->
  gateway_object_name before name characters ->
  gateway_object_operation backend gateway_api_dict_get_string[dictionary;name]before world
    result after next observed ->result<>Vnullptr ->gateway_rooted(python world)(objects world)result.
Proof.
  intros LAW READY ROOT VALUE NAME OPERATION NONNULL.
  destruct(gateway_runtime_dict_lookup backend python objects LAW before world dictionary fields name characters result after next observed
    READY ROOT VALUE NAME OPERATION NONNULL)as[field[LOOK[RESULT FRAME]]];subst result.
  eapply gateway_child_root;[exact ROOT|exact VALUE|].
  unfold gateway_object_children,gateway_dictionary_children.
  apply in_flat_map;exists field;split;[exact(proj1(gateway_dictionary_lookup_member _ _ _ LOOK))|cbn;auto].
Qed.

Definition gateway_python_memory_frame python before after :Prop:=
  Mem.unchanged_on(fun block _=>python_runtime_owned python block)before after.

Lemma gateway_objects_ready_native_frame python heap before after :
  gateway_objects_ready python heap before ->gateway_python_memory_frame python before after ->
  gateway_objects_ready python heap after.
Proof.
  intros[[WORLD[ROOTS[BYTES[DICTS ADDRESSES]]]][GIL PENDING]]FRAME.
  destruct WORLD as[COUNTS[LOADED[OWNED REPRESENTED]]].
  split;[|split;assumption].
  split.
  - split;[exact COUNTS|]. split.
    + intros object bytes VALUE LIVE.
      destruct(LOADED object bytes VALUE LIVE)as[OFFSET[BOUND[PERMISSIONS DATA]]].
      destruct(REPRESENTED object(python_byte_value bytes)VALUE LIVE)as[OBJECT OWNER].
      split;[exact OFFSET|]. split;[exact BOUND|]. split.
      * intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME|exact OWNER|].
        apply PERMISSIONS;exact RANGE.
      * eapply Mem.loadbytes_unchanged_on;[exact FRAME|intros;exact OWNER|exact DATA].
    + split.
      * intros object OWNER;eapply Mem.valid_block_unchanged_on;[exact FRAME|apply OWNED;exact OWNER].
      * exact REPRESENTED.
  - split;[exact ROOTS|]. split;[exact BYTES|]. split;[exact DICTS|].
    intros object ROOT;destruct(ADDRESSES object ROOT)as[block[offset[POINTER LIVE]]].
    destruct(ROOTS object ROOT)as[COUNT[value VALUE]].
    destruct(REPRESENTED object value VALUE COUNT)as[[actual_block[actual_offset[ACTUAL OWNER]]]EXTRA].
    rewrite POINTER in ACTUAL;inversion ACTUAL;subst actual_block actual_offset.
    exists block,offset;split;[exact POINTER|].
    apply Mem.weak_valid_pointer_spec in LIVE;apply Mem.weak_valid_pointer_spec.
    destruct LIVE as[CURRENT|PREVIOUS];[left|right].
    all:apply Mem.valid_pointer_nonempty_perm in CURRENT||apply Mem.valid_pointer_nonempty_perm in PREVIOUS.
    all:apply Mem.valid_pointer_nonempty_perm;eapply Mem.perm_unchanged_on;
      [exact FRAME|exact OWNER|assumption].
Qed.

Theorem gateway_owned_stack_allocation_ready python heap before allocated block amount :
  gateway_objects_ready python heap before ->Mem.alloc before 0 amount=(allocated,block) ->
  gateway_objects_ready python heap allocated /\gateway_native_private python block.
Proof.
  intros READY ALLOC;split.
  - eapply gateway_objects_ready_native_frame;[exact READY|].
    eapply Mem.alloc_unchanged_on;exact ALLOC.
  - destruct READY as[[[_[_[OWNED _]]]_ ]_].
    intro RUNTIME;apply(Mem.fresh_block_alloc _ _ _ _ _ ALLOC);apply OWNED;exact RUNTIME.
Qed.

Theorem gateway_owned_native_store_ready python heap before after chunk block offset value :
  gateway_objects_ready python heap before ->gateway_native_private python block ->
  Mem.store chunk before block offset value=Some after ->gateway_objects_ready python heap after.
Proof.
  intros READY PRIVATE STORE;eapply gateway_objects_ready_native_frame;[exact READY|].
  eapply Mem.store_unchanged_on;[exact STORE|intros position RANGE RUNTIME;exact(PRIVATE RUNTIME)].
Qed.

Theorem gateway_owned_native_free_ready python heap before after block low high :
  gateway_objects_ready python heap before ->gateway_native_private python block ->
  Mem.free before block low high=Some after ->gateway_objects_ready python heap after.
Proof.
  intros READY PRIVATE FREE;eapply gateway_objects_ready_native_frame;[exact READY|].
  eapply Mem.free_unchanged_on;[exact FREE|intros position RANGE RUNTIME;exact(PRIVATE RUNTIME)].
Qed.
