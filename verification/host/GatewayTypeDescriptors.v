(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Immutable attribute dispatch consumes the actual type-creation inputs. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayTypeRuntime GatewayGetsets GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Record gateway_type_method:={
  gateway_type_method_name:list Byte.int;
  gateway_type_method_function:Values.val;
  gateway_type_method_flags:int
}.

Fixpoint gateway_methods_memory memory table offset(methods:list gateway_type_method):Prop:=
  match methods with
  |[]=>Mem.load Mptr memory table offset=Some Vnullptr
  |method::rest=>exists name,
    Mem.load Mptr memory table offset=Some name /\gateway_error_cstring memory name(gateway_type_method_name method) /\
    Mem.load Mptr memory table(offset+8)=Some(gateway_type_method_function method) /\
    Mem.load Mint32 memory table(offset+16)=Some(Vint(gateway_type_method_flags method)) /\
    gateway_methods_memory memory table(offset+32)rest end.

Definition gateway_special_attribute_names:list(list Byte.int):=map(map Byte.repr)
  [[95;95;103;101;116;97;116;116;114;105;98;117;116;101;95;95];
   [95;95;103;101;116;97;116;116;114;95;95];[95;95;115;101;116;97;116;116;114;95;95];
   [95;95;100;101;108;97;116;116;114;95;95];[95;95;99;108;97;115;115;95;95]].

Definition gateway_default_attribute_slots description:Prop:=
  forall code function,In(code,function)(gateway_type_slots description) ->
    code<>Int.repr 57 /\code<>Int.repr 58 /\code<>Int.repr 68 /\code<>Int.repr 69.

Definition gateway_plain_attribute_tables entries methods:Prop:=
  (forall entry,In entry entries->~In(gateway_getset_name entry)gateway_special_attribute_names) /\
    (forall method,In method methods->~In(gateway_type_method_name method)gateway_special_attribute_names).

(* Class values carry allocation identities, not reusable raw address numbers.
   This immutable fact is created by one real FromSpec operation. It records
   only dispatch metadata; it says nothing about mutable instance contents. *)
Record gateway_descriptor_runtime {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(objects:World->gateway_object_heap)
    (types:World->Values.val->option gateway_type_description)(default_allocator:World->Values.val->Prop)
    (instances:World->Values.val->option Values.val)
    (immutable_binding:Values.val->gateway_type_description->list gateway_getset_entry->Prop)
    (attribute_target:World->Values.val->list Byte.int->Values.val->Values.val->Prop):Prop:={
  gateway_from_spec_descriptor_binding:forall before world pointer description entries methods
      property_table property_offset method_table method_offset result after next observed,
    gateway_objects_ready(python world)(objects world)before ->
    gateway_type_spec_memory before pointer description ->gateway_type_itemsize description=0 ->
    Int.and(gateway_type_flags description)(Int.repr 256)=Int.repr 256 ->
    gateway_default_attribute_slots description ->
    In(Int.repr 73,Vptr property_table property_offset)(gateway_type_slots description) ->
    In(Int.repr 64,Vptr method_table method_offset)(gateway_type_slots description) ->
    Ptrofs.unsigned property_offset+40*Z.of_nat(length entries)+8<=Ptrofs.modulus ->
    Ptrofs.unsigned method_offset+32*Z.of_nat(length methods)+8<=Ptrofs.modulus ->
    gateway_getsets_memory before property_table(Ptrofs.unsigned property_offset)entries ->
    gateway_methods_memory before method_table(Ptrofs.unsigned method_offset)methods ->
    NoDup(map gateway_getset_name entries) ->gateway_plain_attribute_tables entries methods ->
    gateway_type_operation backend gateway_type_from_spec[pointer]before world result after next observed ->
    result<>Vnullptr ->immutable_binding result description entries;
  gateway_immutable_type_description:forall memory world class description entries,
    gateway_objects_ready(python world)(objects world)memory ->gateway_rooted(python world)(objects world)class ->
    immutable_binding class description entries ->types world class=Some description /\
      (gateway_type_default_slots description->default_allocator world class);
  gateway_immutable_attribute_dispatch:forall memory world object class description entries entry getter closure,
    gateway_objects_ready(python world)(objects world)memory ->
    gateway_rooted(python world)(objects world)object ->gateway_rooted(python world)(objects world)class ->
    instances world object=Some class ->immutable_binding class description entries ->In entry entries ->
    gateway_getset_getter entry<>Vnullptr ->
    attribute_target world object(gateway_getset_name entry)getter closure ->
    getter=gateway_getset_getter entry /\closure=gateway_getset_closure entry
}.

Theorem gateway_immutable_getter_selected {World Event}(backend:gateway_backend World Event)
    python objects types default_allocator instances immutable_binding attribute_target
    (runtime:gateway_descriptor_runtime backend python objects types default_allocator instances immutable_binding attribute_target)
    memory world object class description entries entry getter closure:
  gateway_objects_ready(python world)(objects world)memory ->
  gateway_rooted(python world)(objects world)object ->gateway_rooted(python world)(objects world)class ->
  instances world object=Some class ->immutable_binding class description entries ->In entry entries ->
  gateway_getset_getter entry<>Vnullptr ->attribute_target world object(gateway_getset_name entry)getter closure ->
  getter=gateway_getset_getter entry /\closure=gateway_getset_closure entry.
Proof. eapply gateway_immutable_attribute_dispatch;exact runtime. Qed.
