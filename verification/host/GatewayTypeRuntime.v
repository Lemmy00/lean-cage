(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Type construction and roots are individual SDK effects. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayRegistry GatewayPython
  GatewayObjects GatewayRootLeases GatewayThreadRuntime GatewayStreamInterface GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Inductive gateway_type_api:=gateway_type_from_spec|gateway_type_generic_new|gateway_module_add_object_ref.
Definition gateway_type_ident api:ident:=match api with
  |gateway_type_from_spec=>_PyType_FromSpec|gateway_type_generic_new=>_PyType_GenericNew
  |gateway_module_add_object_ref=>_PyModule_AddObjectRef end.
Definition gateway_type_definition api:option(Ctypes.fundef Clight.function):=
  match gateway_program_definition(gateway_type_ident api)global_definitions with
  |Some(Gfun(External external types result convention))=>Some(External external types result convention)
  |_=>None end.
Definition gateway_type_operation {World Event}(backend:gateway_backend World Event)api arguments
    before world result after next observed:Prop:=
  exists definition,gateway_type_definition api=Some definition /\
    gateway_runtime_operation backend definition arguments before world result after next observed.

Theorem actual_gateway_type_abis:
  gateway_type_definition gateway_type_from_spec=Some(External
    (EF_external "PyType_FromSpec"(mksignature[Xptr]Xptr cc_default))
    [tptr(Tstruct __5268 noattr)](tptr(Tstruct __object noattr))cc_default) /\
  gateway_type_definition gateway_type_generic_new=Some(External
    (EF_external "PyType_GenericNew"(mksignature[Xptr;Xptr;Xptr]Xptr cc_default))
    [tptr(Tstruct __typeobject noattr);tptr(Tstruct __object noattr);tptr(Tstruct __object noattr)]
    (tptr(Tstruct __object noattr))cc_default) /\
  gateway_type_definition gateway_module_add_object_ref=Some(External
    (EF_external "PyModule_AddObjectRef"(mksignature[Xptr;Xptr;Xptr]Xint cc_default))
    [tptr(Tstruct __object noattr);tptr tschar;tptr(Tstruct __object noattr)]tint cc_default).
Proof. repeat split;reflexivity. Qed.

Record gateway_type_description:={
  gateway_type_basicsize:Z;
  gateway_type_itemsize:Z;
  gateway_type_flags:int;
  gateway_type_slots:list(int*Values.val)
}.

Fixpoint gateway_slot_memory(memory:mem)(object:block)(offset:Z)(slots:list(int*Values.val)):Prop:=
  match slots with
  |[]=>Mem.load Mint32 memory object offset=Some(Vint Int.zero)
  |(code,function)::rest=>Mem.load Mint32 memory object offset=Some(Vint code) /\
    Mem.load Mptr memory object(offset+8)=Some function /\gateway_slot_memory memory object(offset+16)rest
  end.

(* These are ordinary individual struct/slot loads. A source client must produce
   this predicate from its actual initialized globals and their retained bytes. *)
Definition gateway_type_spec_memory memory pointer(description:gateway_type_description):Prop:=
  exists object offset name name_bytes table table_offset,
    pointer=Vptr object offset /\Ptrofs.unsigned offset+32<=Ptrofs.modulus /\
    Mem.load Mptr memory object(Ptrofs.unsigned offset)=Some name /\
    gateway_error_cstring memory name name_bytes /\name_bytes<>[] /\
    Mem.load Mint32 memory object(Ptrofs.unsigned offset+8)=Some(Vint(Int.repr(gateway_type_basicsize description))) /\
    Mem.load Mint32 memory object(Ptrofs.unsigned offset+12)=Some(Vint(Int.repr(gateway_type_itemsize description))) /\
    Mem.load Mint32 memory object(Ptrofs.unsigned offset+16)=Some(Vint(gateway_type_flags description)) /\
    Mem.load Mptr memory object(Ptrofs.unsigned offset+24)=Some(Vptr table table_offset) /\
    Ptrofs.unsigned table_offset+16*Z.of_nat(length(gateway_type_slots description))+4<=Ptrofs.modulus /\
    gateway_slot_memory memory table(Ptrofs.unsigned table_offset)(gateway_type_slots description).

Definition gateway_type_default_slots(description:gateway_type_description):Prop:=
  forall code function,In(code,function)(gateway_type_slots description)->code<>Int.repr 47.

Definition gateway_cancellation_field memory pointer value:Prop:=
  exists object offset,pointer=Vptr object offset /\Ptrofs.unsigned offset+24<=Ptrofs.modulus /\
    Mem.valid_access memory Mint32 object(Ptrofs.unsigned offset+16)Writable /\
    Mem.load Mint32 memory object(Ptrofs.unsigned offset+16)=Some(Vint value).

(* Native-reference tickets denote this invocation's roots. Module attributes
   may later be rebound without consuming the independently retained C root. *)
Record gateway_type_runtime {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(objects:World->gateway_object_heap)
    (types:World->Values.val->option gateway_type_description)
    (default_allocator:World->Values.val->Prop)
    (instances:World->Values.val->option Values.val)(leases:World->nat->Values.val->Prop)
    (normal attached:mem->World->Prop)(io:Event->option gateway_native_io)
    (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop):Prop:={
  gateway_type_normal:forall memory world,normal memory world->
    python_gil(python world)=true /\python_pending(python world)=None /\gateway_objects_valid(python world)(objects world)memory;
  gateway_type_attached:forall memory world,attached memory world->
    python_gil(python world)=true /\gateway_objects_valid(python world)(objects world)memory;
  gateway_type_from_spec_effect:forall before world pointer description result after next observed,
    normal before world ->gateway_type_spec_memory before pointer description ->
    16<=gateway_type_basicsize description<=Int.max_signed ->gateway_type_itemsize description=0 ->
    gateway_type_operation backend gateway_type_from_spec[pointer]before world result after next observed ->
    attached after next /\gateway_access_retained native_private stable_readonly before world next /\
    gateway_native_frame native_private stable_readonly gateway_native_no_output world before after /\io observed=None /\
    (result=Vnullptr \/exists ticket,normal after next /\types next result=Some description /\
      (gateway_type_default_slots description->default_allocator next result) /\
      gateway_reference_created leases world next result ticket);
  gateway_generic_new_effect:forall before world class arguments keywords description result after next observed,
    normal before world ->types world class=Some description ->default_allocator world class ->
    gateway_rooted(python world)(objects world)class ->
    gateway_type_basicsize description=24 ->gateway_type_itemsize description=0 ->
    gateway_type_operation backend gateway_type_generic_new[class;arguments;keywords]
      before world result after next observed ->
    attached after next /\gateway_access_retained native_private stable_readonly before world next /\
    gateway_native_frame native_private stable_readonly gateway_native_no_output world before after /\io observed=None /\
    (result=Vnullptr \/exists object ticket,
      result=Vptr object Ptrofs.zero /\~Mem.valid_block before object /\
      normal after next /\instances next result=Some class /\
      gateway_cancellation_field after result Int.zero /\
      gateway_reference_created leases world next result ticket);
  gateway_module_add_ref_effect:forall before world module name name_bytes object result after next observed,
    normal before world ->gateway_rooted(python world)(objects world)module ->
    gateway_rooted(python world)(objects world)object ->
    gateway_error_cstring before name name_bytes ->
    gateway_type_operation backend gateway_module_add_object_ref[module;name;object]
      before world result after next observed ->
    (exists status,result=Vint status /\(status=Int.zero->normal after next)) /\attached after next /\
    gateway_leases_retained leases world next /\
    gateway_access_retained native_private stable_readonly before world next /\
    gateway_native_frame native_private stable_readonly gateway_native_no_output world before after /\io observed=None
}.

Theorem gateway_new_cancellation_initialized {World Event}(backend:gateway_backend World Event)
    python objects types default_allocator instances leases normal attached io native_private stable_readonly
    (runtime:gateway_type_runtime backend python objects types default_allocator instances leases normal attached io native_private stable_readonly)
    before world class arguments keywords description result after next observed:
  normal before world->types world class=Some description->default_allocator world class->
  gateway_rooted(python world)(objects world)class->
  gateway_type_basicsize description=24->gateway_type_itemsize description=0->
  gateway_type_operation backend gateway_type_generic_new[class;arguments;keywords]
    before world result after next observed->result<>Vnullptr->
  exists object ticket,result=Vptr object Ptrofs.zero /\~Mem.valid_block before object /\normal after next /\
    instances next result=Some class /\gateway_cancellation_field after result Int.zero /\
    gateway_reference_created leases world next result ticket.
Proof.
  intros NORMAL TYPE ALLOCATOR ROOT SIZE ITEMS OPERATION NONNULL.
  pose proof(@gateway_generic_new_effect World Event backend python objects types default_allocator instances leases
    normal attached io native_private stable_readonly runtime
    before world class arguments keywords description result after next observed
    NORMAL TYPE ALLOCATOR ROOT SIZE ITEMS OPERATION)as EFFECT.
  destruct EFFECT as[_[_[_[_[NULL|NEW]]]]];[contradiction|exact NEW].
Qed.
