(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: GenericAlloc and immutable class metadata are individual SDK effects. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayOperations GatewayReadonly
  GatewayObjects GatewayPython GatewayRootLeases GatewayTypeRuntime GatewayOutcomeMemory GatewayObjectRuns
  GatewayStreamInterface GatewayThreadRuntime GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_outcome_data_cell memory object data :Prop:=
  Mem.valid_access memory Mptr object 16 Writable /\Mem.load Mptr memory object 16=Some data.

Definition gateway_outcome_cell_region(object:block)candidate position:Prop:=candidate=object /\16<=position<24.

(* This authority concerns the not-yet-published instance held by the current C
   call. Public instances and later reinitialization have no such authority. *)
Definition gateway_outcome_private_cell {World}(python:World->python_world)
    (owned:World->Values.val->Prop)memory world object :Prop:=
  owned world(Vptr object Ptrofs.zero) /\python_runtime_owned(python world)object /\
    gateway_outcome_cell_separate(python world)object /\
    Mem.valid_access memory Mptr object 16 Writable /\Mem.weak_valid_pointer memory object 0=true.

Record gateway_outcome_allocation_runtime {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(objects:World->gateway_object_heap)
    (types:World->Values.val->option gateway_type_description)(default_allocator:World->Values.val->Prop)
    (instances:World->Values.val->option Values.val)(leases:World->nat->Values.val->Prop)
    (owned:World->Values.val->Prop)(io:Event->option gateway_native_io)
    (native:World->block->Prop)(stable:World->block->Z->Prop):Prop:={
  gateway_outcome_class_ambient:forall before world after next class description,
    gateway_objects_ready(python world)(objects world)before ->
    gateway_rooted(python world)(objects world)class ->types world class=Some description ->
    default_allocator world class ->Int.and(gateway_type_flags description)(Int.repr 256)=Int.repr 256 ->
    gateway_interference backend before world after next ->
    gateway_rooted(python next)(objects next)class /\types next class=Some description /\default_allocator next class;
  gateway_outcome_generic_alloc:forall before world class description result after next observed,
    gateway_objects_ready(python world)(objects world)before ->
    gateway_rooted(python world)(objects world)class ->types world class=Some description ->
    default_allocator world class ->gateway_type_basicsize description=24 ->gateway_type_itemsize description=0 ->
    Int.and(gateway_type_flags description)(Int.repr 256)=Int.repr 256 ->
    gateway_object_operation backend gateway_api_generic_alloc[class;Vlong Int64.zero]
      before world result after next observed ->
    gateway_access_retained native stable before world next /\
    gateway_native_frame native stable gateway_native_no_output world before after /\io observed=None /\
    (result=Vnullptr \/exists object ticket,
      result=Vptr object Ptrofs.zero /\~Mem.valid_block before object /\
      gateway_objects_ready(python next)(objects next)after /\
      instances next result=Some class /\types next class=Some description /\default_allocator next class /\
      gateway_object_values(objects next)result=Some gateway_outcome_object /\
      gateway_object_private(objects next)result=true /\gateway_reference_created leases world next result ticket /\
      gateway_outcome_private_cell python owned after next object /\
      Mem.load Mptr after object 16=Some Vnullptr /\
      gateway_objects_frame(python world)(objects world)(python next)(objects next)[] /\
      gateway_object_privacy_frame(python world)(objects world)(python next)(objects next)[]);
  gateway_outcome_cell_ambient:forall before world after next object,
    gateway_objects_ready(python world)(objects world)before ->
    gateway_outcome_private_cell python owned before world object ->
    gateway_interference backend before world after next ->
    gateway_outcome_private_cell python owned after next object /\
      instances next(Vptr object Ptrofs.zero)=instances world(Vptr object Ptrofs.zero) /\
      Mem.unchanged_on(gateway_outcome_cell_region object)before after
}.

Theorem actual_gateway_generic_alloc_abi :
  gateway_object_api_definition gateway_api_generic_alloc=Some(External
    (EF_external "PyType_GenericAlloc"(mksignature[Xptr;Xlong]Xptr cc_default))
    [tptr(Tstruct __typeobject noattr);tlong](tptr(Tstruct __object noattr))cc_default).
Proof. reflexivity. Qed.

Theorem gateway_actual_generic_allocated {World Event}(backend:gateway_backend World Event)
    python objects types default_allocator instances leases owned io native stable
    (runtime:gateway_outcome_allocation_runtime backend python objects types default_allocator instances leases owned io native stable)
    before world class description result after next observed :
  gateway_objects_ready(python world)(objects world)before ->
  gateway_rooted(python world)(objects world)class ->types world class=Some description ->
  default_allocator world class ->gateway_type_basicsize description=24 ->gateway_type_itemsize description=0 ->
  Int.and(gateway_type_flags description)(Int.repr 256)=Int.repr 256 ->
  gateway_object_operation backend gateway_api_generic_alloc[class;Vlong Int64.zero]
    before world result after next observed ->result<>Vnullptr ->
  exists object ticket,result=Vptr object Ptrofs.zero /\~Mem.valid_block before object /\
    gateway_objects_ready(python next)(objects next)after /\instances next result=Some class /\
    types next class=Some description /\default_allocator next class /\
    gateway_object_values(objects next)result=Some gateway_outcome_object /\
    gateway_object_private(objects next)result=true /\gateway_reference_created leases world next result ticket /\
    gateway_outcome_private_cell python owned after next object /\Mem.load Mptr after object 16=Some Vnullptr /\
    gateway_objects_frame(python world)(objects world)(python next)(objects next)[] /\
    gateway_object_privacy_frame(python world)(objects world)(python next)(objects next)[].
Proof.
  intros READY ROOT TYPE ALLOCATOR SIZE ITEMS IMMUTABLE OPERATION NONNULL.
  destruct(@gateway_outcome_generic_alloc World Event backend python objects types default_allocator instances leases
    owned io native stable runtime before world class description result after next observed
    READY ROOT TYPE ALLOCATOR SIZE ITEMS IMMUTABLE OPERATION)as[_[_[_[NULL|NEW]]]];
    [contradiction|exact NEW].
Qed.

Theorem gateway_outcome_data_store {World:Type}(python:World->python_world)objects owned before world object data :
  @gateway_objects_ready(python world)(objects world)before ->
  gateway_outcome_private_cell python owned before world object ->
  (exists data_block data_offset,data=Vptr data_block data_offset) ->
  exists after,Mem.store Mptr before object 16 data=Some after /\
    gateway_objects_ready(python world)(objects world)after /\
    gateway_outcome_private_cell python owned after world object /\
    Mem.load Mptr after object 16=Some data /\
    Mem.unchanged_on(fun candidate position=>~gateway_outcome_cell_region object candidate position)before after.
Proof.
  intros READY[OWNED[RUNTIME_OWNED[SEPARATE[ACCESS POINTER]]]][data_block[data_offset DATA]];subst data.
  destruct(Mem.valid_access_store before Mptr object 16(Vptr data_block data_offset)ACCESS)as[after STORE].
  exists after;split;[exact STORE|]. split;[eapply gateway_outcome_store_objects_ready;eassumption|].
  split.
  - split;[exact OWNED|]. split;[exact RUNTIME_OWNED|].
    split;[exact SEPARATE|]. split;
      [eapply Mem.store_valid_access_1;eassumption|eapply gateway_store_weak_valid;eassumption].
  - split.
    + pose proof(Mem.load_store_same _ _ _ _ _ _ STORE)as LOAD.
      change(Mem.load Mptr after object 16=Some(Vptr data_block data_offset))in LOAD;exact LOAD.
    + eapply Mem.store_unchanged_on;[exact STORE|].
      intros position RANGE OUTSIDE;apply OUTSIDE;split;[reflexivity|exact RANGE].
Qed.
