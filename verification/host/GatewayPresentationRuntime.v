(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Presentation uses actual tuple/reference effects and an observed callback result. *)
From Stdlib Require Import ZArith List Strings.String.
From compcert Require Import Integers AST Values Memory Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayMachine GatewayRuntime GatewayPython GatewayObjects
  GatewayReferenceRuntime GatewayAttachedReferences.
Import ListNotations.
Open Scope Z_scope.

Inductive gateway_presentation_api:=
|gateway_presentation_tuple_new|gateway_presentation_tuple_set|gateway_presentation_call|gateway_presentation_tuple_release.
Definition gateway_presentation_ident api:=match api with
|gateway_presentation_tuple_new=>_PyTuple_New|gateway_presentation_tuple_set=>_PyTuple_SetItem
|gateway_presentation_call=>_PyObject_CallObject|gateway_presentation_tuple_release=>_Py_DecRef end.
Definition gateway_presentation_definition api:option(Ctypes.fundef Clight.function):=
  match gateway_program_definition(gateway_presentation_ident api)global_definitions with
  |Some(Gfun(External external types result convention))=>Some(External external types result convention)
  |_=>None end.
Definition gateway_presentation_operation {World Event}(backend:gateway_backend World Event)api arguments
    before world result after next observed:Prop:=
  exists definition,gateway_presentation_definition api=Some definition /\
    gateway_runtime_operation backend definition arguments before world result after next observed.

Theorem gateway_presentation_actual_abis:
  gateway_presentation_definition gateway_presentation_tuple_new=Some(External
    (EF_external "PyTuple_New"(mksignature[Xlong]Xptr cc_default))[tlong](tptr(Tstruct __object noattr))cc_default) /\
  gateway_presentation_definition gateway_presentation_tuple_set=Some(External
    (EF_external "PyTuple_SetItem"(mksignature[Xptr;Xlong;Xptr]Xint cc_default))
      [tptr(Tstruct __object noattr);tlong;tptr(Tstruct __object noattr)]tint cc_default) /\
  gateway_presentation_definition gateway_presentation_call=Some(External
    (EF_external "PyObject_CallObject"(mksignature[Xptr;Xptr]Xptr cc_default))
      [tptr(Tstruct __object noattr);tptr(Tstruct __object noattr)](tptr(Tstruct __object noattr))cc_default).
Proof. repeat split;reflexivity. Qed.

Definition gateway_presentation_immutable heap pointer:Prop:=
  (exists characters,gateway_object_values heap pointer=Some(gateway_unicode_object characters)) \/
  gateway_object_values heap pointer=Some gateway_none_object.

Definition gateway_presentation_owned_region {World}(storage:World->block->Prop)world memory(protected:block->Z->Prop):Prop:=
  forall object position,protected object position->storage world object /\Mem.perm memory object position Cur Readable.

(* Storage denotes the current source's private native allocations. It does not
   grant a frame on callback-writable application globals or public object cells. *)
Record gateway_presentation_frame {World}(python:World->python_world)(objects:World->gateway_object_heap)
    (storage:World->block->Prop)(protected:block->Z->Prop)before world after next:Prop:={
  gateway_presentation_attached:gateway_objects_attached(python next)(objects next)after;
  gateway_presentation_values:gateway_objects_frame(python world)(objects world)(python next)(objects next)[];
  gateway_presentation_privacy:gateway_object_privacy_frame(python world)(objects world)(python next)(objects next)[];
  gateway_presentation_memory:Mem.unchanged_on protected before after;
  gateway_presentation_storage:forall object position,protected object position->storage next object
}.

Definition gateway_presentation_same_counts before after:Prop:=
  forall pointer,python_native_strong after pointer=python_native_strong before pointer.
Definition gateway_presentation_debit before after pointer:Prop:=
  python_native_strong before pointer=S(python_native_strong after pointer) /\
  forall other,other<>pointer->python_native_strong after other=python_native_strong before other.

(* The count projection is the fixed source-token selection. Other invocation
   roots and SDK graph edges are not silently included in this C-owned pool. *)
Record gateway_presentation_runtime {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(objects:World->gateway_object_heap)
    (tuples:World->Values.val->option(list(option Values.val)))
    (storage:World->block->Prop):Prop:={
  gateway_presentation_tuple_ambient:forall before world after next tuple contents,
    gateway_objects_attached(python world)(objects world)before->
    tuples world tuple=Some contents->(0<python_native_strong(python world)tuple)%nat->
    gateway_interference backend before world after next->
    tuples next tuple=Some contents /\python_strong(python next)tuple=python_strong(python world)tuple;
  gateway_presentation_new_operation:forall before world result after next observed protected,
    gateway_objects_ready(python world)(objects world)before->
    gateway_presentation_owned_region storage world before protected->
    gateway_presentation_operation backend gateway_presentation_tuple_new[Vlong Int64.one]before world result after next observed->
    gateway_presentation_frame python objects storage protected before world after next /\
    (result=Vnullptr /\python_pending(python next)<>None /\gateway_presentation_same_counts(python world)(python next) \/
     (exists object offset,result=Vptr object offset) /\
       gateway_objects_ready(python next)(objects next)after /\
       gateway_reference_credit(python world)(python next)result /\
       python_strong(python world)result=0%nat /\python_strong(python next)result=1%nat /\
       tuples next result=Some[None]);
  gateway_presentation_set_operation:forall before world tuple child result after next observed protected,
    gateway_objects_ready(python world)(objects world)before->
    gateway_presentation_owned_region storage world before protected->
    tuples world tuple=Some[None]->python_live(python world)tuple->
    (0<python_native_strong(python world)tuple)%nat->python_strong(python world)tuple=1%nat->
    python_live(python world)child->(0<python_native_strong(python world)child)%nat->
    gateway_presentation_immutable(objects world)child->
    gateway_presentation_operation backend gateway_presentation_tuple_set[tuple;Vlong Int64.zero;child]
      before world result after next observed->
    result=Vint Int.zero /\gateway_objects_ready(python next)(objects next)after /\
    gateway_presentation_frame python objects storage protected before world after next /\
    gateway_presentation_debit(python world)(python next)child /\
    tuples next tuple=Some[Some child] /\
    python_strong(python next)child=python_strong(python world)child /\
    python_strong(python next)tuple=1%nat;
  gateway_presentation_call_operation:forall before world callable tuple child result after next observed protected,
    gateway_objects_ready(python world)(objects world)before->
    gateway_presentation_owned_region storage world before protected->
    python_live(python world)callable->python_live(python world)tuple->
    (0<python_native_strong(python world)callable)%nat->(0<python_native_strong(python world)tuple)%nat->
    tuples world tuple=Some[Some child]->gateway_presentation_immutable(objects world)child->
    gateway_presentation_operation backend gateway_presentation_call[callable;tuple]before world result after next observed->
    gateway_presentation_frame python objects storage protected before world after next /\
    tuples next tuple=Some[Some child] /\
    (result=Vnullptr /\python_pending(python next)<>None /\gateway_presentation_same_counts(python world)(python next) \/
     (exists object offset,result=Vptr object offset) /\
       gateway_objects_ready(python next)(objects next)after /\python_live(python next)result /\
       gateway_reference_credit(python world)(python next)result);
  gateway_presentation_release_operation:forall before world tuple contents result after next observed protected,
    gateway_objects_attached(python world)(objects world)before->
    gateway_presentation_owned_region storage world before protected->
    tuples world tuple=Some contents->
    (contents=[None] \/exists child,contents=[Some child] /\gateway_presentation_immutable(objects world)child)->
    (0<python_native_strong(python world)tuple)%nat->
    gateway_presentation_operation backend gateway_presentation_tuple_release[tuple]before world result after next observed->
    gateway_presentation_frame python objects storage protected before world after next /\
    python_pending(python next)=python_pending(python world) /\gateway_presentation_debit(python world)(python next)tuple
}.
