(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Allocation authority comes from the actual allocator operation. *)
From Stdlib Require Import ZArith Lia List.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Events Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRegistry GatewayRuntime GatewayThreadRuntime
  GatewayStreamInterface.
Import ListNotations.
Open Scope Z_scope.

Inductive gateway_memory_api:=gateway_malloc_api|gateway_free_api|gateway_memchr_api.
Definition gateway_memory_ident api :ident:=
  match api with gateway_malloc_api=>_malloc|gateway_free_api=>_free|gateway_memchr_api=>_memchr end.
Definition gateway_memory_definition api :option(Ctypes.fundef Clight.function):=
  match gateway_program_definition(gateway_memory_ident api)global_definitions with
  |Some(Gfun(External external types result convention))=>Some(External external types result convention)
  |_=>None end.
Definition gateway_memory_operation {World Event}(backend:gateway_backend World Event)api arguments
    before world result after next observed :Prop:=
  exists definition,gateway_memory_definition api=Some definition /\
    gateway_runtime_operation backend definition arguments before world result after next observed.

Theorem gateway_native_memory_actual_abis :
  gateway_memory_definition gateway_malloc_api=Some(External EF_malloc[tulong](tptr tvoid)cc_default) /\
  gateway_memory_definition gateway_free_api=Some(External EF_free[tptr tvoid]tvoid cc_default) /\
  gateway_memory_definition gateway_memchr_api=Some(External
    (EF_external "memchr"(mksignature[Xptr;Xint;Xlong]Xptr cc_default))
    [tptr tvoid;tint;tulong](tptr tvoid)cc_default).
Proof. repeat split;reflexivity. Qed.

Theorem gateway_allocator_size_cell_abi amount :
  Mptr=Mint64 /\size_chunk Mptr=8 /\Vptrofs(Ptrofs.repr amount)=Vlong(Int64.repr amount).
Proof.
  split;[reflexivity|]. split;[reflexivity|].
  change(Vlong(Int64.repr(Ptrofs.unsigned(Ptrofs.repr amount)))=Vlong(Int64.repr amount)).
  f_equal;rewrite Ptrofs.unsigned_repr_eq.
  change Ptrofs.modulus with Int64.modulus;rewrite<-Int64.unsigned_repr_eq;apply Int64.repr_unsigned.
Qed.

Definition gateway_heap_region(object:block)amount block position :Prop:=
  block=object /\ -8<=position<amount.

(* The negative size cell is the pinned CompCert allocator representation. The
   immutable allocation classification also records the object's actual origin. *)
Definition gateway_heap_block memory object amount :Prop:=
  0<amount<=Int64.max_unsigned /\Mem.load Mint64 memory object(-8)=Some(Vlong(Int64.repr amount)) /\
  Mem.range_perm memory object(-8)amount Cur Freeable.

Record gateway_malloc_receipt(heap_allocation:block->Z->Prop)before after result amount :Type:={
  gateway_malloc_object:block;
  gateway_malloc_pointer:result=Vptr gateway_malloc_object Ptrofs.zero;
  gateway_malloc_fresh:~Mem.valid_block before gateway_malloc_object;
  gateway_malloc_origin:heap_allocation gateway_malloc_object amount;
  gateway_malloc_live:gateway_heap_block after gateway_malloc_object amount;
  gateway_malloc_allocated:exists allocated initialized,
    Mem.alloc before(-8)amount=(allocated,gateway_malloc_object) /\
    Mem.store Mint64 allocated gateway_malloc_object(-8)(Vlong(Int64.repr amount))=Some initialized
}.

Inductive gateway_memchr_result object offset bytes :Values.val->Prop:=
| gateway_memchr_absent:~In Byte.zero bytes ->gateway_memchr_result object offset bytes Vnullptr
| gateway_memchr_present:forall earlier later,
    bytes=earlier++Byte.zero::later ->~In Byte.zero earlier ->
    gateway_memchr_result object offset bytes
      (Vptr object(Ptrofs.add offset(Ptrofs.repr(Z.of_nat(length earlier))))).

(* The backend remains broad for calls lacking their actual ownership/API
   preconditions. NULL allocation, blocked calls and committed loss remain possible. *)
Record gateway_native_memory_runtime {World Event}(backend:gateway_backend World Event)
    (io:Event->option gateway_native_io)(native_private:World->block->Prop)
    (stable_readonly:World->block->Z->Prop)(discipline:option val->mem->World->Prop)
    (heap_allocation:block->Z->Prop) :Prop:={
  gateway_malloc_operation:forall mode before world amount result after next observed,
    discipline mode before world ->0<amount<=Int64.max_unsigned ->
    gateway_memory_operation backend gateway_malloc_api[Vlong(Int64.repr amount)]
      before world result after next observed ->
    discipline mode after next /\gateway_access_retained native_private stable_readonly before world next /\
    gateway_native_frame native_private stable_readonly gateway_native_no_output world before after /\
    io observed=None /\
    (result=Vnullptr \/exists receipt:gateway_malloc_receipt heap_allocation before after result amount,
      native_private next(gateway_malloc_object _ _ _ _ _ receipt));
  gateway_free_operation:forall mode before world object amount result after next observed,
    discipline mode before world ->native_private world object ->heap_allocation object amount ->
    gateway_heap_block before object amount ->
    gateway_memory_operation backend gateway_free_api[Vptr object Ptrofs.zero]
      before world result after next observed ->
    result=Vundef /\discipline mode after next /\
    gateway_access_retained native_private stable_readonly before world next /\
    gateway_native_frame native_private stable_readonly(gateway_heap_region object amount)world before after /\
    (exists freed,Mem.free before object(-8)amount=Some freed) /\
    (forall position kind permission,-8<=position<amount->~Mem.perm after object position kind permission) /\
    io observed=None;
  gateway_memchr_operation:forall mode before world object offset amount bytes result after next observed,
    discipline mode before world ->
    (native_private world object \/forall position,
      Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+amount->stable_readonly world object position) ->
    gateway_native_pointer before object offset amount Readable ->
    Mem.loadbytes before object(Ptrofs.unsigned offset)amount=Some(inj_bytes bytes) ->
    gateway_memory_operation backend gateway_memchr_api
      [Vptr object offset;Vint Int.zero;Vlong(Int64.repr amount)]before world result after next observed ->
    gateway_memchr_result object offset bytes result /\discipline mode after next /\
    gateway_access_retained native_private stable_readonly before world next /\
    gateway_native_frame native_private stable_readonly gateway_native_no_output world before after /\io observed=None
}.

Theorem gateway_memory_actual_operation {World Event}(backend:gateway_backend World Event)ge api
    external types result_type convention arguments continuation before world result after next observed :
  gateway_memory_definition api=Some(External external types result_type convention) ->
  gateway_step backend ge
    (gateway_live(Callstate(External external types result_type convention)arguments continuation before)world)
    (gateway_primitive observed)(gateway_live(Returnstate result continuation after)next) ->
  gateway_memory_operation backend api arguments before world result after next observed.
Proof.
  intros DEFINITION STEP;inversion STEP;subst;eexists;split;[exact DEFINITION|].
  cbn[gateway_runtime_operation];eassumption.
Qed.

Theorem gateway_memchr_null_excludes_zero object offset bytes :
  gateway_memchr_result object offset bytes Vnullptr ->~In Byte.zero bytes.
Proof. intro RESULT;inversion RESULT;subst;try assumption;discriminate. Qed.

Theorem gateway_malloc_has_free_authority heap_allocation before after result amount
    (receipt:gateway_malloc_receipt heap_allocation before after result amount) :
  heap_allocation(gateway_malloc_object _ _ _ _ _ receipt)amount /\
  gateway_heap_block after(gateway_malloc_object _ _ _ _ _ receipt)amount.
Proof. split;[exact(gateway_malloc_origin _ _ _ _ _ receipt)|exact(gateway_malloc_live _ _ _ _ _ receipt)]. Qed.
