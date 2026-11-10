(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Each actual thread operation retains current native root leases. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Memdata Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayRuntimeABI GatewayThreadRuntime
  GatewayStreamInterface GatewayNativeMemory GatewayPython GatewayObjects GatewayReferences GatewayValue
  GatewayValueFrame GatewayRootLeases GatewayGraphSnapshots.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Inductive gateway_held_description:=
| gateway_held_wire_value(value:gateway_wire_value)
| gateway_held_scalar_value(value:gateway_object_value)
| gateway_held_graph_value(value:gateway_wire_value)(initial:gateway_object_heap).

Definition gateway_held_description_holds decimal_float heap object description :Prop:=
  match description with
  |gateway_held_wire_value value=>gateway_value_heap decimal_float heap object value
  |gateway_held_scalar_value value=>gateway_object_values heap object=Some value /\gateway_object_children value=[]
  |gateway_held_graph_value value initial=>gateway_value_heap decimal_float heap object value /\
    gateway_destructible initial object /\gateway_graph_snapshot initial heap object
  end.

Record gateway_held_value :Type:={
  gateway_held_ticket:nat;
  gateway_held_object:Values.val;
  gateway_held_view:gateway_held_description
}.

Definition gateway_held_values {World}python objects decimal_float(leases:World->nat->Values.val->Prop)
    (held:list gateway_held_value)world :Prop:=
  Forall(fun value=>leases world(gateway_held_ticket value)(gateway_held_object value) /\
    gateway_rooted(python world)(objects world)(gateway_held_object value) /\
    gateway_private_tree(objects world)(gateway_held_object value) /\
    gateway_destructible(objects world)(gateway_held_object value) /\
    gateway_held_description_holds decimal_float(objects world)(gateway_held_object value)(gateway_held_view value))held.

Definition gateway_object_thread_effect {World}python objects(leases:World->nat->Values.val->Prop)world next :Prop:=
  gateway_leases_retained leases world next /\
  gateway_objects_frame(python world)(objects world)(python next)(objects next)[] /\
  gateway_object_privacy_frame(python world)(objects world)(python next)(objects next)[].

Section ObjectThreads.
Context {World Event}(backend:gateway_backend World Event)
  (io:Event->option gateway_native_io)(native_private:World->block->Prop)
  (stable_readonly:World->block->Z->Prop)(base:option Values.val->Memory.mem->World->Prop)
  (thread_errno:World->int)(heap_allocation:block->Z->Prop).
Context(python:World->python_world)(objects:World->gateway_object_heap)
  (decimal_float:list Z->Floats.float->Prop)(leases:World->nat->Values.val->Prop).
Context(roots:gateway_root_lease_runtime backend python objects decimal_float leases).

(* Only calls meeting their real native-pointer, mode and bound preconditions
   enter this relation. Other primitive returns stay broad in GatewayMachine. *)
Inductive gateway_object_thread_operation :
    option Values.val->Memory.mem->World->option Values.val->Memory.mem->World->Prop:=
| gateway_object_thread_save:forall before world result after next observed,
    base None before world ->gateway_runtime_operation backend gateway_save_thread_definition[]
      before world result after next observed ->gateway_object_thread_operation None before world(Some result)after next
| gateway_object_thread_restore:forall saved before world result after next observed,
    base(Some saved)before world ->gateway_runtime_operation backend gateway_restore_thread_definition[saved]
      before world result after next observed ->gateway_object_thread_operation(Some saved)before world None after next
| gateway_object_thread_errno:forall mode before world result after next observed,
    base mode before world ->gateway_runtime_operation backend gateway_errno_location_definition[]
      before world result after next observed ->gateway_object_thread_operation mode before world mode after next
| gateway_object_thread_clock:forall before world object offset result after next observed,
    base None before world ->native_private world object ->gateway_native_pointer before object offset 16 Writable ->
    gateway_runtime_operation backend gateway_clock_gettime_definition[Vint Int.one;Vptr object offset]
      before world result after next observed ->gateway_object_thread_operation None before world None after next
| gateway_object_thread_poll:forall saved before world object offset result after next observed,
    base(Some saved)before world ->native_private world object ->gateway_native_pointer before object offset 8 Writable ->
    gateway_runtime_operation backend gateway_poll_definition[Vptr object offset;Vlong Int64.one;Vint(Int.repr 100)]
      before world result after next observed ->gateway_object_thread_operation(Some saved)before world(Some saved)after next
| gateway_object_thread_send:forall mode before world descriptor object offset amount result after next observed,
    base mode before world ->(native_private world object \/forall position,
      Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+amount ->stable_readonly world object position) ->
    0<amount<=65536 ->gateway_native_pointer before object offset amount Readable ->
    gateway_runtime_operation backend gateway_send_definition
      [Vint descriptor;Vptr object offset;Vlong(Int64.repr amount);Vint(Int.repr 16384)]
      before world result after next observed ->gateway_object_thread_operation mode before world mode after next
| gateway_object_thread_receive:forall saved before world descriptor object offset amount result after next observed,
    base(Some saved)before world ->native_private world object ->0<amount<=65536 ->
    gateway_native_pointer before object offset amount Writable ->
    gateway_runtime_operation backend gateway_receive_definition
      [Vint descriptor;Vptr object offset;Vlong(Int64.repr amount);Vint Int.zero]
      before world result after next observed ->gateway_object_thread_operation(Some saved)before world(Some saved)after next
| gateway_object_thread_signals:forall before world after next observed,
    base None before world ->gateway_runtime_operation backend gateway_check_signals_definition[]
      before world(Vint Int.zero)after next observed ->gateway_object_thread_operation None before world None after next
| gateway_object_thread_volatile:forall mode before world pointer result after next observed,
    base mode before world ->GatewayMachine.gateway_builtin backend(EF_vload Mint32)[tptr(tvolatile tint)][pointer]
      before world result after next observed ->gateway_object_thread_operation mode before world mode after next
| gateway_object_thread_malloc:forall mode before world amount result after next observed,
    base mode before world ->0<amount<=Int64.max_unsigned ->
    gateway_memory_operation backend gateway_malloc_api[Vlong(Int64.repr amount)]before world result after next observed ->
    gateway_object_thread_operation mode before world mode after next
| gateway_object_thread_free:forall mode before world object amount result after next observed,
    base mode before world ->native_private world object ->heap_allocation object amount ->
    gateway_heap_block before object amount ->gateway_memory_operation backend gateway_free_api[Vptr object Ptrofs.zero]
      before world result after next observed ->gateway_object_thread_operation mode before world mode after next
| gateway_object_thread_memchr:forall mode before world object offset amount bytes result after next observed,
    base mode before world ->(native_private world object \/forall position,
      Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+amount ->stable_readonly world object position) ->
    gateway_native_pointer before object offset amount Readable ->
    Mem.loadbytes before object(Ptrofs.unsigned offset)amount=Some(inj_bytes bytes) ->
    gateway_memory_operation backend gateway_memchr_api[Vptr object offset;Vint Int.zero;Vlong(Int64.repr amount)]
      before world result after next observed ->gateway_object_thread_operation mode before world mode after next.

(* The current invocation's owned leases and exact private builtin graphs are
   retained per operation. Public graphs and other owners' refcounts may change. *)
Record gateway_object_thread_contract :Prop:={
  gateway_object_thread_ambient:forall mode before world after next,
    base mode before world ->gateway_interference backend before world after next ->
    gateway_object_thread_effect python objects leases world next;
  gateway_object_thread_return:forall mode before world after_mode after next,
    gateway_object_thread_operation mode before world after_mode after next ->
    gateway_object_thread_effect python objects leases world next
}.

Lemma gateway_held_values_effect held world next :
  gateway_held_values python objects decimal_float leases held world ->
  gateway_object_thread_effect python objects leases world next ->
  gateway_held_values python objects decimal_float leases held next.
Proof.
  intros HELD[RETAINED[FRAME PRIVACY]];apply Forall_forall;intros value MEMBER.
  apply Forall_forall with(x:=value)in HELD;[|exact MEMBER].
  destruct HELD as[LEASE[ROOTED[PRIVATE[DESTRUCTIBLE VALUE]]]].
  assert(NEXT_LEASE:leases next(gateway_held_ticket value)(gateway_held_object value))by(apply RETAINED;exact LEASE).
  pose proof(gateway_lease_rooted backend python objects decimal_float leases roots _ _ _ LEASE)as ROOT.
  pose proof(gateway_lease_rooted backend python objects decimal_float leases roots _ _ _ NEXT_LEASE)as NEXT.
  destruct(gateway_private_tree_preserved _ _ _ _ _ PRIVATE DESTRUCTIBLE ROOT NEXT FRAME PRIVACY)
    as[AFTER_PRIVATE AFTER_DESTRUCTIBLE].
  split;[exact NEXT_LEASE|]. split;[exact NEXT|]. split;[exact AFTER_PRIVATE|]. split;[exact AFTER_DESTRUCTIBLE|].
  destruct(gateway_held_view value)as[wire|scalar|wire initial];cbn[gateway_held_description_holds]in VALUE|-*.
  - eapply gateway_value_heap_retained;eassumption.
  - destruct VALUE as[LOOKUP CHILDREN];split;[|exact CHILDREN].
    eapply FRAME;[exact ROOT|exact NEXT|apply PRIVATE;constructor|intro BAD;inversion BAD|exact LOOKUP].
  - destruct VALUE as[WIRE[INITIAL SNAPSHOT]];split.
    + eapply gateway_value_heap_retained;[exact WIRE|exact PRIVATE|exact ROOT|exact NEXT|exact FRAME|exact PRIVACY].
    + split;[exact INITIAL|]. eapply gateway_graph_snapshot_retained;
        [exact PRIVATE|exact DESTRUCTIBLE|exact ROOT|exact NEXT|exact FRAME|exact PRIVACY|exact SNAPSHOT].
Qed.

Definition gateway_held_discipline held mode memory world :Prop:=
  base mode memory world /\gateway_held_values python objects decimal_float leases held world.

Theorem gateway_thread_with_held_values held
    (runtime:gateway_thread_runtime backend io native_private stable_readonly base thread_errno)
    (contract:gateway_object_thread_contract) :
  gateway_thread_runtime backend io native_private stable_readonly(gateway_held_discipline held)thread_errno.
Proof.
  constructor.
  - intros mode before world after next[SIDE HELD]INTERFERENCE.
    destruct(gateway_thread_ambient _ _ _ _ _ _ runtime mode _ _ _ _ SIDE INTERFERENCE)
      as[NEXT OTHERS]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_held_values_effect;[exact HELD|].
    eapply gateway_object_thread_ambient;[exact contract|exact SIDE|exact INTERFERENCE].
  - intros mode before world object[SIDE HELD]FRESH.
    eapply gateway_thread_fresh_native;[exact runtime|exact SIDE|exact FRESH].
  - intros mode before world object position[SIDE HELD]NATIVE.
    eapply gateway_thread_native_stable;[exact runtime|exact SIDE|exact NATIVE].
  - intros mode before world after object low high[SIDE HELD]ALLOC;split;[|exact HELD].
    eapply gateway_thread_native_alloc;[exact runtime|exact SIDE|exact ALLOC].
  - intros mode before world after object low high[SIDE HELD]NATIVE FREE;split;[|exact HELD].
    eapply gateway_thread_native_free;[exact runtime|exact SIDE|exact NATIVE|exact FREE].
  - intros mode before world after object offset chunk value[SIDE HELD]NATIVE STORE;split;[|exact HELD].
    eapply gateway_thread_native_store;[exact runtime|exact SIDE|exact NATIVE|exact STORE].
  - intros before world result after next observed[SIDE HELD]OPERATION.
    destruct(gateway_save_thread_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ SIDE OPERATION)
      as[POINTER[NEXT OTHERS]]. split;[exact POINTER|]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_held_values_effect;[exact HELD|]. eapply gateway_object_thread_return;[exact contract|].
    eapply gateway_object_thread_save;eassumption.
  - intros saved before world result after next observed[SIDE HELD]OPERATION.
    destruct(gateway_restore_thread_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ SIDE OPERATION)
      as[NEXT OTHERS]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_held_values_effect;[exact HELD|]. eapply gateway_object_thread_return;[exact contract|].
    eapply gateway_object_thread_restore;eassumption.
  - intros mode before world result after next observed[SIDE HELD]OPERATION.
    destruct(gateway_errno_location_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ SIDE OPERATION)
      as(object &offset &RESULT &POINTER &LOAD &NATIVE &STABLE &NEXT &OTHERS).
    exists object,offset;split;[exact RESULT|]. split;[exact POINTER|]. split;[exact LOAD|].
    split;[exact NATIVE|]. split;[exact STABLE|]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_held_values_effect;[exact HELD|]. eapply gateway_object_thread_return;[exact contract|].
    eapply gateway_object_thread_errno;eassumption.
  - intros before world object offset result after next observed[SIDE HELD]NATIVE POINTER OPERATION.
    destruct(gateway_clock_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ SIDE NATIVE POINTER OPERATION)
      as(status &RESULT &CONTENT &NEXT &OTHERS).
    exists status;split;[exact RESULT|]. split;[exact CONTENT|]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_held_values_effect;[exact HELD|]. eapply gateway_object_thread_return;[exact contract|].
    eapply gateway_object_thread_clock;eassumption.
  - intros saved before world object offset result after next observed[SIDE HELD]NATIVE POINTER OPERATION.
    destruct(gateway_poll_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ SIDE NATIVE POINTER OPERATION)
      as(status &RESULT &NEXT &OTHERS).
    exists status;split;[exact RESULT|]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_held_values_effect;[exact HELD|]. eapply gateway_object_thread_return;[exact contract|].
    eapply gateway_object_thread_poll;eassumption.
  - intros mode before world descriptor object offset amount result after next observed
      [SIDE HELD]READABLE AMOUNT POINTER OPERATION.
    destruct(gateway_send_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ _ _
      SIDE READABLE AMOUNT POINTER OPERATION)as(count &bytes &RANGE &RESULT &COUNT &LOAD &EVENT &NEXT &OTHERS).
    exists count,bytes;split;[exact RANGE|]. split;[exact RESULT|]. split;[exact COUNT|]. split;[exact LOAD|].
    split;[exact EVENT|]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_held_values_effect;[exact HELD|]. eapply gateway_object_thread_return;[exact contract|].
    eapply gateway_object_thread_send;eassumption.
  - intros saved before world descriptor object offset amount result after next observed
      [SIDE HELD]NATIVE AMOUNT POINTER OPERATION.
    destruct(gateway_receive_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ _ _
      SIDE NATIVE AMOUNT POINTER OPERATION)as(count &bytes &RANGE &RESULT &COUNT &LOAD &EVENT &NEXT &OTHERS).
    exists count,bytes;split;[exact RANGE|]. split;[exact RESULT|]. split;[exact COUNT|]. split;[exact LOAD|].
    split;[exact EVENT|]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_held_values_effect;[exact HELD|]. eapply gateway_object_thread_return;[exact contract|].
    eapply gateway_object_thread_receive;eassumption.
  - intros before world result after next observed[SIDE HELD]OPERATION.
    destruct(gateway_check_signals_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ SIDE OPERATION)
      as(status &RESULT &SUCCESS &EVENT).
    exists status;split;[exact RESULT|]. split;[|exact EVENT]. intros ZERO;subst status.
    destruct(SUCCESS eq_refl)as[NEXT OTHERS]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_held_values_effect;[exact HELD|]. eapply gateway_object_thread_return;[exact contract|].
    eapply gateway_object_thread_signals;[exact SIDE|rewrite<-RESULT;exact OPERATION].
  - intros mode before world pointer result after next observed[SIDE HELD]OPERATION.
    destruct(gateway_volatile_int_load _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ SIDE OPERATION)
      as[RESULT[NEXT OTHERS]]. split;[exact RESULT|]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_held_values_effect;[exact HELD|]. eapply gateway_object_thread_return;[exact contract|].
    eapply gateway_object_thread_volatile;eassumption.
Qed.

Theorem gateway_memory_with_held_values held
    (runtime:gateway_native_memory_runtime backend io native_private stable_readonly base heap_allocation)
    (contract:gateway_object_thread_contract) :
  gateway_native_memory_runtime backend io native_private stable_readonly(gateway_held_discipline held)heap_allocation.
Proof.
  constructor.
  - intros mode before world amount result after next observed[SIDE HELD]AMOUNT OPERATION.
    destruct(gateway_malloc_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ SIDE AMOUNT OPERATION)
      as[NEXT OTHERS]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_held_values_effect;[exact HELD|]. eapply gateway_object_thread_return;[exact contract|].
    eapply gateway_object_thread_malloc;eassumption.
  - intros mode before world object amount result after next observed[SIDE HELD]NATIVE AUTHORITY BLOCK OPERATION.
    destruct(gateway_free_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ SIDE NATIVE AUTHORITY BLOCK OPERATION)
      as[RESULT[NEXT OTHERS]]. split;[exact RESULT|]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_held_values_effect;[exact HELD|]. eapply gateway_object_thread_return;[exact contract|].
    eapply gateway_object_thread_free;eassumption.
  - intros mode before world object offset amount bytes result after next observed
      [SIDE HELD]READABLE POINTER LOAD OPERATION.
    destruct(gateway_memchr_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ _ _
      SIDE READABLE POINTER LOAD OPERATION)as[RESULT[NEXT OTHERS]].
    split;[exact RESULT|]. split;[|exact OTHERS]. split;[exact NEXT|].
    eapply gateway_held_values_effect;[exact HELD|]. eapply gateway_object_thread_return;[exact contract|].
    eapply gateway_object_thread_memchr;eassumption.
Qed.

End ObjectThreads.
