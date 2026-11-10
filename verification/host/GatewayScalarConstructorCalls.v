(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Each real scalar constructor keeps its buffer and mints its own root lease. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayObjectDiscipline
  GatewayRootLeases GatewayObjectThreads GatewayValueOwnership GatewayValueEntry GatewayValueContext GatewayValueStack
  GatewayScalarLength GatewayScalarPayloadMemory GatewayScalarTerminate GatewayScalarConstructorMemory
  GatewayRegistry GatewayOperations GatewayReadonly GatewayRuntime GatewayFramedRuntime GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.

Definition gateway_scalar_private_ready {World}python objects detached native_stable heap_allocation scalar slots stream_block stream_offset
    initial readonly original size object bytes memory world :Prop:=
  @gateway_scalar_terminated_ready World(fun current candidate=>gateway_native_private(python current)candidate)native_stable
    (gateway_python_discipline python objects detached)heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes memory world /\
    (forall candidate position,readonly candidate position ->gateway_native_private(python world)candidate).

Lemma gateway_scalar_private_side {World}python objects detached stable heap_allocation scalar slots stream_block stream_offset
    initial readonly original size object bytes memory world :
  @gateway_scalar_private_ready World python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly
    original size object bytes memory world ->gateway_python_discipline python objects detached None memory world.
Proof. intros[[[[_[[SIDE HEAP]SEPARATE]]PAYLOAD]TERMINATED]READONLY];exact SIDE. Qed.

Lemma gateway_scalar_private_ambient {World Event}(backend:gateway_backend World Event)
    python objects detached io stable thread_errno
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    heap_allocation scalar slots stream_block stream_offset initial readonly original size object bytes :
  gateway_ambient_closed backend(gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block
    stream_offset initial readonly original size object bytes).
Proof.
  intros before world after next[READY PRIVATE]INTERFERENCE;split.
  - eapply gateway_scalar_terminated_ambient;[exact runtime|exact READY|exact INTERFERENCE].
  - destruct READY as[[[[[[[SIDE[STREAM[STABLE[INPUT FRAME]]]]SLOTS]TAG]SIZE][HEAP REST]]PAYLOAD]TERMINATED].
    destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ SIDE INTERFERENCE)as[_[[RETAIN_NATIVE RETAIN_STABLE]STEP_FRAME]].
    intros candidate position READ;apply RETAIN_NATIVE;
      [exact(gateway_value_readonly_live _ _ _ _ _ INPUT candidate position READ)|apply PRIVATE with(position:=position);exact READ].
Qed.

Section ConstructorCalls.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (python:World->python_world)(objects:World->gateway_object_heap)
  (detached:Values.val->Memory.mem->World->Prop)(io:Event->option gateway_native_io)
  (stable:World->block->Z->Prop)(thread_errno:World->int)(heap_allocation:block->Z->Prop)
  (decimal_float:list Z->Floats.float->Prop)(leases:World->nat->Values.val->Prop).
Let native:=fun current candidate=>gateway_native_private(python current)candidate.
Let base:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno)
  (constructors:gateway_objects_runtime backend python objects decimal_float)
  (roots:gateway_root_lease_runtime backend python objects decimal_float leases)
  (object_threads:gateway_object_thread_contract backend native stable base heap_allocation python objects leases).

Theorem gateway_actual_scalar_constructor_storage api definition arguments value kind scalar slots stream_block stream_offset initial
    readonly original size object bytes before world events result after next :
  gateway_object_api_definition api=Some definition ->
  (forall memory current,gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block
    stream_offset initial readonly original size object bytes memory current ->
    gateway_constructor_request decimal_float(objects current)memory api arguments value /\
    gateway_constructor_roots(python current)(objects current)api arguments) ->
  gateway_object_children value=[] ->gateway_object_kind value=Some kind ->GatewayReferences.gateway_destructor_kind kind ->
  gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly
    original size object bytes before world ->
  gateway_steps backend ge(gateway_live(Callstate definition arguments Kstop before)world)events
    (gateway_live(Returnstate result Kstop after)next) ->result<>Vnullptr ->
  exists ticket,gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial
    readonly original size object bytes after next /\
    gateway_held_values python objects decimal_float leases
      [{|gateway_held_ticket:=ticket;gateway_held_object:=result;gateway_held_view:=gateway_held_scalar_value value|}]next.
Proof.
  intros DEFINITION REQUEST CHILDREN KIND SAFE INPUT RUN NONNULL.
  pose proof DEFINITION as EXTERNAL;unfold gateway_object_api_definition in EXTERNAL.
  destruct(gateway_program_definition(gateway_object_api_ident api)global_definitions)as[global|]eqn:GLOBAL;[|discriminate].
  destruct global as[function|variable];[|discriminate].
  destruct function as[function|external types result_type convention];[discriminate|].
  inversion EXTERNAL;subst definition.
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ _ _ _ _ _ _ RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &PENDING &PREFIX &OPERATION &SUFFIX).
  pose proof(gateway_scalar_private_ambient backend python objects detached io stable thread_errno runtime heap_allocation scalar slots
    stream_block stream_offset initial readonly original size object bytes)as CLOSED.
  pose proof(gateway_pending_run_ready backend ge _ CLOSED
    (Callstate(External external types result_type convention)arguments Kstop before)before world prefix called called_world
    INPUT PENDING PREFIX)as CALLED.
  destruct(REQUEST _ _ CALLED)as[CALL_REQUEST CALL_ROOTS].
  assert(SIDE:base None called called_world)by(eapply gateway_scalar_private_side;exact CALLED).
  assert(API:gateway_object_operation backend api arguments called called_world result changed changed_world observed).
  { eexists;split;[exact DEFINITION|exact OPERATION]. }
  pose proof(gateway_runtime_constructor _ _ _ _ constructors _ _ _ _ _ _ _ _ _ SIDE CALL_REQUEST CALL_ROOTS API NONNULL)as RETURN.
  destruct(gateway_actual_constructor_held_scalar backend python objects decimal_float leases constructors roots
    api arguments called called_world result changed changed_world observed value kind SIDE CALL_REQUEST CALL_ROOTS API NONNULL
    CHILDREN KIND SAFE)as(ticket &CREATED &HELD).
  set(captured:={|gateway_held_ticket:=ticket;gateway_held_object:=result;gateway_held_view:=gateway_held_scalar_value value|}).
  set(ready:=fun memory current=>gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block
    stream_offset initial readonly original size object bytes memory current /\
    gateway_held_values python objects decimal_float leases[captured]current).
  assert(AFTER:ready changed changed_world).
  { split;[|exact HELD]. eapply gateway_scalar_constructor_retains;[exact runtime|exact(proj1 CALLED)|exact(proj2 CALLED)|exact RETURN]. }
  assert(READY_CLOSED:gateway_ambient_closed backend ready).
  { intros first current last following[PRIVATE HOLD]INTERFERENCE;split.
    - eapply CLOSED;eassumption.
    - eapply gateway_held_values_effect;[exact roots|exact HOLD|].
      eapply gateway_object_thread_ambient;[exact object_threads| |exact INTERFERENCE].
      eapply gateway_scalar_private_side;exact PRIVATE. }
  pose proof(gateway_readonly_run_side backend ge ready READY_CLOSED(Returnstate result Kstop changed)changed_world suffix result
    after next I AFTER SUFFIX)as FINAL.
  exists ticket;exact FINAL.
Qed.

End ConstructorCalls.
