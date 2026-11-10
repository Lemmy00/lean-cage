(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A scalar constructor retains its actual buffer and source references. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayMachine GatewayPython GatewayObjects GatewayReferences
  GatewayObjectDiscipline GatewayObjectThreads GatewayScalarConstructorCalls GatewayScalarConstructorMemory GatewayScalarTerminate
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceConstructors GatewayReferenceThreads
  GatewayObjectExecution GatewayOperations GatewayReadonly GatewayFramedRuntime GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_actual_scalar_storage {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects detached io stable thread_errno heap_allocation decimal_float
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    ledger owner held api definition arguments value kind scalar slots stream_block stream_offset initial
    readonly original size object bytes before world events result after next:
  gateway_reference_ledger_well_formed ledger->gateway_reference_take owner(gateway_reference_entries ledger)=None->
  gateway_reference_scope python objects decimal_float ledger held world->
  gateway_object_api_definition api=Some definition->
  (forall memory current,gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block
    stream_offset initial readonly original size object bytes memory current->
    gateway_constructor_request decimal_float(objects current)memory api arguments value /\
    gateway_constructor_roots(python current)(objects current)api arguments)->
  gateway_object_children value=[]->gateway_object_kind value=Some kind->gateway_destructor_kind kind->
  gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset
    initial readonly original size object bytes before world->
  gateway_steps backend ge(gateway_live(Callstate definition arguments Kstop before)world)events
    (gateway_live(Returnstate result Kstop after)next)->result<>Vnullptr->
  exists final,
    gateway_reference_apply(gateway_reference_mint owner result)(gateway_reference_valid ledger)=
      gateway_reference_valid final /\gateway_reference_ledger_well_formed final /\
    gateway_reference_owns final owner(gateway_reference_next ledger)result /\
    gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset
      initial readonly original size object bytes after next /\
    gateway_reference_scope python objects decimal_float final
      (held++[{|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=result;
        gateway_held_view:=gateway_held_scalar_value value|}])next.
Proof.
  intros FORMED VACANT SCOPE DEFINITION REQUEST CHILDREN KIND SAFE INPUT RUN NONNULL.
  set(native:=fun current object=>gateway_native_private(python current)object).
  set(base:=gateway_python_discipline python objects detached).
  set(storage:=gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset
    initial readonly original size object bytes).
  pose proof(gateway_scalar_private_ambient backend python objects detached io stable thread_errno runtime heap_allocation scalar slots
    stream_block stream_offset initial readonly original size object bytes)as STORAGE_CLOSED.
  assert(CLOSED:gateway_ambient_closed backend(fun memory current=>storage memory current /\
    gateway_reference_scope python objects decimal_float ledger held current)).
  { intros first current last following[MEMORY HELD]INTERFERENCE;split.
    - eapply STORAGE_CLOSED;eassumption.
    - eapply gateway_reference_scope_thread_effect;[exact HELD|].
      eapply gateway_reference_thread_ambient;[exact reference_threads| |exact INTERFERENCE].
      eapply gateway_scalar_private_side;exact MEMORY. }
  destruct(gateway_actual_object_operation backend ge api definition arguments _ before world events result after next
    DEFINITION CLOSED(conj INPUT SCOPE)RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &[CALLED[FIT HELD]]&OPERATION &PREFIX &SUFFIX).
  destruct(REQUEST _ _ CALLED)as[CALL_REQUEST CALL_ROOTS].
  assert(SIDE:base None called called_world)by(eapply gateway_scalar_private_side;exact CALLED).
  pose proof(gateway_runtime_constructor _ _ _ _ constructors _ _ _ _ _ _ _ _ _
    SIDE CALL_REQUEST CALL_ROOTS OPERATION NONNULL)as RETURN.
  destruct(gateway_reference_constructed_held python objects decimal_float ledger owner held called called_world result changed changed_world
    value kind FORMED FIT VACANT HELD RETURN CHILDREN KIND SAFE)
    as[final[MINT[WELL[COUNTS[OWNED[CAPTURED DIFFERENT]]]]]].
  set(captured:={|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=result;
    gateway_held_view:=gateway_held_scalar_value value|}).
  set(ready:=fun memory current=>storage memory current /\
    gateway_reference_scope python objects decimal_float final(held++[captured])current).
  assert(AFTER:ready changed changed_world).
  { split;[|exact(conj COUNTS CAPTURED)].
    eapply gateway_scalar_constructor_retains;[exact runtime|exact(proj1 CALLED)|exact(proj2 CALLED)|exact RETURN]. }
  assert(READY_CLOSED:gateway_ambient_closed backend ready).
  { intros first current last following[MEMORY HOLD]INTERFERENCE;split.
    - eapply STORAGE_CLOSED;eassumption.
    - eapply gateway_reference_scope_thread_effect;[exact HOLD|].
      eapply gateway_reference_thread_ambient;[exact reference_threads| |exact INTERFERENCE].
      eapply gateway_scalar_private_side;exact MEMORY. }
  pose proof(gateway_readonly_run_side backend ge ready READY_CLOSED(Returnstate result Kstop changed)changed_world
    suffix result after next I AFTER SUFFIX)as FINAL.
  exists final;exact(conj MINT(conj WELL(conj OWNED FINAL))).
Qed.
