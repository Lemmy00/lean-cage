(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual scalar API executions retain disjoint native caller storage. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayMachine GatewayPython GatewayObjects
  GatewayObjectDiscipline GatewayScalarRuns GatewayReturnRuntime GatewayReturnMemory GatewayNativeRegions
  GatewayOperations GatewayReadonly GatewayThreadRuntime GatewayStreamInterface GatewayRuntime GatewayLocalRuntime
  GatewayFramedRuntime.
Import ListNotations.

Section ScalarMemory.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (python:World->python_world)(objects:World->gateway_object_heap)
  (detached:Values.val->Memory.mem->World->Prop)(io:Event->option gateway_native_io)
  (stable:World->block->Z->Prop)(thread_errno:World->int)(decimal_float:list Z->Floats.float->Prop).
Let native:=fun world object=>gateway_native_private(python world)object.
Let base:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno)
  (constructors:gateway_objects_runtime backend python objects decimal_float).

Theorem gateway_actual_scalar_api_memory api definition arguments value environment protected original
    (property:Memory.mem->World->Prop)before world events result after next :
  gateway_object_api_definition api=Some definition ->gateway_ambient_closed backend property ->
  (forall memory current,property memory current ->
    gateway_constructor_request decimal_float(objects current)memory api arguments value /\
    gateway_constructor_roots(python current)(objects current)api arguments) ->
  property before world ->gateway_return_region_context native base None environment protected original before world ->
  gateway_steps backend ge(gateway_live(Callstate definition arguments Kstop before)world)events
    (gateway_live(Returnstate result Kstop after)next) ->result<>Vnullptr ->
  gateway_return_region_context native base None environment protected original after next.
Proof.
  intros DEFINITION CLOSED REQUEST GOOD INITIAL RUN NONNULL.
  pose proof DEFINITION as EXTERNAL;unfold gateway_object_api_definition in EXTERNAL.
  destruct(gateway_program_definition(gateway_object_api_ident api)global_definitions)as[global|]eqn:GLOBAL;
    [|discriminate].
  destruct global as[function|variable];[|discriminate].
  destruct function as[function|external types result_type convention];[discriminate|].
  inversion EXTERNAL;subst definition.
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ _ _ _ _ _ _ RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &PENDING &PREFIX &OPERATION &SUFFIX).
  set(ready:=gateway_return_region_context native base None environment protected original).
  pose proof(gateway_return_region_ambient backend io native stable base thread_errno runtime
    None environment protected original)as READY_CLOSED.
  assert(PAIR_CLOSED:gateway_runtime_discipline backend(fun memory current=>ready memory current /\property memory current)).
  { intros first current last following[SIDE PROP]INTERFERENCE;split.
    - eapply READY_CLOSED;eassumption.
    - eapply CLOSED;eassumption. }
  destruct(gateway_pending_run_ready backend ge _ PAIR_CLOSED
    (Callstate(External external types result_type convention)arguments Kstop before)before world
    prefix called called_world(conj INITIAL GOOD)PENDING PREFIX)as[CALLED PROP].
  destruct CALLED as[[SIDE OWNED][REGION FRAME]].
  destruct(REQUEST _ _ PROP)as[CALL_REQUEST CALL_ROOTS].
  assert(API:gateway_object_operation backend api arguments called called_world result changed changed_world observed).
  { eexists;split;[exact DEFINITION|exact OPERATION]. }
  pose proof(gateway_runtime_constructor _ _ _ _ constructors _ _ _ _ _ _ _ _ _
    SIDE CALL_REQUEST CALL_ROOTS API NONNULL)as RETURN.
  destruct(gateway_constructor_native_region python objects protected called called_world result changed changed_world value
    REGION RETURN)as[AFTER_REGION STEP_FRAME].
  assert(AFTER:ready changed changed_world).
  { split.
    - split.
      + split;[exact(gateway_constructor_valid _ _ _ _ _ _ _ _ RETURN)|].
        split;[exact(gateway_constructor_gil _ _ _ _ _ _ _ _ RETURN)|exact(gateway_constructor_clear _ _ _ _ _ _ _ _ RETURN)].
      + eapply gateway_constructor_native_environment;[exact OWNED|exact RETURN].
    - split;[exact AFTER_REGION|eapply Mem.unchanged_on_trans;[exact FRAME|exact STEP_FRAME]]. }
  eapply(gateway_readonly_run_side backend ge ready READY_CLOSED(Returnstate result Kstop changed)changed_world
    suffix result after next);[exact I|exact AFTER|exact SUFFIX].
Qed.

End ScalarMemory.
