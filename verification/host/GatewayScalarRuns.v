(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Real scalar API calls mint and retain their own reference leases. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayMachine GatewayPython GatewayObjects
  GatewayRootLeases GatewayObjectThreads GatewayValueOwnership GatewayObjectDiscipline GatewayReturnRuntime GatewayReferences
  GatewayOperations GatewayReadonly GatewayThreadRuntime GatewayStreamInterface GatewayRuntime GatewayFramedRuntime
  GatewayLocalRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Section ScalarRuns.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (python:World->python_world)(objects:World->gateway_object_heap)
  (detached:Values.val->mem->World->Prop)(io:Event->option gateway_native_io)
  (stable:World->block->Z->Prop)(thread_errno:World->int)(heap_allocation:block->BinNums.Z->Prop)
  (decimal_float:list BinNums.Z->Floats.float->Prop)(leases:World->nat->Values.val->Prop).
Let native:=fun world object=>gateway_native_private(python world)object.
Let base:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno)
  (constructors:gateway_objects_runtime backend python objects decimal_float)
  (roots:gateway_root_lease_runtime backend python objects decimal_float leases)
  (object_threads:gateway_object_thread_contract backend native stable base heap_allocation python objects leases).

Lemma gateway_constructor_native_environment before world result after next value environment :
  gateway_native_environment native world before environment ->
  gateway_constructor_return(python world)(objects world)before result(python next)(objects next)after value ->
  gateway_native_environment native next after environment.
Proof.
  intros OWNED RETURN identifier object ty LOOK;destruct(OWNED identifier object ty LOOK)as[LIVE PRIVATE];split.
  - eapply Mem.valid_block_unchanged_on;[exact(gateway_constructor_native _ _ _ _ _ _ _ _ RETURN)|exact LIVE].
  - eapply gateway_constructor_native_retained;[exact RETURN|exact LIVE|exact PRIVATE].
Qed.

Theorem gateway_actual_scalar_api_run api definition arguments value kind environment
    (property:mem->World->Prop)before world events result after next :
  gateway_object_api_definition api=Some definition ->gateway_ambient_closed backend property ->
  (forall memory current,property memory current ->
    gateway_constructor_request decimal_float(objects current)memory api arguments value /\
    gateway_constructor_roots(python current)(objects current)api arguments) ->
  gateway_object_children value=[] ->gateway_object_kind value=Some kind ->gateway_destructor_kind kind ->
  property before world ->gateway_return_environment native base None environment before world ->
  gateway_steps backend ge(gateway_live(Callstate definition arguments Kstop before)world)events
    (gateway_live(Returnstate result Kstop after)next) ->result<>Vnullptr ->
  exists ticket,gateway_held_values python objects decimal_float leases
      [{|gateway_held_ticket:=ticket;gateway_held_object:=result;gateway_held_view:=gateway_held_scalar_value value|}]next /\
    gateway_return_environment native base None environment after next.
Proof.
  intros DEFINITION CLOSED REQUEST CHILDREN KIND SAFE GOOD INITIAL RUN NONNULL.
  pose proof DEFINITION as EXTERNAL;unfold gateway_object_api_definition in EXTERNAL.
  destruct(gateway_program_definition(gateway_object_api_ident api)global_definitions)as[global|]eqn:GLOBAL;
    [|discriminate].
  destruct global as[function|variable];[|discriminate].
  destruct function as[function|external types result_type convention];[discriminate|].
  inversion EXTERNAL;subst definition.
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ _ _ _ _ _ _ RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &PENDING &PREFIX &OPERATION &SUFFIX).
  assert(CALLED:gateway_return_environment native base None environment called called_world /\property called called_world).
  { assert(PAIR_CLOSED:gateway_runtime_discipline backend
      (fun memory current=>gateway_return_environment native base None environment memory current /\property memory current)).
    { intros first current last following[SIDE PROP]INTERFERENCE;split.
      - eapply gateway_return_environment_ambient;[exact runtime|exact SIDE|exact INTERFERENCE].
      - eapply CLOSED;eassumption. }
    exact(gateway_pending_run_ready backend ge _ PAIR_CLOSED
      (Callstate(External external types result_type convention)arguments Kstop before)before world
      prefix called called_world(conj INITIAL GOOD)PENDING PREFIX). }
  destruct CALLED as[[READY OWNED]PROP].
  destruct(REQUEST _ _ PROP)as[CALL_REQUEST CALL_ROOTS].
  assert(API:gateway_object_operation backend api arguments called called_world result changed changed_world observed).
  { eexists;split;[exact DEFINITION|exact OPERATION]. }
  pose proof(gateway_runtime_constructor _ _ _ _ constructors _ _ _ _ _ _ _ _ _
    READY CALL_REQUEST CALL_ROOTS API NONNULL)as RETURN.
  destruct(gateway_actual_constructor_held_scalar backend python objects decimal_float leases constructors roots
    api arguments called called_world result changed changed_world observed value kind
    READY CALL_REQUEST CALL_ROOTS API NONNULL CHILDREN KIND SAFE)as(ticket &CREATED &HELD).
  set(captured:={|gateway_held_ticket:=ticket;gateway_held_object:=result;gateway_held_view:=gateway_held_scalar_value value|}).
  set(ready:=fun memory current=>gateway_return_environment native base None environment memory current /\
    gateway_held_values python objects decimal_float leases[captured]current).
  assert(READY_AFTER:gateway_objects_ready(python changed_world)(objects changed_world)changed).
  { split;[exact(gateway_constructor_valid _ _ _ _ _ _ _ _ RETURN)|].
    split;[exact(gateway_constructor_gil _ _ _ _ _ _ _ _ RETURN)|exact(gateway_constructor_clear _ _ _ _ _ _ _ _ RETURN)]. }
  assert(AFTER:ready changed changed_world).
  { split;[split;[exact READY_AFTER|eapply gateway_constructor_native_environment;eassumption]|exact HELD]. }
  assert(READY_CLOSED:gateway_runtime_discipline backend ready).
  { intros first current last following[[SIDE ENV]HOLD]INTERFERENCE;split.
    - eapply gateway_return_environment_ambient;[exact runtime|split;[exact SIDE|exact ENV]|exact INTERFERENCE].
    - eapply gateway_held_values_effect;[exact roots|exact HOLD|].
      eapply gateway_object_thread_ambient;[exact object_threads|exact SIDE|exact INTERFERENCE]. }
  assert(FINAL:ready after next).
  { eapply(gateway_readonly_run_side backend ge ready READY_CLOSED(Returnstate result Kstop changed)changed_world
      suffix result after next);[exact I|exact AFTER|exact SUFFIX]. }
  exists ticket;split;[exact(proj2 FINAL)|exact(proj1 FINAL)].
Qed.

End ScalarRuns.
