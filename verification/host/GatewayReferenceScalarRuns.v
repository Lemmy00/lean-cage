(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Scalar call receipts retain the source-owned reference pool. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayMachine GatewayPython GatewayObjects
  GatewayObjectDiscipline GatewayObjectThreads GatewayReferences GatewayReferenceLedger GatewayReferenceAccounting
  GatewayReferenceHeld GatewayReferenceConstructors GatewayReferenceThreads GatewayOperations GatewayReadonly
  GatewayReturnRuntime GatewayScalarRuns GatewayThreadRuntime GatewayStreamInterface GatewayFramedRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Section ScalarRuns.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (python:World->python_world)(objects:World->gateway_object_heap)
  (detached:Values.val->mem->World->Prop)(io:Event->option gateway_native_io)
  (stable:World->block->Z->Prop)(thread_errno:World->int)(heap_allocation:block->Z->Prop)
  (decimal_float:list Z->Floats.float->Prop).
Let native:=fun world object=>gateway_native_private(python world)object.
Let base:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno)
  (constructors:gateway_objects_runtime backend python objects decimal_float)
  (reference_threads:gateway_reference_thread_contract backend native stable base heap_allocation python objects).

Theorem gateway_reference_actual_scalar_run ledger owner held api definition arguments value kind environment
    (property:mem->World->Prop)before world events result after next:
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_take owner(gateway_reference_entries ledger)=None->
  gateway_reference_scope python objects decimal_float ledger held world->
  gateway_object_api_definition api=Some definition->gateway_ambient_closed backend property->
  (forall memory current,property memory current->
    gateway_constructor_request decimal_float(objects current)memory api arguments value /\
    gateway_constructor_roots(python current)(objects current)api arguments)->
  gateway_object_children value=[]->gateway_object_kind value=Some kind->gateway_destructor_kind kind->
  property before world->gateway_return_environment native base None environment before world->
  gateway_steps backend ge(gateway_live(Callstate definition arguments Kstop before)world)events
    (gateway_live(Returnstate result Kstop after)next)->result<>Vnullptr->
  exists final prefix suffix called called_world changed changed_world observed,
    events=prefix++gateway_primitive observed::suffix /\
    gateway_object_operation backend api arguments called called_world result changed changed_world observed /\
    gateway_reference_apply(gateway_reference_mint owner result)(gateway_reference_valid ledger)=
      gateway_reference_valid final /\gateway_reference_ledger_well_formed final /\
    gateway_reference_owns final owner(gateway_reference_next ledger)result /\
    gateway_reference_scope python objects decimal_float final
      (held++[{|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=result;
        gateway_held_view:=gateway_held_scalar_value value|}])next /\
    gateway_return_environment native base None environment after next /\
    (forall place ticket pointer,gateway_reference_owns ledger place ticket pointer->
      gateway_reference_owns final place ticket pointer).
Proof.
  intros FORMED VACANT SCOPE DEFINITION CLOSED REQUEST CHILDREN KIND SAFE GOOD INITIAL RUN NONNULL.
  pose proof DEFINITION as EXTERNAL;unfold gateway_object_api_definition in EXTERNAL.
  destruct(gateway_program_definition(gateway_object_api_ident api)global_definitions)as[global|]eqn:GLOBAL;
    [|discriminate].
  destruct global as[function|variable];[|discriminate].
  destruct function as[function|external types result_type convention];[discriminate|].
  inversion EXTERNAL;subst definition.
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ _ _ _ _ _ _ RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &PENDING &PREFIX &OPERATION &SUFFIX).
  assert(CALLED:gateway_return_environment native base None environment called called_world /\
    property called called_world /\gateway_reference_scope python objects decimal_float ledger held called_world).
  { assert(PAIR_CLOSED:gateway_runtime_discipline backend
      (fun memory current=>gateway_return_environment native base None environment memory current /\
        property memory current /\gateway_reference_scope python objects decimal_float ledger held current)).
    { intros first current last following[SIDE[PROP HOLD]]INTERFERENCE;split.
      - eapply gateway_return_environment_ambient;[exact runtime|exact SIDE|exact INTERFERENCE].
      - split;[eapply CLOSED;eassumption|].
        eapply gateway_reference_scope_thread_effect;[exact HOLD|].
        eapply gateway_reference_thread_ambient;[exact reference_threads|exact(proj1 SIDE)|exact INTERFERENCE]. }
    eapply(gateway_pending_run_ready backend ge _ PAIR_CLOSED
      (Callstate(External external types result_type convention)arguments Kstop before)before world
      prefix called called_world);[exact(conj INITIAL(conj GOOD SCOPE))|exact PENDING|exact PREFIX]. }
  destruct CALLED as[[READY OWNED][PROP[FIT HELD]]].
  destruct(REQUEST _ _ PROP)as[CALL_REQUEST CALL_ROOTS].
  assert(API:gateway_object_operation backend api arguments called called_world result changed changed_world observed).
  { eexists;split;[exact DEFINITION|exact OPERATION]. }
  pose proof(gateway_runtime_constructor _ _ _ _ constructors _ _ _ _ _ _ _ _ _
    READY CALL_REQUEST CALL_ROOTS API NONNULL)as RETURN.
  destruct(gateway_reference_constructed_held python objects decimal_float ledger owner held
    called called_world result changed changed_world value kind FORMED FIT VACANT HELD RETURN CHILDREN KIND SAFE)
    as[final[APPLY[WELL[COUNTS[OWNED_RESULT[HELD_AFTER DIFFERENT]]]]]].
  set(captured:={|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=result;
    gateway_held_view:=gateway_held_scalar_value value|}).
  assert(RETAINED:forall place ticket pointer,gateway_reference_owns ledger place ticket pointer->
      gateway_reference_owns final place ticket pointer).
  { intros place ticket pointer OLD.
    unfold gateway_reference_apply in APPLY;rewrite VACANT in APPLY;inversion APPLY;subst final;right;exact OLD. }
  set(ready:=fun memory current=>gateway_return_environment native base None environment memory current /\
    gateway_reference_scope python objects decimal_float final(held++[captured])current).
  assert(READY_AFTER:gateway_objects_ready(python changed_world)(objects changed_world)changed).
  { split;[exact(gateway_constructor_valid _ _ _ _ _ _ _ _ RETURN)|].
    split;[exact(gateway_constructor_gil _ _ _ _ _ _ _ _ RETURN)|exact(gateway_constructor_clear _ _ _ _ _ _ _ _ RETURN)]. }
  assert(AFTER:ready changed changed_world).
  { split;[split;[exact READY_AFTER|eapply gateway_constructor_native_environment;eassumption]|].
    split;[exact COUNTS|exact HELD_AFTER]. }
  assert(READY_CLOSED:gateway_runtime_discipline backend ready).
  { intros first current last following[[SIDE ENV]HOLD]INTERFERENCE;split.
    - eapply gateway_return_environment_ambient;[exact runtime|exact(conj SIDE ENV)|exact INTERFERENCE].
    - eapply gateway_reference_scope_thread_effect;[exact HOLD|].
      eapply gateway_reference_thread_ambient;[exact reference_threads|exact SIDE|exact INTERFERENCE]. }
  assert(FINAL:ready after next).
  { eapply(gateway_readonly_run_side backend ge ready READY_CLOSED(Returnstate result Kstop changed)changed_world
      suffix result after next);[exact I|exact AFTER|exact SUFFIX]. }
  exists final,prefix,suffix,called,called_world,changed,changed_world,observed.
  split;[exact EVENTS|]. split;[exact API|]. split;[exact APPLY|]. split;[exact WELL|].
  split;[exact OWNED_RESULT|]. split;[exact(proj2 FINAL)|]. split;[exact(proj1 FINAL)|exact RETAINED].
Qed.

End ScalarRuns.
