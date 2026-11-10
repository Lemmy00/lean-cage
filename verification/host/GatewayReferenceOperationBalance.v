(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: One actual SDK occurrence and its permitted interleavings
   supply reference-pool balance; aliases use per-pointer sums rather than disjointness. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceThreads GatewayReferenceBalance GatewayReferenceRuntime GatewayOperations GatewayObjectExecution
  GatewayReadonly GatewayFramedRuntime GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_actual_operation_balance {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    api definition arguments initial final(property:mem->World->Prop)before world events result after next:
  gateway_object_api_definition api=Some definition->gateway_ambient_closed backend property->
  (forall memory current,property memory current->gateway_objects_ready(python current)(objects current)memory)->
  (forall memory current changed following observed,property memory current->
    gateway_object_operation backend api arguments memory current result changed following observed->
    gateway_objects_ready(python following)(objects following)changed /\
    gateway_reference_balance(python current)(python following)initial final)->
  property before world->
  gateway_steps backend ge(gateway_live(Callstate definition arguments Kstop before)world)events
    (gateway_live(Returnstate result Kstop after)next)->
  gateway_reference_balance(python world)(python next)initial final.
Proof.
  intros DEFINITION CLOSED SIDE EFFECT INPUT RUN.
  set(input:=fun memory current=>property memory current /\
    forall pointer,(python_native_strong(python world)pointer<=python_native_strong(python current)pointer)%nat).
  assert(INPUT_CLOSED:gateway_ambient_closed backend input).
  { intros first current last following[PROP COUNTS]INTERFERENCE;split;[eapply CLOSED;eassumption|].
    pose proof(gateway_reference_thread_ambient _ _ _ _ _ _ _ reference_threads None first current last following(SIDE first current PROP)INTERFERENCE)as CHANGE.
    intros pointer;specialize(COUNTS pointer);pose proof(gateway_reference_thread_counts _ _ _ _ CHANGE pointer);lia. }
  assert(START:input before world)by(split;[exact INPUT|intros;lia]).
  destruct(gateway_actual_object_operation backend ge api definition arguments input before world events result after next
    DEFINITION INPUT_CLOSED START RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &[CALLED COUNTS]&OPERATION &PREFIX &SUFFIX).
  destruct(EFFECT called called_world changed changed_world observed CALLED OPERATION)as[READY LOCAL].
  assert(PREFIX_BALANCE:gateway_reference_balance(python world)(python called_world)initial initial)
    by(apply gateway_reference_balance_retained;exact COUNTS).
  assert(AFTER:gateway_reference_balance(python world)(python changed_world)initial final)
    by(eapply gateway_reference_balance_trans;eassumption).
  set(output:=fun memory current=>gateway_objects_ready(python current)(objects current)memory /\
    gateway_reference_balance(python world)(python current)initial final).
  assert(OUTPUT_CLOSED:gateway_ambient_closed backend output).
  { intros first current last following[READY_BEFORE BALANCE]INTERFERENCE;split.
    - exact(proj1(gateway_thread_ambient _ _ _ _ _ _ runtime None first current last following READY_BEFORE INTERFERENCE)).
    - pose proof(gateway_reference_thread_ambient _ _ _ _ _ _ _ reference_threads None first current last following READY_BEFORE INTERFERENCE)as CHANGE.
      eapply gateway_reference_balance_trans;[exact BALANCE|].
      apply gateway_reference_balance_retained;exact(gateway_reference_thread_counts _ _ _ _ CHANGE). }
  exact(proj2(gateway_readonly_run_side backend ge output OUTPUT_CLOSED(Returnstate result Kstop changed)changed_world
    suffix result after next I(conj READY AFTER)SUFFIX)).
Qed.

Theorem gateway_reference_actual_constructor_balance {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects detached io stable thread_errno heap_allocation decimal_float
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    api definition arguments description owner initial final(property:mem->World->Prop)before world events result after next:
  gateway_object_api_definition api=Some definition->gateway_ambient_closed backend property->
  (forall memory current,property memory current->gateway_objects_ready(python current)(objects current)memory /\
    gateway_constructor_request decimal_float(objects current)memory api arguments description /\
    gateway_constructor_roots(python current)(objects current)api arguments)->
  gateway_reference_apply(gateway_reference_mint owner result)(gateway_reference_valid initial)=gateway_reference_valid final->
  property before world->
  gateway_steps backend ge(gateway_live(Callstate definition arguments Kstop before)world)events
    (gateway_live(Returnstate result Kstop after)next)->result<>Vnullptr->
  gateway_reference_balance(python world)(python next)initial final.
Proof.
  intros DEFINITION CLOSED REQUEST MINT INPUT RUN NONNULL.
  eapply gateway_reference_actual_operation_balance;[exact runtime|exact reference_threads|exact DEFINITION|exact CLOSED| | |exact INPUT|exact RUN].
  - intros memory current GOOD;exact(proj1(REQUEST memory current GOOD)).
  - intros memory current changed following observed GOOD OPERATION.
    destruct(REQUEST memory current GOOD)as[READY[REQUESTED ROOTS]].
    pose proof(gateway_runtime_constructor _ _ _ _ constructors _ _ _ _ _ _ _ _ _ READY REQUESTED ROOTS OPERATION NONNULL)as RETURN.
    split.
    + exact(conj(gateway_constructor_valid _ _ _ _ _ _ _ _ RETURN)
        (conj(gateway_constructor_gil _ _ _ _ _ _ _ _ RETURN)(gateway_constructor_clear _ _ _ _ _ _ _ _ RETURN))).
    + eapply gateway_reference_balance_mint;[eapply gateway_constructor_reference_credit;exact RETURN|exact MINT].
Qed.

Theorem gateway_reference_actual_release_balance {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (references:gateway_reference_runtime backend python objects)
    definition owner ticket pointer initial final(property:mem->World->Prop)before world events result after next:
  gateway_object_api_definition gateway_api_decref=Some definition->gateway_ambient_closed backend property->
  gateway_reference_ledger_well_formed initial->gateway_reference_owns initial owner ticket pointer->
  (forall memory current,property memory current->gateway_objects_ready(python current)(objects current)memory /\
    gateway_reference_counts_fit initial(python current) /\gateway_destructible(objects current)pointer)->
  gateway_reference_apply(gateway_reference_release owner pointer)(gateway_reference_valid initial)=gateway_reference_valid final->
  property before world->
  gateway_steps backend ge(gateway_live(Callstate definition[pointer]Kstop before)world)events
    (gateway_live(Returnstate result Kstop after)next)->
  gateway_reference_balance(python world)(python next)initial final.
Proof.
  intros DEFINITION CLOSED FORMED OWNED SELECTED RELEASE INPUT RUN.
  eapply gateway_reference_actual_operation_balance;[exact runtime|exact reference_threads|exact DEFINITION|exact CLOSED| | |exact INPUT|exact RUN].
  - intros memory current GOOD;exact(proj1(SELECTED memory current GOOD)).
  - intros memory current changed following observed GOOD OPERATION.
    destruct(SELECTED memory current GOOD)as[READY[FIT DESTROY]].
    destruct(gateway_reference_actual_decref backend python objects references initial owner ticket pointer memory current result changed following observed
      FORMED FIT OWNED READY DESTROY OPERATION)as(ledger &ACTION &WELL &NEXT_FIT &RETURN &OTHERS).
    rewrite RELEASE in ACTION;injection ACTION as SAME;subst ledger.
    split;[exact(gateway_reference_ready _ _ _ _ _ _ _ RETURN)|].
    eapply gateway_reference_balance_release;[exact FORMED|exact OWNED|exact RELEASE|
      exact(gateway_reference_owned _ _ _ _ _ _ _ RETURN)|exact(gateway_reference_others _ _ _ _ _ _ _ RETURN)].
Qed.
