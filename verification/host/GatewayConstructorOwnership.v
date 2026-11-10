(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Fresh SDK leases retain actual outer parser roots and their identities. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayMachine GatewayPython GatewayObjects GatewayReferences
  GatewayGraphFreshness GatewayObjectDiscipline GatewayRootLeases GatewayObjectThreads GatewayValueOwnership GatewayScalarRuns GatewayReturnRuntime
  GatewayOperations GatewayReadonly GatewayFramedRuntime GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.

Theorem gateway_actual_constructor_held_run {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects detached io stable thread_errno heap_allocation decimal_float leases
    (runtime:gateway_thread_runtime backend io(fun world object=>gateway_native_private(python world)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (roots:gateway_root_lease_runtime backend python objects decimal_float leases)
    (object_threads:gateway_object_thread_contract backend(fun world object=>gateway_native_private(python world)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects leases)
    api definition arguments value kind environment old_held(property:mem->World->Prop)
    before world events result after next:
  gateway_object_api_definition api=Some definition ->gateway_ambient_closed backend property ->
  (forall memory current,property memory current ->
    gateway_constructor_request decimal_float(objects current)memory api arguments value /\
    gateway_constructor_roots(python current)(objects current)api arguments) ->
  gateway_object_children value=[] ->gateway_object_kind value=Some kind ->gateway_destructor_kind kind ->
  property before world ->
  gateway_return_environment(fun world object=>gateway_native_private(python world)object)
    (gateway_python_discipline python objects detached)None environment before world ->
  gateway_held_values python objects decimal_float leases old_held world ->
  gateway_steps backend ge(gateway_live(Callstate definition arguments Kstop before)world)events
    (gateway_live(Returnstate result Kstop after)next) ->result<>Vnullptr ->
  exists ticket,
    (forall old,In old old_held ->ticket<>gateway_held_ticket old) /\
    gateway_held_values python objects decimal_float leases
      (old_held++[{|gateway_held_ticket:=ticket;gateway_held_object:=result;
        gateway_held_view:=gateway_held_scalar_value value|}])next /\
    gateway_return_environment(fun world object=>gateway_native_private(python world)object)
      (gateway_python_discipline python objects detached)None environment after next /\
    (gateway_mutable_container value ->gateway_held_graphs_avoid(objects next)old_held result).
Proof.
  intros DEFINITION CLOSED REQUEST CHILDREN KIND SAFE GOOD INITIAL HELD RUN NONNULL.
  set(native:=fun world object=>gateway_native_private(python world)object).
  set(base:=gateway_python_discipline python objects detached).
  pose proof DEFINITION as EXTERNAL;unfold gateway_object_api_definition in EXTERNAL.
  destruct(gateway_program_definition(gateway_object_api_ident api)global_definitions)as[global|]eqn:GLOBAL;[|discriminate].
  destruct global as[function|variable];[|discriminate].
  destruct function as[function|external types result_type convention];[discriminate|].
  inversion EXTERNAL;subst definition.
  set(pending_ready:=fun memory current=>gateway_return_environment native base None environment memory current /\
    property memory current /\gateway_held_values python objects decimal_float leases old_held current).
  assert(PENDING_CLOSED:gateway_ambient_closed backend pending_ready).
  { intros first current last following[[SIDE ENV][PROPERTY OLD]]INTERFERENCE;split.
    - eapply gateway_return_environment_ambient;[exact runtime|split;eassumption|exact INTERFERENCE].
    - split;[eapply CLOSED;eassumption|]. eapply gateway_held_values_effect;[exact roots|exact OLD|].
      eapply gateway_object_thread_ambient;[exact object_threads|exact SIDE|exact INTERFERENCE]. }
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ _ _ _ _ _ _ RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &PENDING &PREFIX &OPERATION &SUFFIX).
  destruct(gateway_pending_run_ready backend ge pending_ready PENDING_CLOSED
    (Callstate(External external types result_type convention)arguments Kstop before)before world prefix called called_world
    ltac:(split;[exact INITIAL|split;assumption])PENDING PREFIX)as[[SIDE ENV][PROPERTY OLD]].
  destruct(REQUEST _ _ PROPERTY)as[CALL_REQUEST CALL_ROOTS].
  assert(API:gateway_object_operation backend api arguments called called_world result changed changed_world observed).
  { eexists;split;[exact DEFINITION|exact OPERATION]. }
  pose proof(gateway_runtime_constructor _ _ _ _ constructors _ _ _ _ _ _ _ _ _ SIDE CALL_REQUEST CALL_ROOTS API NONNULL)as RETURN.
  destruct(gateway_actual_constructor_held_scalar backend python objects decimal_float leases constructors roots api arguments
    called called_world result changed changed_world observed value kind SIDE CALL_REQUEST CALL_ROOTS API NONNULL CHILDREN KIND SAFE)
    as(ticket &CREATED &NEW_HELD).
  assert(DIFFERENT:forall old,In old old_held ->ticket<>gateway_held_ticket old).
  { intros old MEMBER.
    pose proof(proj1(Forall_forall _ _)OLD old MEMBER)as[LEASE REST].
    eapply gateway_created_reference_is_new;[exact CREATED|exact LEASE]. }
  pose proof(gateway_constructor_keeps_held_values backend python objects decimal_float leases constructors roots old_held
    api arguments called called_world result changed changed_world observed value SIDE CALL_REQUEST CALL_ROOTS API NONNULL OLD)as OLD_AFTER.
  set(ready:=fun memory current=>gateway_return_environment native base None environment memory current /\
    gateway_held_values python objects decimal_float leases
      (old_held++[{|gateway_held_ticket:=ticket;gateway_held_object:=result;gateway_held_view:=gateway_held_scalar_value value|}])current /\
    (gateway_mutable_container value ->gateway_held_graphs_avoid(objects current)old_held result)).
  assert(AFTER:ready changed changed_world).
  { split.
    - split.
      + split;[exact(gateway_constructor_valid _ _ _ _ _ _ _ _ RETURN)|].
        split;[exact(gateway_constructor_gil _ _ _ _ _ _ _ _ RETURN)|exact(gateway_constructor_clear _ _ _ _ _ _ _ _ RETURN)].
      + eapply gateway_constructor_native_environment;[exact ENV|exact RETURN].
    - split;[apply Forall_app;split;assumption|]. intro MUTABLE.
      eapply gateway_constructor_avoids_held_graphs;[exact RETURN|exact SIDE|exact MUTABLE|exact OLD|exact OLD_AFTER]. }
  assert(READY_CLOSED:gateway_ambient_closed backend ready).
  { intros first current last following[[READY ENVIRONMENT][CAPTURED AVOIDS]]INTERFERENCE.
    assert(EFFECT:gateway_object_thread_effect python objects leases current following).
    { eapply gateway_object_thread_ambient;[exact object_threads|exact READY|exact INTERFERENCE]. }
    assert(NEXT_HELD:gateway_held_values python objects decimal_float leases
      (old_held++[{|gateway_held_ticket:=ticket;gateway_held_object:=result;gateway_held_view:=gateway_held_scalar_value value|}])following).
    { eapply gateway_held_values_effect;[exact roots|exact CAPTURED|exact EFFECT]. }
    split.
    - eapply gateway_return_environment_ambient;[exact runtime|split;eassumption|exact INTERFERENCE].
    - split;[exact NEXT_HELD|]. intro MUTABLE.
      pose proof CAPTURED as OLD_PARTS;apply Forall_app in OLD_PARTS;destruct OLD_PARTS as[OLD_BEFORE IGNORED_BEFORE].
      pose proof NEXT_HELD as NEXT_PARTS;apply Forall_app in NEXT_PARTS;destruct NEXT_PARTS as[OLD_FOLLOWING IGNORED_FOLLOWING].
      destruct EFFECT as[RETAINED[FRAME PRIVACY]].
      eapply gateway_held_graphs_avoid_retained;[exact OLD_BEFORE|exact OLD_FOLLOWING|exact FRAME|exact PRIVACY|apply AVOIDS;exact MUTABLE]. }
  pose proof(gateway_readonly_run_side backend ge ready READY_CLOSED(Returnstate result Kstop changed)changed_world suffix result after next
    I AFTER SUFFIX)as[FINAL[HELD_FINAL AVOID_FINAL]].
  exists ticket;split;[exact DIFFERENT|]. split;[exact HELD_FINAL|]. split;assumption.
Qed.
