(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual key cleanup retains the independently owned result graph. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayPublicReferences
  GatewayAttachedReferences GatewayObjectDiscipline GatewayObjectThreads GatewayReferenceLedger GatewayReferenceAccounting
  GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceBorrowedGraph GatewayReferenceSourceExecution
  GatewayObservationContexts GatewayOutcomeGetterSource GatewaySourceObjectReceipt GatewayFramedRuntime GatewaySourcePaths
  GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_actual_owned_observation_key_release {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun world object=>gateway_native_private(python world)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun world object=>gateway_native_private(python world)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (public_references:gateway_public_reference_runtime backend python objects)
    parameters key key_offset ignored before world events value after next ledger key_ticket held decref:
  parameters!_key=Some(Vptr key key_offset)->
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_owns ledger(gateway_reference_temporary 0 _key)key_ticket(Vptr key key_offset)->
  (forall captured,In captured held->gateway_held_ticket captured<>key_ticket)->
  gateway_observation_owned_context python objects decimal_float ledger held before world->
  Genv.find_symbol ge _Py_DecRef=Some decref->Genv.find_funct_ptr ge decref=Some gateway_reference_decref_definition->
  gateway_steps backend ge
    (gateway_live(Returnstate ignored(gateway_observation_value_root_cont parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists released prefix suffix called owner returned changed following observed,
    events=prefix++gateway_primitive observed::suffix /\
    gateway_reference_apply(gateway_reference_release(gateway_reference_temporary 0 _key)(Vptr key key_offset))
      (gateway_reference_valid ledger)=gateway_reference_valid released /\
    gateway_reference_ledger_well_formed released /\
    gateway_observation_owned_context python objects decimal_float released held changed following /\
    (forall place ticket pointer,ticket<>key_ticket->gateway_reference_owns ledger place ticket pointer->
      gateway_reference_owns released place ticket pointer) /\
    gateway_object_operation backend gateway_api_decref[Vptr key key_offset]called owner returned changed following observed /\
    gateway_steps backend ge
      (gateway_live(Returnstate ignored(gateway_observation_value_root_cont parameters)before)world)prefix
      (gateway_live(Callstate gateway_reference_decref_definition[Vptr key key_offset]
        (gateway_observation_key_release_cont parameters)called)owner) /\
    gateway_steps backend ge
      (gateway_live(Returnstate returned(gateway_observation_key_release_cont parameters)changed)following)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros KEY WELL OWNED HELD_OTHER INPUT SYMBOL FUNCTION RUN.
  set(property:=gateway_observation_owned_context python objects decimal_float ledger held).
  assert(CLOSED:gateway_ambient_closed backend property).
  { eapply gateway_observation_owned_context_closed;[exact runtime|exact reference_threads]. }
  pose proof(gateway_observation_key_release_source_path backend ge property parameters key key_offset ignored before decref
    gateway_reference_decref_definition CLOSED KEY SYMBOL FUNCTION eq_refl)as PATH.
  destruct(gateway_source_object_receipt backend ge gateway_api_decref gateway_reference_decref_definition[Vptr key key_offset]
    (gateway_observation_key_release_cont parameters)property _ before world events value after next eq_refl
    ltac:(cbn;exact I)ltac:(cbn;lia)CLOSED PATH INPUT RUN)
    as(prefix &suffix &called &owner &returned &changed &following &observed &EVENTS &[NORMAL[FIT HELD]]&PREFIX &OPERATION &REST).
  destruct(gateway_public_release_keeps_independent_graphs backend python objects decimal_float public_references ledger
    (gateway_reference_temporary 0 _key)key_ticket(Vptr key key_offset)held called owner returned changed following observed
    WELL FIT OWNED(gateway_normal_attached _ _ _ NORMAL)HELD HELD_OTHER OPERATION)
    as(released &RELEASE &RELEASED_WELL &COUNTS &CAPTURED &EFFECT &RETAINED).
  assert(AFTER:gateway_objects_ready(python following)(objects following)changed).
  { destruct(gateway_attached_reference_ready _ _ _ _ _ _ _ EFFECT)as[VALID GIL].
    split;[exact VALID|]. split;[exact GIL|].
    rewrite(gateway_attached_reference_pending _ _ _ _ _ _ _ EFFECT);exact(proj2(proj2 NORMAL)). }
  exists released,prefix,suffix,called,owner,returned,changed,following,observed.
  exact(conj EVENTS(conj RELEASE(conj RELEASED_WELL(conj(conj AFTER(conj COUNTS CAPTURED))
    (conj RETAINED(conj OPERATION(conj PREFIX REST))))))).
Qed.
