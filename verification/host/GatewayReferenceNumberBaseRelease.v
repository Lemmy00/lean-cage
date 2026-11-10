(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The same completed integer loop releases its retained base
   before sign conversion, preserving the independent current value even if pointers alias. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline GatewayObjectThreads
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceMoves GatewayReferenceNormalForm
  GatewayReferenceNumericLedger GatewayReferenceNumericFrames GatewayReferenceNumericNormalForm GatewayReferenceNumericContext GatewayReferenceNumericRequests
  GatewayReferenceNumericRelease GatewayReferenceNumberOwners GatewayReferenceContainerScope GatewayReferenceFloatTail
  GatewayNumberSignSource GatewayNumberIntegerStructure GatewayContexts GatewaySourcePaths GatewayFramedRuntime GatewayPathEvents GatewayObjectRuns GatewayObjectEvents
  GatewayScalarConstructorCalls GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Theorem gateway_reference_actual_number_base_release {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (references:gateway_reference_runtime backend python objects)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (projection:gateway_direct_io_projection backend io)
    invocation ledger current_ticket current current_offset integer base_ticket base base_offset tail held parameters
    scalar slots stream_block stream_offset initial readonly original size object bytes before world events value after next:
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_entries ledger=
    gateway_reference_entry current_ticket(number_current_owner invocation)(Vptr current current_offset)::
    gateway_reference_entry base_ticket(number_base_owner invocation)(Vptr base base_offset)::tail->
  (forall captured,In captured held->gateway_held_ticket captured<>base_ticket)->
  gateway_reference_scope python objects decimal_float ledger
    (held++[gateway_reference_scalar_capture base_ticket(Vptr base base_offset)(gateway_long_object 1000000000);
      gateway_reference_scalar_capture current_ticket(Vptr current current_offset)(gateway_long_object integer)])world->
  gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes before world->parameters!_base=Some(Vptr base base_offset)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_json_number Sskip number_integer_loop_cont empty_env parameters before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists final prefix suffix released current_world ignored,
    gateway_reference_apply(gateway_reference_release(number_base_owner invocation)(Vptr base base_offset))
      (gateway_reference_valid ledger)=gateway_reference_valid final /\gateway_reference_ledger_well_formed final /\
    gateway_reference_next final=gateway_reference_next ledger /\
    gateway_reference_entries final=gateway_reference_entry current_ticket(number_current_owner invocation)(Vptr current current_offset)::tail /\
    gateway_reference_owns final(number_current_owner invocation)current_ticket(Vptr current current_offset) /\
    gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation final
      (held++[gateway_reference_scalar_capture current_ticket(Vptr current current_offset)(gateway_long_object integer)])
      scalar slots stream_block stream_offset initial readonly original size object bytes released current_world /\
    events=prefix++suffix /\gateway_received_bytes io(stream_descriptor initial)prefix=[] /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_json_number Sskip number_integer_loop_cont empty_env parameters before)world)prefix
      (gateway_live(Returnstate ignored(number_sign_base_cont parameters)released)current_world) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate ignored(number_sign_base_cont parameters)released)current_world)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros FORMED ENTRIES DIFFERENT SCOPE INPUT BASE RUN.
  set(base_capture:=gateway_reference_scalar_capture base_ticket(Vptr base base_offset)(gateway_long_object 1000000000)).
  set(current_capture:=gateway_reference_scalar_capture current_ticket(Vptr current current_offset)(gateway_long_object integer)).
  assert(BASE_OWNED:gateway_reference_owns ledger(number_base_owner invocation)base_ticket(Vptr base base_offset))
    by(unfold gateway_reference_owns;rewrite ENTRIES;right;left;reflexivity).
  assert(CURRENT_OWNED:gateway_reference_owns ledger(number_current_owner invocation)current_ticket(Vptr current current_offset))
    by(unfold gateway_reference_owns;rewrite ENTRIES;left;reflexivity).
  assert(TICKETS:current_ticket<>base_ticket).
  { intro SAME;rewrite SAME in CURRENT_OWNED.
    destruct(gateway_reference_owned_ticket_unique _ _ _ _ _ _ FORMED BASE_OWNED CURRENT_OWNED)as[OWNER POINTER].
    unfold number_current_owner,number_base_owner in OWNER;discriminate. }
  set(property:=gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation ledger(held++[base_capture;current_capture])
    scalar slots stream_block stream_offset initial readonly original size object bytes).
  pose proof(gateway_reference_numeric_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
    ledger(held++[base_capture;current_capture])scalar slots stream_block stream_offset initial readonly original size object bytes)as CLOSED.
  destruct gateway_actual_number_float_bindings as[_[definition[DEFINITION[BINDING TYPE]]]];destruct BINDING as[symbol[SYMBOL FUNCTION]].
  pose proof(gateway_number_final_base_release_path backend(Clight.globalenv prog)property parameters(Vptr base base_offset)before symbol definition
    CLOSED BASE ltac:(right;repeat eexists;reflexivity)SYMBOL FUNCTION TYPE)as PATH.
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)_ _ _ _ _ _ PATH before world events value after next(conj INPUT SCOPE)RUN)
    as(source_prefix &rest &called &called_world &EVENTS &QUIET &TO_RELEASE &CALLED &FROM_RELEASE).
  destruct(gateway_return_cut backend(Clight.globalenv prog)definition[Vptr base base_offset](number_sign_base_cont parameters)called called_world rest
    (Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_RELEASE)
    as(releasing &suffix &ignored &released &current_world &RELEASE_EVENTS &RELEASE_RUN &REST).
  assert(REORDERED:gateway_reference_scope python objects decimal_float ledger((held++[current_capture])++[base_capture])called_world).
  { eapply gateway_reference_scope_sublist;[exact(proj2 CALLED)|]. intros captured MEMBER;
      repeat rewrite in_app_iff in *;cbn in *;tauto. }
  destruct(gateway_reference_actual_numeric_release backend(Clight.globalenv prog)python objects detached io stable thread_errno heap_allocation decimal_float
    runtime references reference_threads ledger(number_base_owner invocation)base_ticket(Vptr base base_offset)(gateway_long_object 1000000000)
    (held++[current_capture])definition scalar slots stream_block stream_offset initial readonly original size object bytes called called_world releasing ignored released current_world
    FORMED BASE_OWNED ltac:(intros captured MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|BAD]];
      [apply DIFFERENT;exact OLD|subst captured;exact TICKETS|contradiction])REORDERED DEFINITION(proj1 CALLED)RELEASE_RUN)
    as(final &RELEASE &WELL &FINAL_SCOPE &FINAL_STORAGE &OCCURRENCE).
  destruct(gateway_reference_numeric_middle_release ledger final tail current_ticket(number_current_owner invocation)(Vptr current current_offset)
    base_ticket(number_base_owner invocation)(Vptr base base_offset)ltac:(unfold number_base_owner,number_current_owner;discriminate)ENTRIES RELEASE)
    as[FINAL_ENTRIES FINAL_NEXT].
  pose proof(gateway_plug_steps backend(Clight.globalenv prog)_ _ _(number_sign_base_cont parameters)ltac:(cbn;exact I)RELEASE_RUN)as RELEASE_CALLER.
  exists final,(source_prefix++releasing),suffix,released,current_world,ignored.
  split;[exact RELEASE|]. split;[exact WELL|]. split;[exact FINAL_NEXT|]. split;[exact FINAL_ENTRIES|]. split.
  - unfold gateway_reference_owns;rewrite FINAL_ENTRIES;left;reflexivity.
  - split;[split;[exact FINAL_STORAGE|exact FINAL_SCOPE]|]. split;[rewrite EVENTS,RELEASE_EVENTS,app_assoc;reflexivity|]. split.
    + rewrite gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)source_prefix QUIET).
      rewrite(gateway_object_run_no_direct_receive backend(Clight.globalenv prog)io gateway_api_decref definition[Vptr base base_offset]
        called called_world releasing ignored released current_world(stream_descriptor initial)projection DEFINITION RELEASE_RUN);reflexivity.
    + split;[eapply gateway_steps_append;[exact TO_RELEASE|exact RELEASE_CALLER]|exact REST].
Qed.
