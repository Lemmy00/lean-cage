(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The same received private-copy credit is captured in the original caller's _copy. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue GatewayObjectDiscipline GatewayObjectThreads
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceNormalForm GatewayReferenceStackBound GatewayReferenceRuntime
  GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceExecution GatewayOutcomeCopyViews GatewayOutcomeCopyCapture GatewayOutcomeCopySource
  GatewayOutcomeFields GatewayOutcomeMetadata GatewayFramedRuntime GatewayThreadRuntime GatewayStreamInterface GatewayLocalRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_actual_received_copy_capture {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    context older held reserved environment parameters original fields wires metadata_field metadata wire
    before world copy copy_offset changed following observed events value after next:
  gateway_reference_stack_bound context older->gateway_reference_ledger_well_formed older->
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count older pointer<=python_native_strong(python world)pointer)%nat)->
  gateway_reference_held python objects decimal_float older held world->gateway_objects_ready(python world)(objects world)before->
  gateway_native_environment(fun current object=>gateway_native_private(python current)object)world before environment->
  (0<python_native_strong(python world)original)%nat->
  gateway_object_values(objects world)original=Some(gateway_dict_object fields)->gateway_private_tree(objects world)original->
  gateway_destructible(objects world)original->gateway_dictionary_heap decimal_float(objects world)fields wires->
  gateway_dictionary_lookup gateway_outcome_json_name fields=Some metadata_field->gateway_dictionary_value metadata_field=metadata->
  gateway_value_heap decimal_float(objects world)metadata wire->
  gateway_object_operation backend gateway_api_dict_copy[original]before world(Vptr copy copy_offset)changed following observed->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vptr copy copy_offset)(plug_cont(gateway_outcome_copy_cont environment parameters)context)changed)following)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists stored prefix suffix memory current,
    events=prefix++suffix /\gateway_reference_ledger_well_formed stored /\
    gateway_reference_entries stored=gateway_reference_entry(gateway_reference_next older)
      (gateway_reference_temporary(gateway_reference_depth context)_copy)(Vptr copy copy_offset)::gateway_reference_entries older /\
    gateway_reference_scope python objects decimal_float stored held current /\gateway_objects_ready(python current)(objects current)memory /\
    gateway_native_environment(fun current object=>gateway_native_private(python current)object)current memory environment /\
    gateway_outcome_fields_view python objects decimal_float(Vptr copy copy_offset)fields wires current /\
    gateway_outcome_metadata_view python objects decimal_float(Vptr copy copy_offset)fields metadata_field metadata wire current /\
    (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count stored pointer<=python_native_strong(python current)pointer)%nat) /\
    gateway_reference_source_bound ge
      (State f_host_outcome_from Sskip(Kseq gateway_outcome_after_copy context)environment
        (gateway_outcome_copied_parameters parameters(Vptr copy copy_offset))memory)stored /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vptr copy copy_offset)(plug_cont(gateway_outcome_copy_cont environment parameters)context)changed)following)prefix
      (gateway_live(State f_host_outcome_from Sskip(Kseq gateway_outcome_after_copy context)environment
        (gateway_outcome_copied_parameters parameters(Vptr copy copy_offset))memory)current) /\
    gateway_steps backend ge
      (gateway_live(State f_host_outcome_from Sskip(Kseq gateway_outcome_after_copy context)environment
        (gateway_outcome_copied_parameters parameters(Vptr copy copy_offset))memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros STACK WELL BUDGET HELD READY ENVIRONMENT OWNED VALUE PRIVATE DESTROY RECEIVED METADATA META_VALUE WIRE OPERATION RUN.
  assert(VACANT:gateway_reference_take(gateway_reference_result(S(gateway_reference_depth context)))(gateway_reference_entries older)=None).
  { apply gateway_reference_take_none;intros entry MEMBER OWNER;destruct(STACK entry MEMBER)as[invocation[identifier[PLACE SAVED]]];congruence. }
  destruct(gateway_actual_private_outcome_copy_views backend python objects decimal_float constructors older
    (gateway_reference_result(S(gateway_reference_depth context)))held reserved original fields wires metadata_field metadata wire
    before world(Vptr copy copy_offset)changed following observed WELL BUDGET VACANT HELD READY OWNED VALUE PRIVATE DESTROY RECEIVED
    METADATA META_VALUE WIRE OPERATION ltac:(discriminate))
    as(minted &MINT &MINT_WELL &MINT_OWNED &MINT_SCOPE &MINT_READY &MINT_FIELDS &MINT_META &FIELD_OUTSIDE &META_OUTSIDE &SNAPSHOT &MINT_BUDGET &RETURN).
  assert(MINT_ENTRIES:gateway_reference_entries minted=gateway_reference_entry(gateway_reference_next older)
    (gateway_reference_result(S(gateway_reference_depth context)))(Vptr copy copy_offset)::gateway_reference_entries older)
    by(exact(proj1(gateway_reference_mint_entries _ _ _ _ MINT))).
  assert(MINT_ENV:gateway_native_environment(fun current object=>gateway_native_private(python current)object)following changed environment).
  { intros identifier object ty LOOK;destruct(ENVIRONMENT identifier object ty LOOK)as[LIVE NATIVE];split.
    - eapply Mem.valid_block_unchanged_on;[exact(gateway_constructor_native _ _ _ _ _ _ _ _ RETURN)|exact LIVE].
    - eapply gateway_constructor_native_retained;[exact RETURN|exact LIVE|exact NATIVE]. }
  set(property:=fun memory current=>gateway_reference_scope python objects decimal_float minted held current /\
    gateway_objects_ready(python current)(objects current)memory /\
    gateway_native_environment(fun current object=>gateway_native_private(python current)object)current memory environment /\
    gateway_outcome_fields_view python objects decimal_float(Vptr copy copy_offset)fields wires current /\
    gateway_outcome_metadata_view python objects decimal_float(Vptr copy copy_offset)fields metadata_field metadata wire current /\
    forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count minted pointer<=python_native_strong(python current)pointer)%nat).
  assert(CLOSED:gateway_ambient_closed backend property).
  { intros memory current modified target[SCOPE_NOW[NORMAL[ENV_NOW[FIELDS_NOW[META_NOW BUDGET_NOW]]]]]AMBIENT.
    destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None memory current modified target NORMAL AMBIENT)as[NEXT[ACCESS FRAME]].
    pose proof(@gateway_reference_thread_ambient World Event backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects reference_threads None memory current modified target NORMAL AMBIENT)as EFFECT.
    split;[eapply gateway_reference_scope_thread_effect;eassumption|]. split;[exact NEXT|]. split.
    - intros identifier object ty LOOK;destruct(ENV_NOW identifier object ty LOOK)as[LIVE NATIVE];split;
        [eapply Mem.valid_block_unchanged_on;[exact FRAME|exact LIVE]|apply(proj1 ACCESS);assumption].
    - split;[eapply gateway_outcome_fields_view_frame;eassumption|]. split;[eapply gateway_outcome_metadata_view_frame;eassumption|].
      intro pointer;specialize(BUDGET_NOW pointer);pose proof(gateway_reference_thread_counts _ _ _ _ EFFECT pointer);lia. }
  destruct(gateway_actual_outcome_copy_capture_with_property backend ge python objects decimal_float property context environment parameters(Vptr copy copy_offset)
    changed following events value after next older minted(gateway_reference_next older)held reserved CLOSED
    (conj MINT_SCOPE(conj MINT_READY(conj MINT_ENV(conj MINT_FIELDS(conj MINT_META MINT_BUDGET)))))
    ltac:(intros memory current GOOD;exact(conj(proj1 GOOD)(proj2(proj2(proj2(proj2(proj2 GOOD)))))))
    STACK MINT_WELL MINT_ENTRIES RUN)
    as(stored &prefix &suffix &memory &current &EVENTS &POST &FORMED &ENTRIES &SCOPE &FINAL_BUDGET &BOUND &EXECUTION &SUFFIX).
  pose proof(gateway_reference_execution_erases _ _ _ _ _ _ _ _ EXECUTION)as PREFIX.
  destruct POST as[OLD_SCOPE[FINAL_READY[FINAL_ENV[FINAL_FIELDS[FINAL_METADATA ORIGINAL_BUDGET]]]]].
  exists stored,prefix,suffix,memory,current.
  exact(conj EVENTS(conj FORMED(conj ENTRIES(conj SCOPE(conj FINAL_READY(conj FINAL_ENV(conj FINAL_FIELDS
    (conj FINAL_METADATA(conj FINAL_BUDGET(conj BOUND(conj PREFIX SUFFIX))))))))))).
Qed.
