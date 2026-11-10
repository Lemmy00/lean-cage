(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The original Workspace consumes the constructed result on the same source return path. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayObjectDiscipline GatewayObjectThreads
  GatewayTypeRuntime GatewayOutcomeAllocation GatewayOwnedOutcomeReturn GatewayOutcomeFields GatewayOutcomeMetadata GatewayOutcomePrivateReference
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceNormalForm GatewayReferenceStackBound GatewayReferenceThreads
  GatewayPublicReferences GatewayReferenceSourceExecution GatewayWorkspaceOutcomeSource GatewayWorkspaceOutcomeCapture GatewayWorkspaceOutcomeRelease
  GatewayWorkspaceOutcomeReturn GatewayThreadRuntime GatewayStreamInterface GatewayLocalRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_actual_workspace_returns_constructed_outcome {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects types allocator instances leases owned decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (allocations:gateway_outcome_allocation_runtime backend python objects types allocator instances leases owned io
      (fun current candidate=>gateway_native_private(python current)candidate)stable)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (references:gateway_public_reference_runtime backend python objects)
    (cells:gateway_outcome_private_reference_runtime backend python objects instances owned)
    context older ledger outcome_ticket copy_ticket data_ticket held reserved environment parameters object copy class data data_offset
    fields wires metadata_field metadata wire before world events value after next release_symbol:
  is_call_cont context->parameters!_data=Some(Vptr data data_offset)->gateway_reference_stack_bound context older->
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_entries ledger=
    gateway_reference_entry outcome_ticket(gateway_reference_result(S(gateway_reference_depth context)))(Vptr object Ptrofs.zero)::
    gateway_reference_entry copy_ticket(gateway_reference_cell object 16%Z)copy::
    gateway_reference_entry data_ticket(gateway_reference_temporary(gateway_reference_depth context)_data)(Vptr data data_offset)::
    gateway_reference_entries older->
  gateway_owned_outcome_return_context python objects instances owned decimal_float object copy class ledger
    (gateway_reference_result(S(gateway_reference_depth context)))outcome_ticket held before world->
  gateway_native_environment(fun current candidate=>gateway_native_private(python current)candidate)world before environment->
  gateway_workspace_received_view python objects decimal_float copy fields wires metadata_field metadata wire(Vptr data data_offset)object world->
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python world)pointer)%nat)->
  environment!_Py_DecRef=None->Genv.find_symbol ge _Py_DecRef=Some release_symbol->
  Genv.find_funct_ptr ge release_symbol=Some gateway_reference_decref_definition->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vptr object Ptrofs.zero)(gateway_workspace_outcome_cont environment parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists final,
    value=Vptr object Ptrofs.zero /\gateway_reference_ledger_well_formed final /\
    gateway_reference_entries final=
      gateway_reference_entry outcome_ticket(gateway_reference_result(gateway_reference_depth context))(Vptr object Ptrofs.zero)::
      gateway_reference_entry copy_ticket(gateway_reference_cell object 16%Z)copy::gateway_reference_entries older /\
    gateway_reference_source_bound ge(Returnstate value context after)final /\
    gateway_owned_outcome_return_context python objects instances owned decimal_float object copy class final
      (gateway_reference_result(gateway_reference_depth context))outcome_ticket(gateway_reference_without_held data_ticket held)after next /\
    gateway_reference_owns final(gateway_reference_cell object 16%Z)copy_ticket copy /\
    gateway_outcome_fields_view python objects decimal_float copy fields wires next /\
    gateway_outcome_metadata_view python objects decimal_float copy fields metadata_field metadata wire next /\
    (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count final pointer<=python_native_strong(python next)pointer)%nat).
Proof.
  intros CALL DATA STACK WELL ENTRIES INITIAL ENVIRONMENT VIEW BUDGET LOCAL SYMBOL FUNCTION RUN.
  destruct(gateway_actual_workspace_captures_outcome backend ge python objects types allocator instances leases owned decimal_float detached io stable
    thread_errno heap_allocation runtime allocations reference_threads
    (gateway_workspace_received_view python objects decimal_float copy fields wires metadata_field metadata wire(Vptr data data_offset)object)
    ltac:(intros first last INITIAL_VIEW EFFECT;eapply gateway_workspace_received_view_frame;eassumption)
    context older ledger outcome_ticket copy_ticket data_ticket held reserved environment parameters object copy class data data_offset
    before world events value after next release_symbol CALL DATA STACK WELL ENTRIES INITIAL ENVIRONMENT VIEW BUDGET LOCAL SYMBOL FUNCTION RUN)
    as(captured &prefix &rest &called &current &EVENTS &CAPTURED_WELL &CAPTURED_ENTRIES &CAPTURED_CONTEXT &NATIVE &CAPTURED_VIEW &COUNTED &BOUND &PREFIX &REST).
  set(selected:=gateway_workspace_outcome_parameters parameters(Vptr object Ptrofs.zero)).
  assert(SELECTED_OUTCOME:selected!_outcome=Some(Vptr object Ptrofs.zero))by(apply PTree.gss).
  assert(SELECTED_DATA:selected!_data=Some(Vptr data data_offset)).
  { unfold selected,gateway_workspace_outcome_parameters;repeat rewrite PTree.gso by discriminate;exact DATA. }
  destruct(gateway_actual_workspace_decoded_release backend ge python objects types allocator instances leases owned decimal_float detached io stable
    thread_errno heap_allocation runtime allocations reference_threads references cells context older captured outcome_ticket copy_ticket data_ticket held reserved
    environment selected object copy class data data_offset fields wires metadata_field metadata wire called current rest value after next
    CALL SELECTED_OUTCOME SELECTED_DATA STACK CAPTURED_WELL CAPTURED_ENTRIES CAPTURED_CONTEXT NATIVE CAPTURED_VIEW COUNTED REST)
    as(released &cleanup &suffix &memory &owner &TAIL &RELEASED_WELL &RELEASED_ENTRIES &RELEASED_CONTEXT &RELEASED_ENV &FIELDS &METADATA &RELEASED_BUDGET &RELEASED_BOUND &CLEANUP &SUFFIX).
  destruct(gateway_actual_workspace_returned_outcome backend ge python objects types allocator instances leases owned decimal_float detached io stable
    thread_errno heap_allocation runtime allocations reference_threads context environment selected object copy class released outcome_ticket
    (gateway_reference_without_held data_ticket held)reserved fields wires metadata_field metadata wire memory owner suffix value after next
    CALL SELECTED_OUTCOME RELEASED_WELL RELEASED_BOUND RELEASED_ENV RELEASED_CONTEXT FIELDS METADATA RELEASED_BUDGET SUFFIX)
    as(final &SAME &FINAL_WELL &MOVE &EXECUTION &FINAL_CONTEXT &RESULT_BOUND &FINAL_FIELDS &FINAL_META &FINAL_BUDGET).
  pose proof(proj1(gateway_reference_head_move released final _ outcome_ticket
    (gateway_reference_temporary(gateway_reference_depth context)_outcome)(gateway_reference_result(gateway_reference_depth context))
    (Vptr object Ptrofs.zero)RELEASED_ENTRIES MOVE))as FINAL_ENTRIES.
  exists final;split;[exact SAME|]. split;[exact FINAL_WELL|]. split;[exact FINAL_ENTRIES|]. split.
  - intros entry MEMBER;rewrite FINAL_ENTRIES in MEMBER;destruct MEMBER as[IDENTICAL|[IDENTICAL|MEMBER]].
    + subst entry;rewrite SAME;apply gateway_reference_result_binding.
    + subst entry;exact(proj1(proj2(proj2 FINAL_CONTEXT))).
    + destruct(STACK entry MEMBER)as[invocation[identifier[PLACE SAVED]]];rewrite PLACE;exact SAVED.
  - split;[exact FINAL_CONTEXT|]. split.
    + unfold gateway_reference_owns;rewrite FINAL_ENTRIES;right;left;reflexivity.
    + exact(conj FINAL_FIELDS(conj FINAL_META FINAL_BUDGET)).
Qed.
