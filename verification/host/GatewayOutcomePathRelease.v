(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual Path release retains the copy ticket and received fields. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline GatewayObjectThreads
  GatewayPublicReferences GatewayAttachedReferences GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceMoves GatewayReferenceBalance
  GatewayReferenceHeld GatewayReferenceBorrowedGraph GatewayReferenceThreads GatewayReferenceRuntime GatewayReferenceSourceExecution GatewayOutcomeFields GatewayOutcomeMetadata
  GatewayOutcomePathSource GatewaySourceObjectReceipt GatewaySourceSegments GatewayOutcomeConstruction GatewayFramedRuntime GatewayContexts
  GatewayLocalRuntime GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_actual_outcome_path_release {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (references:gateway_public_reference_runtime backend python objects)
    invocation ledger copy_ticket path_ticket held reserved environment parameters copy copy_offset path path_offset fields wires metadata_field metadata wire
    before world events value after next symbol:
  parameters!_copy=Some(Vptr copy copy_offset)->parameters!_path=Some(Vptr path path_offset)->
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_owns ledger(gateway_reference_temporary invocation _copy)copy_ticket(Vptr copy copy_offset)->
  gateway_reference_owns ledger(gateway_reference_temporary invocation _path)path_ticket(Vptr path path_offset)->
  (forall captured,In captured held->gateway_held_ticket captured<>path_ticket)->
  gateway_objects_ready(python world)(objects world)before->gateway_reference_scope python objects decimal_float ledger held world->
  gateway_native_environment(fun current object=>gateway_native_private(python current)object)world before environment->
  gateway_outcome_fields_view python objects decimal_float(Vptr copy copy_offset)fields wires world->
  gateway_outcome_metadata_view python objects decimal_float(Vptr copy copy_offset)fields metadata_field metadata wire world->
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python world)pointer)%nat)->
  environment!_Py_DecRef=None->Genv.find_symbol ge _Py_DecRef=Some symbol->
  Genv.find_funct_ptr ge symbol=Some gateway_reference_decref_definition->
  gateway_steps backend ge(gateway_live(Returnstate(Vint Int.zero)(gateway_outcome_path_set_cont environment parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists final prefix suffix selected memory current,
    events=prefix++suffix /\gateway_reference_ledger_well_formed final /\
    gateway_reference_apply(gateway_reference_release(gateway_reference_temporary invocation _path)(Vptr path path_offset))
      (gateway_reference_valid ledger)=gateway_reference_valid final /\
    gateway_reference_owns final(gateway_reference_temporary invocation _copy)copy_ticket(Vptr copy copy_offset) /\
    gateway_objects_ready(python current)(objects current)memory /\gateway_reference_scope python objects decimal_float final held current /\
    gateway_native_environment(fun current object=>gateway_native_private(python current)object)current memory environment /\
    gateway_outcome_fields_view python objects decimal_float(Vptr copy copy_offset)fields wires current /\
    gateway_outcome_metadata_view python objects decimal_float(Vptr copy copy_offset)fields metadata_field metadata wire current /\
    (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count final pointer<=python_native_strong(python current)pointer)%nat) /\
    selected!_copy=Some(Vptr copy copy_offset) /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)(gateway_outcome_path_set_cont environment parameters)before)world)prefix
      (gateway_live(State f_host_outcome_from gateway_outcome_allocation_tail Kstop environment selected memory)current) /\
    gateway_steps backend ge
      (gateway_live(State f_host_outcome_from gateway_outcome_allocation_tail Kstop environment selected memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros COPY PATH WELL COPY_OWNED PATH_OWNED OTHER READY SCOPE ENVIRONMENT FIELDS METADATA BUDGET LOCAL SYMBOL FUNCTION RUN.
  assert(DIFFERENT:copy_ticket<>path_ticket).
  { intro SAME;rewrite SAME in COPY_OWNED.
    destruct(gateway_reference_owned_ticket_unique _ _ _ _ _ _ WELL COPY_OWNED PATH_OWNED)as[OWNER VALUE];discriminate. }
  set(property:=fun memory current=>gateway_objects_ready(python current)(objects current)memory /\
    gateway_reference_scope python objects decimal_float ledger held current /\
    gateway_native_environment(fun current object=>gateway_native_private(python current)object)current memory environment /\
    gateway_outcome_fields_view python objects decimal_float(Vptr copy copy_offset)fields wires current /\
    gateway_outcome_metadata_view python objects decimal_float(Vptr copy copy_offset)fields metadata_field metadata wire current /\
    forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python current)pointer)%nat).
  assert(CLOSED:gateway_ambient_closed backend property).
  { intros memory current changed following[NORMAL[SCOPE_NOW[ENV_NOW[FIELDS_NOW[META_NOW BUDGET_NOW]]]]]INTERFERENCE.
    destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None memory current changed following NORMAL INTERFERENCE)as[NEXT[ACCESS FRAME]].
    pose proof(@gateway_reference_thread_ambient World Event backend
      (fun current object=>gateway_native_private(python current)object)stable(gateway_python_discipline python objects detached)
      heap_allocation python objects reference_threads None memory current changed following NORMAL INTERFERENCE)as EFFECT.
    split;[exact NEXT|]. split;[eapply gateway_reference_scope_thread_effect;eassumption|]. split.
    - intros identifier object ty LOOK;destruct(ENV_NOW identifier object ty LOOK)as[LIVE PRIVATE];split;
        [eapply Mem.valid_block_unchanged_on;[exact FRAME|exact LIVE]|apply(proj1 ACCESS);assumption].
    - split;[eapply gateway_outcome_fields_view_frame;eassumption|]. split;[eapply gateway_outcome_metadata_view_frame;eassumption|].
      intro pointer;specialize(BUDGET_NOW pointer);pose proof(gateway_reference_thread_counts _ _ _ _ EFFECT pointer);lia. }
  destruct(gateway_outcome_path_release_source backend ge property environment parameters path path_offset Int.zero before symbol
    gateway_reference_decref_definition CLOSED PATH LOCAL SYMBOL FUNCTION eq_refl)
    as[selected[SOURCE[SELECTED_COPY[SELECTED_PATH[FAILED SELECTED_DATA]]]]].
  destruct(gateway_source_object_receipt backend ge gateway_api_decref gateway_reference_decref_definition[Vptr path path_offset]
    (gateway_outcome_path_release_cont environment selected)property _ before world events value after next eq_refl
    ltac:(exact I)ltac:(cbn;lia)CLOSED SOURCE
    (conj READY(conj SCOPE(conj ENVIRONMENT(conj FIELDS(conj METADATA BUDGET)))))RUN)
    as(prelude &rest &called &owner &ignored &changed &following &observed &EVENTS &CALLED &PREFIX &OPERATION &REST).
  destruct CALLED as[NORMAL[SCOPE_NOW[ENV_NOW[FIELDS_NOW[META_NOW BUDGET_NOW]]]]].
  destruct(gateway_public_release_keeps_independent_graphs backend python objects decimal_float references ledger
    (gateway_reference_temporary invocation _path)path_ticket(Vptr path path_offset)held called owner ignored changed following observed
    WELL(proj1 SCOPE_NOW)PATH_OWNED(gateway_normal_attached _ _ _ NORMAL)(proj2 SCOPE_NOW)OTHER OPERATION)
    as(final &RELEASE &FINAL_WELL &FIT &HELD &EFFECT &RETAINED).
  assert(FINAL_COPY:gateway_reference_owns final(gateway_reference_temporary invocation _copy)copy_ticket(Vptr copy copy_offset))
    by(apply RETAINED;assumption).
  assert(COPY_POSITIVE:(0<python_native_strong(python following)(Vptr copy copy_offset))%nat).
  { pose proof(gateway_reference_owned_count_positive _ _ _ _ FINAL_COPY);specialize(FIT(Vptr copy copy_offset));lia. }
  assert(AFTER_READY:gateway_objects_ready(python following)(objects following)changed).
  { destruct(gateway_attached_reference_ready _ _ _ _ _ _ _ EFFECT)as[VALID GIL];split;[exact VALID|]. split;[exact GIL|].
    rewrite(gateway_attached_reference_pending _ _ _ _ _ _ _ EFFECT);exact(proj2(proj2 NORMAL)). }
  assert(AFTER_FIELDS:gateway_outcome_fields_view python objects decimal_float(Vptr copy copy_offset)fields wires following).
  { eapply gateway_outcome_fields_view_kept;[exact FIELDS_NOW|exact COPY_POSITIVE|
      exact(gateway_attached_reference_values _ _ _ _ _ _ _ EFFECT)|exact(gateway_attached_reference_privacy _ _ _ _ _ _ _ EFFECT)]. }
  assert(AFTER_META:gateway_outcome_metadata_view python objects decimal_float(Vptr copy copy_offset)fields metadata_field metadata wire following).
  { eapply gateway_outcome_metadata_view_kept;[exact META_NOW|exact COPY_POSITIVE|
      exact(gateway_attached_reference_values _ _ _ _ _ _ _ EFFECT)|exact(gateway_attached_reference_privacy _ _ _ _ _ _ _ EFFECT)]. }
  assert(AFTER_ENV:gateway_native_environment(fun current object=>gateway_native_private(python current)object)following changed environment).
  { intros identifier object ty LOOK;destruct(ENV_NOW identifier object ty LOOK)as[LIVE PRIVATE];split.
    - eapply Mem.valid_block_unchanged_on;[exact(gateway_attached_reference_native _ _ _ _ _ _ _ EFFECT)|exact LIVE].
    - eapply gateway_attached_reference_native_retained;[exact EFFECT|exact LIVE|exact PRIVATE]. }
  assert(AFTER_BUDGET:forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count final pointer<=python_native_strong(python following)pointer)%nat).
  { eapply gateway_reference_balance_reservations;[exact BUDGET_NOW|].
    eapply gateway_reference_balance_release;[exact WELL|exact PATH_OWNED|exact RELEASE|
      exact(gateway_attached_reference_owned _ _ _ _ _ _ _ EFFECT)|exact(gateway_attached_reference_others _ _ _ _ _ _ _ EFFECT)]. }
  set(post:=fun memory current=>gateway_objects_ready(python current)(objects current)memory /\
    gateway_reference_scope python objects decimal_float final held current /\
    gateway_native_environment(fun current object=>gateway_native_private(python current)object)current memory environment /\
    gateway_outcome_fields_view python objects decimal_float(Vptr copy copy_offset)fields wires current /\
    gateway_outcome_metadata_view python objects decimal_float(Vptr copy copy_offset)fields metadata_field metadata wire current /\
    forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count final pointer<=python_native_strong(python current)pointer)%nat).
  assert(POST_CLOSED:gateway_ambient_closed backend post).
  { intros memory current changed_memory next_world[NORMAL_NOW[SCOPE_NEXT[ENV_NEXT[FIELD_NEXT[META_NEXT BUDGET_NEXT]]]]]INTERFERENCE.
    destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None memory current changed_memory next_world NORMAL_NOW INTERFERENCE)as[NEXT[ACCESS FRAME]].
    pose proof(@gateway_reference_thread_ambient World Event backend
      (fun current object=>gateway_native_private(python current)object)stable(gateway_python_discipline python objects detached)
      heap_allocation python objects reference_threads None memory current changed_memory next_world NORMAL_NOW INTERFERENCE)as THREAD.
    split;[exact NEXT|]. split;[eapply gateway_reference_scope_thread_effect;eassumption|]. split.
    - intros identifier object ty LOOK;destruct(ENV_NEXT identifier object ty LOOK)as[LIVE PRIVATE];split;
        [eapply Mem.valid_block_unchanged_on;[exact FRAME|exact LIVE]|apply(proj1 ACCESS);assumption].
    - split;[eapply gateway_outcome_fields_view_frame;eassumption|]. split;[eapply gateway_outcome_metadata_view_frame;eassumption|].
      intro pointer;specialize(BUDGET_NEXT pointer);pose proof(gateway_reference_thread_counts _ _ _ _ THREAD pointer);lia. }
  pose proof(gateway_outcome_path_installed_segment backend ge post environment selected ignored changed POST_CLOSED FAILED)as SEGMENT.
  destruct(gateway_source_segment_cut backend ge _ _ _ _ SEGMENT changed following rest value after next
    (conj AFTER_READY(conj(conj FIT HELD)(conj AFTER_ENV(conj AFTER_FIELDS(conj AFTER_META AFTER_BUDGET)))))REST)
    as(pending &suffix &memory &current &TAIL &QUIET &TO_ALLOC &[FINAL_READY[FINAL_SCOPE[FINAL_ENV[FINAL_FIELDS[FINAL_META FINAL_BUDGET]]]]]&SUFFIX).
  exists final,(prelude++gateway_primitive observed::pending),suffix,selected,memory,current.
  split;[rewrite EVENTS,TAIL,<-app_assoc;reflexivity|]. split;[exact FINAL_WELL|]. split;[exact RELEASE|]. split;[exact FINAL_COPY|].
  split;[exact FINAL_READY|]. split;[exact FINAL_SCOPE|]. split;[exact FINAL_ENV|]. split;[exact FINAL_FIELDS|]. split;[exact FINAL_META|].
  split;[exact FINAL_BUDGET|]. split;[rewrite SELECTED_COPY;exact COPY|]. split.
  - eapply gateway_steps_append;[exact PREFIX|]. econstructor.
    + destruct OPERATION as[definition[DEFINITION OPERATION]];inversion DEFINITION;subst definition;apply gateway_external_returned;exact OPERATION.
    + exact TO_ALLOC.
  - exact SUFFIX.
Qed.
