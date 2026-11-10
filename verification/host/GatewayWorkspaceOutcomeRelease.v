(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The same decoded-data release retains the original Workspace result. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine CallContexts ClightSteps StoreSteps LocalAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayPython GatewayObjects GatewayReferences GatewayValueOwnership
  GatewayObjectDiscipline GatewayObjectThreads GatewayTypeRuntime GatewayOutcomeAllocation GatewayOwnedOutcomeReturn GatewayOutcomeFields GatewayOutcomeMetadata
  GatewayOutcomePrivateReference GatewayWorkspaceOutcomeSource GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting
  GatewayReferenceNormalForm GatewayReferenceStackBound GatewayReferenceMoves GatewayReferenceThreads GatewayReferenceBalance GatewayPublicReferences GatewayAttachedReferences
  GatewayReferenceSourceExecution GatewaySourcePaths GatewaySourceSegments GatewayExternalFrontier GatewaySourceObjectReceipt GatewayFramedRuntime
  GatewayOperations GatewaySourceSegmentAutomation GatewayLocalRuntime GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.
Local Close Scope lean_scope.

Definition gateway_workspace_decoded_graph {World}(python:World->python_world)(objects:World->gateway_object_heap)data object current:Prop:=
  (0<python_native_strong(python current)data)%nat /\gateway_private_tree(objects current)data /\gateway_destructible(objects current)data /\
    ~gateway_object_reachable(objects current)data(Vptr object Ptrofs.zero).

Theorem gateway_workspace_decoded_graph_frame {World}python objects data object first last:
  @gateway_workspace_decoded_graph World python objects data object first->gateway_reference_thread_effect python objects first last->
  gateway_workspace_decoded_graph python objects data object last.
Proof.
  intros[OWNED[PRIVATE[SAFE OUTSIDE]]]EFFECT.
  assert(NEXT_OWNED:(0<python_native_strong(python last)data)%nat)by(pose proof(gateway_reference_thread_counts _ _ _ _ EFFECT data);lia).
  assert(ROOT:gateway_rooted(python first)(objects first)data)by(constructor;exact OWNED).
  assert(NEXT:gateway_rooted(python last)(objects last)data)by(constructor;exact NEXT_OWNED).
  destruct(gateway_private_tree_preserved _ _ _ _ _ PRIVATE SAFE ROOT NEXT
    (gateway_reference_thread_values _ _ _ _ EFFECT)(gateway_reference_thread_privacy _ _ _ _ EFFECT))as[NEXT_PRIVATE NEXT_SAFE].
  assert(NEXT_OUTSIDE:~gateway_object_reachable(objects last)data(Vptr object Ptrofs.zero)).
  { intro REACHED;apply OUTSIDE;eapply gateway_private_tree_reachable_back;
      [exact PRIVATE|exact SAFE|exact ROOT|exact NEXT|exact(gateway_reference_thread_values _ _ _ _ EFFECT)|
       exact(gateway_reference_thread_privacy _ _ _ _ EFFECT)|exact REACHED]. }
  exact(conj NEXT_OWNED(conj NEXT_PRIVATE(conj NEXT_SAFE NEXT_OUTSIDE))).
Qed.

Definition gateway_workspace_received_view {World}(python:World->python_world)(objects:World->gateway_object_heap)decimal_float
    copy fields wires metadata_field metadata wire data object current:Prop:=
  gateway_outcome_fields_view python objects decimal_float copy fields wires current /\
  gateway_outcome_metadata_view python objects decimal_float copy fields metadata_field metadata wire current /\
  gateway_workspace_decoded_graph python objects data object current.

Theorem gateway_workspace_received_view_frame {World}python objects decimal_float copy fields wires metadata_field metadata wire data object first last:
  @gateway_workspace_received_view World python objects decimal_float copy fields wires metadata_field metadata wire data object first->
  gateway_reference_thread_effect python objects first last->
  gateway_workspace_received_view python objects decimal_float copy fields wires metadata_field metadata wire data object last.
Proof.
  intros[FIELDS[METADATA ORIGINAL]]EFFECT;split;[eapply gateway_outcome_fields_view_frame;eassumption|].
  split;[eapply gateway_outcome_metadata_view_frame;eassumption|]. eapply gateway_workspace_decoded_graph_frame;eassumption.
Qed.

Theorem gateway_actual_workspace_decoded_release {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
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
    fields wires metadata_field metadata wire before world events value after next:
  is_call_cont context->parameters!_outcome=Some(Vptr object Ptrofs.zero)->parameters!_data=Some(Vptr data data_offset)->
  gateway_reference_stack_bound context older->gateway_reference_ledger_well_formed ledger->
  gateway_reference_entries ledger=
    gateway_reference_entry outcome_ticket(gateway_reference_temporary(gateway_reference_depth context)_outcome)(Vptr object Ptrofs.zero)::
    gateway_reference_entry copy_ticket(gateway_reference_cell object 16%Z)copy::
    gateway_reference_entry data_ticket(gateway_reference_temporary(gateway_reference_depth context)_data)(Vptr data data_offset)::
    gateway_reference_entries older->
  gateway_owned_outcome_return_context python objects instances owned decimal_float object copy class ledger
    (gateway_reference_temporary(gateway_reference_depth context)_outcome)outcome_ticket held before world->
  gateway_native_environment(fun current candidate=>gateway_native_private(python current)candidate)world before environment->
  gateway_workspace_received_view python objects decimal_float copy fields wires metadata_field metadata wire(Vptr data data_offset)object world->
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python world)pointer)%nat)->
  gateway_steps backend ge
    (gateway_live(Callstate gateway_reference_decref_definition[Vptr data data_offset]
      (gateway_workspace_data_release_cont environment parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists final prefix suffix memory current,
    events=prefix++suffix /\gateway_reference_ledger_well_formed final /\
    gateway_reference_entries final=
      gateway_reference_entry outcome_ticket(gateway_reference_temporary(gateway_reference_depth context)_outcome)(Vptr object Ptrofs.zero)::
      gateway_reference_entry copy_ticket(gateway_reference_cell object 16%Z)copy::gateway_reference_entries older /\
    gateway_owned_outcome_return_context python objects instances owned decimal_float object copy class final
      (gateway_reference_temporary(gateway_reference_depth context)_outcome)outcome_ticket(gateway_reference_without_held data_ticket held)memory current /\
    gateway_native_environment(fun current candidate=>gateway_native_private(python current)candidate)current memory environment /\
    gateway_outcome_fields_view python objects decimal_float copy fields wires current /\
    gateway_outcome_metadata_view python objects decimal_float copy fields metadata_field metadata wire current /\
    (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count final pointer<=python_native_strong(python current)pointer)%nat) /\
    gateway_reference_source_bound ge(plug_state(State f_host_workspace_execute gateway_workspace_outcome_return Kstop environment parameters memory)context)final /\
    gateway_steps backend ge
      (gateway_live(Callstate gateway_reference_decref_definition[Vptr data data_offset]
        (gateway_workspace_data_release_cont environment parameters)before)world)prefix
      (gateway_live(State f_host_workspace_execute gateway_workspace_outcome_return Kstop environment parameters memory)current) /\
    gateway_steps backend ge(gateway_live(State f_host_workspace_execute gateway_workspace_outcome_return Kstop environment parameters memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros CALL OUTCOME DATA STACK WELL ENTRIES INITIAL ENVIRONMENT VIEW BUDGET RUN.
  assert(DATA_OWNED:gateway_reference_owns ledger(gateway_reference_temporary(gateway_reference_depth context)_data)data_ticket(Vptr data data_offset))
    by(unfold gateway_reference_owns;rewrite ENTRIES;right;right;left;reflexivity).
  assert(OUTCOME_OWNED:gateway_reference_owns ledger(gateway_reference_temporary(gateway_reference_depth context)_outcome)outcome_ticket(Vptr object Ptrofs.zero))
    by(unfold gateway_reference_owns;rewrite ENTRIES;left;reflexivity).
  assert(COPY_OWNED:gateway_reference_owns ledger(gateway_reference_cell object 16%Z)copy_ticket copy)
    by(unfold gateway_reference_owns;rewrite ENTRIES;right;left;reflexivity).
  assert(OUTCOME_DIFFERENT:outcome_ticket<>data_ticket).
  { intro SAME;rewrite SAME in OUTCOME_OWNED.
    destruct(GatewayReferenceMoves.gateway_reference_owned_ticket_unique _ _ _ _ _ _ WELL OUTCOME_OWNED DATA_OWNED)as[OWNER POINTER];discriminate. }
  assert(COPY_DIFFERENT:copy_ticket<>data_ticket).
  { intro SAME;rewrite SAME in COPY_OWNED.
    destruct(GatewayReferenceMoves.gateway_reference_owned_ticket_unique _ _ _ _ _ _ WELL COPY_OWNED DATA_OWNED)as[OWNER POINTER];discriminate. }
  set(property:=fun memory current=>gateway_owned_outcome_return_context python objects instances owned decimal_float object copy class ledger
    (gateway_reference_temporary(gateway_reference_depth context)_outcome)outcome_ticket held memory current /\
    gateway_native_environment(fun current candidate=>gateway_native_private(python current)candidate)current memory environment /\
    gateway_workspace_received_view python objects decimal_float copy fields wires metadata_field metadata wire(Vptr data data_offset)object current /\
    forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python current)pointer)%nat).
  assert(CLOSED:gateway_ambient_closed backend property).
  { intros memory current changed following[CONTEXT[NATIVE[CURRENT COUNTED]]]AMBIENT;split.
    - eapply gateway_owned_outcome_return_context_ambient;[exact runtime|exact allocations|exact reference_threads|exact CONTEXT|exact AMBIENT].
    - destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None memory current changed following(proj1 CONTEXT)AMBIENT)as[NORMAL[ACCESS FRAME]].
      pose proof(@gateway_reference_thread_ambient World Event backend(fun current candidate=>gateway_native_private(python current)candidate)stable
        (gateway_python_discipline python objects detached)heap_allocation python objects reference_threads None memory current changed following(proj1 CONTEXT)AMBIENT)as EFFECT.
      split.
      + intros identifier candidate ty LOOK;destruct(NATIVE identifier candidate ty LOOK)as[LIVE PRIVATE];split;
          [eapply Mem.valid_block_unchanged_on;[exact FRAME|exact LIVE]|apply(proj1 ACCESS);assumption].
      + split;[eapply gateway_workspace_received_view_frame;eassumption|]. intro pointer;specialize(COUNTED pointer);pose proof(gateway_reference_thread_counts _ _ _ _ EFFECT pointer);lia. }
  destruct(gateway_actual_external_frontier backend ge _ _ _ _ [Vptr data data_offset](gateway_workspace_data_release_cont environment parameters)
    before world events value after next ltac:(exact I)ltac:(cbn;lia)RUN)
    as(pending &rest &called &owner &ignored &changed &following &observed &EVENTS &PENDING &PREFIX &RAW &REST).
  assert(AT_CALL:property called owner).
  { exact(gateway_pending_run_ready backend ge property CLOSED
      (Callstate gateway_reference_decref_definition[Vptr data data_offset](gateway_workspace_data_release_cont environment parameters)before)
      before world pending called owner(conj INITIAL(conj ENVIRONMENT(conj VIEW BUDGET)))PENDING PREFIX). }
  destruct AT_CALL as[CONTEXT[NATIVE[[FIELDS[METADATA[POSITIVE[PRIVATE[SAFE OUTSIDE]]]]]COUNTED]]].
  assert(OPERATION:gateway_object_operation backend gateway_api_decref[Vptr data data_offset]called owner ignored changed following observed)
    by(exists gateway_reference_decref_definition;split;[reflexivity|exact RAW]).
  destruct CONTEXT as[NORMAL[CELL[LOAD[CLASS[INSTANCE_SCOPE SCOPE]]]]].
  destruct(gateway_actual_decoded_graph_release_keeps_outcome backend python objects instances owned decimal_float references cells ledger
    (gateway_reference_temporary(gateway_reference_depth context)_data)data_ticket(Vptr data data_offset)object
    (gateway_reference_temporary(gateway_reference_depth context)_outcome)outcome_ticket(gateway_reference_cell object 16%Z)copy_ticket copy
    fields wires metadata_field metadata wire class held reserved called owner ignored changed following observed WELL SCOPE DATA_OWNED OUTCOME_OWNED COPY_OWNED
    OUTCOME_DIFFERENT COPY_DIFFERENT NORMAL PRIVATE SAFE CELL LOAD CLASS OUTSIDE FIELDS METADATA COUNTED OPERATION)
    as(final &RELEASE &FINAL_WELL &FINAL_SCOPE &FINAL_OWNER &FINAL_COPY &NEXT_READY &NEXT_CELL &NEXT_LOAD &NEXT_CLASS &NEXT_FIELDS &NEXT_META &NEXT_BUDGET).
  assert(FINAL_ENTRIES:gateway_reference_entries final=
    gateway_reference_entry outcome_ticket(gateway_reference_temporary(gateway_reference_depth context)_outcome)(Vptr object Ptrofs.zero)::
    gateway_reference_entry copy_ticket(gateway_reference_cell object 16%Z)copy::gateway_reference_entries older).
  { unfold gateway_reference_apply in RELEASE;rewrite ENTRIES in RELEASE;
      cbn[gateway_reference_take gateway_reference_entry gateway_reference_owner gateway_reference_pointer]in RELEASE.
    destruct(gateway_reference_place_eq(gateway_reference_temporary(gateway_reference_depth context)_data)
      (gateway_reference_temporary(gateway_reference_depth context)_outcome))as[BAD|OUTCOME_OTHER];[discriminate BAD|].
    destruct(gateway_reference_place_eq(gateway_reference_temporary(gateway_reference_depth context)_data)
      (gateway_reference_cell object 16%Z))as[BAD|COPY_OTHER];[discriminate BAD|].
    destruct(gateway_reference_place_eq(gateway_reference_temporary(gateway_reference_depth context)_data)
      (gateway_reference_temporary(gateway_reference_depth context)_data))as[OWNER_SELF|BAD];[|contradict BAD;reflexivity].
    cbn[gateway_reference_pointer gateway_reference_entry]in RELEASE.
    destruct(Val.eq(Vptr data data_offset)(Vptr data data_offset))as[VALUE_SELF|BAD];[|contradict BAD;reflexivity].
    injection RELEASE as FINAL_ID;subst final;reflexivity. }
  assert(LIVE:python_live(python owner)(Vptr data data_offset)).
  { exact(proj1(proj2(proj1 NORMAL))(Vptr data data_offset)ltac:(constructor;exact POSITIVE)). }
  pose proof(gateway_public_decref _ _ _ references called owner(Vptr data data_offset)ignored changed following observed
    (gateway_normal_attached _ _ _ NORMAL)POSITIVE LIVE OPERATION)as EFFECT.
  assert(NEXT_ENV:gateway_native_environment(fun current candidate=>gateway_native_private(python current)candidate)following changed environment).
  { intros identifier candidate ty LOOK;destruct(NATIVE identifier candidate ty LOOK)as[VALID NATIVE_NOW];split.
    - eapply Mem.valid_block_unchanged_on;[exact(gateway_attached_reference_native _ _ _ _ _ _ _ EFFECT)|exact VALID].
    - eapply gateway_attached_reference_native_retained;[exact EFFECT|exact VALID|exact NATIVE_NOW]. }
  set(post:=fun memory current=>gateway_owned_outcome_return_context python objects instances owned decimal_float object copy class final
    (gateway_reference_temporary(gateway_reference_depth context)_outcome)outcome_ticket(gateway_reference_without_held data_ticket held)memory current /\
    gateway_native_environment(fun current candidate=>gateway_native_private(python current)candidate)current memory environment /\
    gateway_outcome_fields_view python objects decimal_float copy fields wires current /\
    gateway_outcome_metadata_view python objects decimal_float copy fields metadata_field metadata wire current /\
    forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count final pointer<=python_native_strong(python current)pointer)%nat).
  assert(POST_CLOSED:gateway_ambient_closed backend post).
  { intros memory current modified target[BASE[NATIVE_NOW[FIELD_NOW[META_NOW COUNTED_NOW]]]]AMBIENT;split.
    - eapply gateway_owned_outcome_return_context_ambient;[exact runtime|exact allocations|exact reference_threads|exact BASE|exact AMBIENT].
    - destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None memory current modified target(proj1 BASE)AMBIENT)as[READY_NOW[ACCESS FRAME]].
      pose proof(@gateway_reference_thread_ambient World Event backend(fun current candidate=>gateway_native_private(python current)candidate)stable
        (gateway_python_discipline python objects detached)heap_allocation python objects reference_threads None memory current modified target(proj1 BASE)AMBIENT)as THREAD.
      split.
      + intros identifier candidate ty LOOK;destruct(NATIVE_NOW identifier candidate ty LOOK)as[VALID PRIVATE_NOW];split;
          [eapply Mem.valid_block_unchanged_on;[exact FRAME|exact VALID]|apply(proj1 ACCESS);assumption].
      + split;[eapply gateway_outcome_fields_view_frame;eassumption|]. split;[eapply gateway_outcome_metadata_view_frame;eassumption|].
        intro pointer;specialize(COUNTED_NOW pointer);pose proof(gateway_reference_thread_counts _ _ _ _ THREAD pointer);lia. }
  assert(SEGMENT:gateway_source_segment backend ge post(Returnstate ignored(gateway_workspace_data_release_cont environment parameters)changed)
    (State f_host_workspace_execute gateway_workspace_outcome_return Kstop environment parameters changed)post).
  { gateway_segment_dynamic POST_CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity). }
  assert(POST:post changed following).
  { split;[exact(conj NEXT_READY(conj NEXT_CELL(conj NEXT_LOAD(conj NEXT_CLASS(conj FINAL_OWNER FINAL_SCOPE)))))|].
    exact(conj NEXT_ENV(conj NEXT_FIELDS(conj NEXT_META NEXT_BUDGET))). }
  destruct(gateway_source_segment_cut backend ge _ _ _ _ SEGMENT changed following rest value after next POST REST)
    as(ending &suffix &memory &current &TAIL &QUIET &TO_RETURN &[FINAL_CONTEXT[FINAL_ENV[FIELD_FINAL[META_FINAL BUDGET_FINAL]]]]&SUFFIX).
  exists final,(pending++gateway_primitive observed::ending),suffix,memory,current.
  split;[rewrite EVENTS,TAIL,<-app_assoc;reflexivity|]. split;[exact FINAL_WELL|]. split;[exact FINAL_ENTRIES|]. split;[exact FINAL_CONTEXT|].
  split;[exact FINAL_ENV|]. split;[exact FIELD_FINAL|]. split;[exact META_FINAL|]. split;[exact BUDGET_FINAL|]. split.
  - intros entry MEMBER;rewrite FINAL_ENTRIES in MEMBER;destruct MEMBER as[SAME|[SAME|MEMBER]].
    + subst entry;eapply gateway_reference_temporary_binding;exact OUTCOME.
    + subst entry;exact(proj1(proj2(proj2 FINAL_CONTEXT))).
    + eapply gateway_reference_stack_local_bound;[exact STACK|exact MEMBER].
  - split.
    + eapply gateway_steps_append;[exact PREFIX|]. econstructor;[apply gateway_external_returned;exact RAW|exact TO_RETURN].
    + exact SUFFIX.
Qed.
