(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The original Workspace captures its actual instance credit before releasing decoded data. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine CallContexts ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayPython GatewayObjects GatewayObjectDiscipline GatewayObjectThreads
  GatewayTypeRuntime GatewayOutcomeAllocation GatewayOwnedOutcomeReturn GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting
  GatewayReferenceNormalForm GatewayReferenceStackBound GatewayReferenceFrames GatewayReferenceExecution GatewayReferenceThreads GatewayReferenceMoves
  GatewayReferenceCapture GatewayOutcomeCopyCapture GatewayReferenceCaptureObservation GatewayReferenceSourceExecution GatewayWorkspaceOutcomeSource
  GatewaySourcePaths GatewaySourceBoundCalls GatewaySourceSegmentAutomation GatewayFramedRuntime GatewayLocalRuntime GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_actual_workspace_captures_outcome {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects types allocator instances leases owned decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (allocations:gateway_outcome_allocation_runtime backend python objects types allocator instances leases owned io
      (fun current object=>gateway_native_private(python current)object)stable)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (view:World->Prop)(view_frame:forall first last,view first->gateway_reference_thread_effect python objects first last->view last)
    context older ledger outcome_ticket copy_ticket data_ticket held reserved environment parameters object copy class data data_offset
    before world events value after next release_symbol:
  is_call_cont context->parameters!_data=Some(Vptr data data_offset)->gateway_reference_stack_bound context older->
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_entries ledger=
    gateway_reference_entry outcome_ticket(gateway_reference_result(S(gateway_reference_depth context)))(Vptr object Ptrofs.zero)::
    gateway_reference_entry copy_ticket(gateway_reference_cell object 16%Z)copy::
    gateway_reference_entry data_ticket(gateway_reference_temporary(gateway_reference_depth context)_data)(Vptr data data_offset)::
    gateway_reference_entries older->
  gateway_owned_outcome_return_context python objects instances owned decimal_float object copy class ledger
    (gateway_reference_result(S(gateway_reference_depth context)))outcome_ticket held before world->
  gateway_native_environment(fun current object=>gateway_native_private(python current)object)world before environment->view world->
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python world)pointer)%nat)->
  environment!_Py_DecRef=None->Genv.find_symbol ge _Py_DecRef=Some release_symbol->
  Genv.find_funct_ptr ge release_symbol=Some gateway_reference_decref_definition->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vptr object Ptrofs.zero)(gateway_workspace_outcome_cont environment parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists stored prefix suffix memory current,
    events=prefix++suffix /\gateway_reference_ledger_well_formed stored /\
    gateway_reference_entries stored=
      gateway_reference_entry outcome_ticket(gateway_reference_temporary(gateway_reference_depth context)_outcome)(Vptr object Ptrofs.zero)::
      gateway_reference_entry copy_ticket(gateway_reference_cell object 16%Z)copy::
      gateway_reference_entry data_ticket(gateway_reference_temporary(gateway_reference_depth context)_data)(Vptr data data_offset)::
      gateway_reference_entries older /\
    gateway_owned_outcome_return_context python objects instances owned decimal_float object copy class stored
      (gateway_reference_temporary(gateway_reference_depth context)_outcome)outcome_ticket held memory current /\
    gateway_native_environment(fun current object=>gateway_native_private(python current)object)current memory environment /\view current /\
    (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count stored pointer<=python_native_strong(python current)pointer)%nat) /\
    gateway_reference_source_bound ge(plug_state(Callstate gateway_reference_decref_definition[Vptr data data_offset]
      (gateway_workspace_data_release_cont environment(gateway_workspace_outcome_parameters parameters(Vptr object Ptrofs.zero)))memory)context)stored /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vptr object Ptrofs.zero)(gateway_workspace_outcome_cont environment parameters)before)world)prefix
      (gateway_live(Callstate gateway_reference_decref_definition[Vptr data data_offset]
        (gateway_workspace_data_release_cont environment(gateway_workspace_outcome_parameters parameters(Vptr object Ptrofs.zero)))memory)current) /\
    gateway_steps backend ge
      (gateway_live(Callstate gateway_reference_decref_definition[Vptr data data_offset]
        (gateway_workspace_data_release_cont environment(gateway_workspace_outcome_parameters parameters(Vptr object Ptrofs.zero)))memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros CALL DATA STACK WELL ENTRIES INITIAL ENVIRONMENT VIEW BUDGET RELEASE_LOCAL RELEASE_SYMBOL RELEASE_FUNCTION RUN.
  assert(VACANT:forall identifier,identifier<>_data->
    gateway_reference_take(gateway_reference_temporary(gateway_reference_depth context)identifier)(gateway_reference_entries ledger)=None).
  { intros identifier DIFFERENT;apply gateway_reference_take_none;intros entry MEMBER OWNER;rewrite ENTRIES in MEMBER.
    destruct MEMBER as[SAME|[SAME|[SAME|MEMBER]]];try(subst entry;cbn in OWNER;congruence).
    apply(proj1(gateway_reference_take_none _ _)(GatewayOutcomeCopyCapture.gateway_reference_stack_current_vacant context older identifier STACK)entry MEMBER OWNER). }
  set(property:=fun memory current=>gateway_owned_outcome_return_context python objects instances owned decimal_float object copy class ledger
    (gateway_reference_result(S(gateway_reference_depth context)))outcome_ticket held memory current /\
    gateway_native_environment(fun current object=>gateway_native_private(python current)object)current memory environment /\view current /\
    forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python current)pointer)%nat).
  assert(CLOSED:gateway_ambient_closed backend property).
  { intros memory current changed following[CONTEXT[NATIVE[CURRENT COUNTED]]]AMBIENT;split.
    - eapply gateway_owned_outcome_return_context_ambient;[exact runtime|exact allocations|exact reference_threads|exact CONTEXT|exact AMBIENT].
    - destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None memory current changed following(proj1 CONTEXT)AMBIENT)as[NORMAL[ACCESS FRAME]].
      pose proof(@gateway_reference_thread_ambient World Event backend(fun current object=>gateway_native_private(python current)object)stable
        (gateway_python_discipline python objects detached)heap_allocation python objects reference_threads None memory current changed following(proj1 CONTEXT)AMBIENT)as EFFECT.
      split.
      + intros identifier candidate ty LOOK;destruct(NATIVE identifier candidate ty LOOK)as[LIVE PRIVATE];split;
          [eapply Mem.valid_block_unchanged_on;[exact FRAME|exact LIVE]|apply(proj1 ACCESS);assumption].
      + split;[eapply view_frame;eassumption|]. intro pointer;specialize(COUNTED pointer);pose proof(gateway_reference_thread_counts _ _ _ _ EFFECT pointer);lia. }
  destruct(gateway_actual_context_capture_scope backend ge python objects decimal_float property context f_host_workspace_execute environment parameters
    _t'31 _outcome(tptr(Tstruct __object noattr))(Kseq gateway_workspace_after_outcome Kstop)(Vptr object Ptrofs.zero)
    before world events value after next ledger outcome_ticket held reserved CALL CLOSED(conj INITIAL(conj ENVIRONMENT(conj VIEW BUDGET)))
    ltac:(discriminate)
    ltac:(intros memory current [CONTEXT [NATIVE_NOW [VIEW_NOW BUDGET_NOW]]];
      destruct CONTEXT as[NORMAL_NOW[CELL_NOW[LOAD_NOW[CLASS_NOW[OWNER_NOW SCOPE_NOW]]]]];exact(conj SCOPE_NOW BUDGET_NOW))
    WELL(proj1(proj2(proj2(proj2(proj2 INITIAL)))))(VACANT _t'31 ltac:(discriminate))(VACANT _outcome ltac:(discriminate))RUN)
    as(stored &capture_prefix &rest &captured &owner &EVENTS &CURRENT &STORED_WELL &STORED_OWNER &SCOPE &STORED_BUDGET &BOUND &COUNTS &
      [returned[RETURN_MOVE STORE_MOVE]] &RETAINED &CAPTURE &EXECUTION &REST).
  cbn[plug_cont gateway_reference_depth]in RETURN_MOVE,STORE_MOVE,STORED_OWNER,BOUND.
  destruct CURRENT as[CONTEXT[NATIVE[CURRENT COUNTED]]].
  destruct CONTEXT as[NORMAL[CELL[LOAD[CLASS[OWNED OLD_SCOPE]]]]].
  pose proof(proj1(gateway_reference_head_move ledger returned _ outcome_ticket
    (gateway_reference_result(S(gateway_reference_depth context)))
    (gateway_reference_temporary(gateway_reference_depth context)_t'31)(Vptr object Ptrofs.zero)ENTRIES RETURN_MOVE))as RETURNED_ENTRIES.
  pose proof(proj1(gateway_reference_head_move returned stored _ outcome_ticket
    (gateway_reference_temporary(gateway_reference_depth context)_t'31)
    (gateway_reference_temporary(gateway_reference_depth context)_outcome)(Vptr object Ptrofs.zero)RETURNED_ENTRIES STORE_MOVE))as STORED_ENTRIES.
  set(post:=fun memory current=>gateway_owned_outcome_return_context python objects instances owned decimal_float object copy class stored
    (gateway_reference_temporary(gateway_reference_depth context)_outcome)outcome_ticket held memory current /\
    gateway_native_environment(fun current object=>gateway_native_private(python current)object)current memory environment /\view current /\
    forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count stored pointer<=python_native_strong(python current)pointer)%nat).
  assert(POST_CLOSED:gateway_ambient_closed backend post).
  { intros memory current changed following[CONTEXT[NATIVE_NOW[VIEW_NOW COUNTED_NOW]]]AMBIENT;split.
    - eapply gateway_owned_outcome_return_context_ambient;[exact runtime|exact allocations|exact reference_threads|exact CONTEXT|exact AMBIENT].
    - destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None memory current changed following(proj1 CONTEXT)AMBIENT)as[NORMAL_NOW[ACCESS FRAME]].
      pose proof(@gateway_reference_thread_ambient World Event backend(fun current object=>gateway_native_private(python current)object)stable
        (gateway_python_discipline python objects detached)heap_allocation python objects reference_threads None memory current changed following(proj1 CONTEXT)AMBIENT)as EFFECT.
      split.
      + intros identifier candidate ty LOOK;destruct(NATIVE_NOW identifier candidate ty LOOK)as[LIVE PRIVATE];split;
          [eapply Mem.valid_block_unchanged_on;[exact FRAME|exact LIVE]|apply(proj1 ACCESS);assumption].
      + split;[eapply view_frame;eassumption|]. intro pointer;specialize(COUNTED_NOW pointer);pose proof(gateway_reference_thread_counts _ _ _ _ EFFECT pointer);lia. }
  assert(PATH:gateway_source_path backend ge gateway_reference_decref_definition[Vptr data data_offset]
    (gateway_workspace_data_release_cont environment(gateway_workspace_outcome_parameters parameters(Vptr object Ptrofs.zero)))post
    (State f_host_workspace_execute Sskip(Kseq gateway_workspace_after_outcome Kstop)environment
      (gateway_workspace_outcome_parameters parameters(Vptr object Ptrofs.zero))captured)post).
  { gateway_bound_source_call POST_CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
    eapply gateway_source_same with(target:=Callstate gateway_reference_decref_definition[Vptr data data_offset]
      (gateway_workspace_data_release_cont environment(gateway_workspace_outcome_parameters parameters(Vptr object Ptrofs.zero)))captured).
    - exact POST_CLOSED.
    - cbn;tauto.
    - intros;eapply certified_call_edge with(vf:=Vptr release_symbol Ptrofs.zero).
      + reflexivity.
      + apply old_expression_value;eapply value_function;[exact RELEASE_LOCAL|exact RELEASE_SYMBOL|reflexivity].
      + apply cons_argument_values with(v:=Vptr data data_offset).
        * apply old_expression_value,value_temp;unfold gateway_workspace_outcome_parameters;repeat rewrite PTree.gso by discriminate;exact DATA.
        * reflexivity.
        * apply no_argument_values.
      + change(Genv.find_funct_ptr ge release_symbol=Some gateway_reference_decref_definition);exact RELEASE_FUNCTION.
      + reflexivity.
    - apply gateway_source_reached;auto. }
  assert(POST:post captured owner).
  { split.
    - exact (conj NORMAL (conj CELL (conj LOAD (conj CLASS (conj STORED_OWNER SCOPE))))).
    - exact (conj NATIVE (conj CURRENT STORED_BUDGET)). }
  destruct(gateway_source_path_cut backend ge _ _ _ post _ post PATH captured owner rest value after next POST REST)
    as(pending &suffix &memory &current &TAIL &QUIET &TO_RELEASE &[FINAL_CONTEXT[FINAL_ENV[FINAL_VIEW FINAL_BUDGET]]]&SUFFIX).
  exists stored,(capture_prefix++pending),suffix,memory,current.
  split;[rewrite EVENTS,TAIL,<-app_assoc;reflexivity|]. split;[exact STORED_WELL|]. split;[exact STORED_ENTRIES|]. split;[exact FINAL_CONTEXT|].
  split;[exact FINAL_ENV|]. split;[exact FINAL_VIEW|]. split;[exact FINAL_BUDGET|]. split.
  - intros entry MEMBER;rewrite STORED_ENTRIES in MEMBER;destruct MEMBER as[SAME|[SAME|[SAME|MEMBER]]].
    + subst entry;cbn[gateway_reference_place_value plug_state gateway_workspace_data_release_cont plug_cont gateway_reference_saved_temporary gateway_reference_depth
        gateway_reference_owner gateway_reference_pointer gateway_reference_entry].
      destruct(Nat.eq_dec(gateway_reference_depth context)(gateway_reference_depth context));[apply PTree.gss|contradiction].
    + subst entry;exact(proj1(proj2(proj2 FINAL_CONTEXT))).
    + subst entry;cbn[gateway_reference_place_value plug_state gateway_workspace_data_release_cont plug_cont gateway_reference_saved_temporary gateway_reference_depth
        gateway_reference_owner gateway_reference_pointer gateway_reference_entry].
      destruct(Nat.eq_dec(gateway_reference_depth context)(gateway_reference_depth context));[|contradiction].
      unfold gateway_workspace_outcome_parameters;repeat rewrite PTree.gso by discriminate;exact DATA.
    + eapply gateway_reference_stack_nested_call_bound;[exact STACK|exact MEMBER].
  - split;[eapply gateway_steps_append;eassumption|exact SUFFIX].
Qed.
