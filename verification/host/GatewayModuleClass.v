(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The source-created class, retained reference and C global agree. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayTypeRuntime
  GatewayRootLeases GatewayPython GatewayObjects GatewayOutcomeType GatewayModuleSource
  GatewayModuleRegions GatewayLoaderRegions GatewayThreadRuntime.
Require Import Machine ClightSteps StoreSteps LocalAccess.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_module_outcome_specification memory :
  gateway_module_descriptor_regions (Clight.globalenv prog) memory ->
  exists specification new initialize destroy traverse clear methods properties,
    Genv.find_symbol (Clight.globalenv prog) _host_outcome_spec = Some specification /\
    Genv.find_symbol (Clight.globalenv prog) _PyType_GenericNew = Some new /\
    Genv.find_symbol (Clight.globalenv prog) _host_outcome_init = Some initialize /\
    Genv.find_symbol (Clight.globalenv prog) _host_outcome_free = Some destroy /\
    Genv.find_symbol (Clight.globalenv prog) _host_outcome_traverse = Some traverse /\
    Genv.find_symbol (Clight.globalenv prog) _host_outcome_clear = Some clear /\
    Genv.find_symbol (Clight.globalenv prog) _host_outcome_methods = Some methods /\
    Genv.find_symbol (Clight.globalenv prog) _host_outcome_properties = Some properties /\
    gateway_type_spec_memory memory (Vptr specification Ptrofs.zero)
      (gateway_outcome_description new initialize destroy traverse clear methods properties).
Proof.
  intro REGIONS.
  destruct (REGIONS _host_outcome_spec v_host_outcome_spec eq_refl eq_refl
    ltac:(change (0 < 32); lia) ltac:(right; cbn; tauto)) as [specification SPECIFICATION].
  destruct (REGIONS _host_outcome_slots v_host_outcome_slots eq_refl eq_refl
    ltac:(change (0 < 128); lia) ltac:(right; cbn; tauto)) as [slots SLOTS].
  destruct (REGIONS ___stringlit_120 v___stringlit_120 eq_refl eq_refl
    ltac:(change (0 < 23); lia) ltac:(left; reflexivity)) as [name NAME].
  pose proof (gateway_loaded_region_cstring _ _ _ _ _ actual_outcome_name_literal NAME) as NAME_BYTES.
  destruct SPECIFICATION as [SPEC_DEF [SPEC_VOLATILE [SPEC_SYMBOL SPEC_REGION]]].
  destruct SLOTS as [SLOT_DEF [SLOT_VOLATILE [SLOT_SYMBOL SLOT_REGION]]].
  destruct NAME as [NAME_DEF [NAME_VOLATILE [NAME_SYMBOL NAME_REGION]]].
  destruct (gateway_outcome_type_regions memory specification slots name SLOT_SYMBOL NAME_SYMBOL
    (gateway_loaded_region_values _ _ _ _ SPEC_REGION)
    (gateway_loaded_region_values _ _ _ _ SLOT_REGION) NAME_BYTES)
    as [new [initialize [destroy [traverse [clear [methods [properties RESULT]]]]]]].
  exists specification, new, initialize, destroy, traverse, clear, methods, properties.
  split; [exact SPEC_SYMBOL |exact RESULT].
Qed.

Theorem gateway_actual_module_class_store ge python heap before temporaries continuation class symbol :
  gateway_objects_ready python heap before -> gateway_native_private python symbol ->
  gateway_module_descriptor_regions ge before -> Genv.find_symbol ge _host_outcome_class = Some symbol ->
  Mem.valid_access before Mptr symbol 0 Writable ->
  (exists object offset, class = Vptr object offset) ->
  exists after,
    store_path ge (fun _ => True)
      (Returnstate class (module_outcome_cont temporaries continuation) before) 4
      (State f_host_initialize module_outcome_rest continuation empty_env
        (PTree.set _t'11 class temporaries) after) /\
    Mem.store Mptr before symbol 0 class = Some after /\
    Mem.load Mptr after symbol 0 = Some class /\
    gateway_objects_ready python heap after /\ gateway_module_descriptor_regions ge after.
Proof.
  intros READY PRIVATE REGIONS SYMBOL ACCESS [object [offset CLASS]]; subst class.
  destruct (Mem.valid_access_store before Mptr symbol 0 (Vptr object offset) ACCESS) as [after STORE].
  exists after; split.
  - eapply store_next; [exact I |apply unchanged_store_edge, edge_returnstate |].
    eapply store_next; [exact I |apply unchanged_store_edge, edge_skip_seq |].
    eapply store_next; [exact I |eapply actual_module_outcome_store_edge;
      [exact SYMBOL |apply PTree.gss |repeat eexists |exact STORE] |].
    eapply store_next; [exact I |apply unchanged_store_edge, edge_skip_seq |constructor; exact I].
  - split; [exact STORE |]. split.
    + pose proof (Mem.load_store_same _ _ _ _ _ _ STORE) as LOAD;
        change (Mem.load Mptr after symbol 0 = Some (Vptr object offset)) in LOAD; exact LOAD.
    + split.
      * eapply gateway_owned_native_store_ready; eassumption.
      * eapply gateway_module_regions_global_store; [exact REGIONS | |exact SYMBOL |exact STORE].
        unfold gateway_module_mutable_globals; cbn; tauto.
Qed.

Theorem gateway_actual_module_outcome_type {World Event} (backend : gateway_backend World Event)
    python objects types allocator instances leases normal attached io native stable decimal_float
    (runtime : gateway_type_runtime backend python objects types allocator instances leases normal attached io native stable)
    (roots : gateway_root_lease_runtime backend python objects decimal_float leases)
    before world specification new initialize destroy traverse clear methods properties
    temporaries continuation result after next observed :
  normal before world ->
  gateway_type_spec_memory before (Vptr specification Ptrofs.zero)
    (gateway_outcome_description new initialize destroy traverse clear methods properties) ->
  gateway_step backend (Clight.globalenv prog)
    (gateway_live (Callstate (External
      (EF_external "PyType_FromSpec" (mksignature [Xptr] Xptr cc_default))
      [tptr (Tstruct __5268 noattr)] (tptr (Tstruct __object noattr)) cc_default)
      [Vptr specification Ptrofs.zero] (module_outcome_cont temporaries continuation) before) world)
    (gateway_primitive observed)
    (gateway_live (Returnstate result (module_outcome_cont temporaries continuation) after) next) ->
  result <> Vnullptr ->
  exists ticket object offset,
    result = Vptr object offset /\ normal after next /\
    types next result = Some (gateway_outcome_description new initialize destroy traverse clear methods properties) /\
    allocator next result /\ gateway_rooted (python next) (objects next) result /\
    gateway_reference_created leases world next result ticket.
Proof.
  intros NORMAL SPECIFICATION STEP NONNULL.
  assert (OPERATION : gateway_type_operation backend gateway_type_from_spec [Vptr specification Ptrofs.zero]
    before world result after next observed).
  { eexists; split; [reflexivity |]. inversion STEP; subst;
      cbn [gateway_runtime_operation]; eassumption. }
  destruct (@gateway_type_from_spec_effect World Event backend python objects types allocator instances leases
    normal attached io native stable runtime before world (Vptr specification Ptrofs.zero)
    (gateway_outcome_description new initialize destroy traverse clear methods properties)
    result after next observed NORMAL SPECIFICATION ltac:(cbn; lia) eq_refl OPERATION)
    as [ATTACHED [ACCESS [FRAME [QUIET [NULL |[ticket [CLEAR [TYPE [DEFAULT CREATED]]]]]]]]];
    [contradiction |].
  assert (ROOT : gateway_rooted (python next) (objects next) result).
  { eapply gateway_lease_rooted; [exact roots |exact (proj1 CREATED)]. }
  destruct (@gateway_type_attached World Event backend python objects types allocator instances leases
    normal attached io native stable runtime after next ATTACHED) as [GIL VALID].
  destruct (proj2 (proj2 (proj2 (proj2 VALID))) result ROOT) as [object [offset [VALUE POINTER]]].
  exists ticket, object, offset; split; [exact VALUE |]. split; [exact CLEAR |].
  split; [exact TYPE |]. split; [apply DEFAULT, gateway_outcome_allocator_is_default |].
  split; [exact ROOT |exact CREATED].
Qed.
