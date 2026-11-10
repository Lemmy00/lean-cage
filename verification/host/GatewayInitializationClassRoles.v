(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Native class-cell roles come from the same loaded
  caller. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayMachine GatewayLoaderRegions GatewayModuleRegions
  GatewayBootstrapHistory GatewayBootstrapRegions GatewayInitializerProtection GatewayBootstrapReferenceScope GatewayBootstrapRuntime GatewayBootstrapReference
  GatewayInitializationConnection GatewayInitializationRegions GatewayBootstrapFlagged GatewayBootstrapLoaderSetup
  GatewayReferenceHistoryThreads GatewayReferenceThreads GatewayThreadRuntime GatewayNativeRegions GatewayRegionThreads
  GatewayInterpreterRuntime GatewayInitializerNativeRoles.
Import ListNotations.
Open Scope Z_scope.
Local Opaque Clight.globalenv Genv.find_symbol.

Definition gateway_initializer_class_name identifier:Prop:=
  In identifier[_host_path_class;_host_cancellation_class;_host_outcome_class].
Definition gateway_initializer_class_region(ge:Clight.genv)(object:block)(_position:Z):Prop:=
  exists identifier,gateway_initializer_class_name identifier /\Genv.find_symbol ge identifier=Some object.

Lemma gateway_initializer_class_registration identifier:
  gateway_initializer_class_name identifier ->exists variable,
    gateway_program_definition identifier global_definitions=Some(Gvar variable) /\gvar_volatile variable=false /\
    0<init_data_list_size(gvar_init variable) /\In identifier gateway_module_mutable_globals.
Proof.
  intros[NAME|[NAME|[NAME|BAD]]];try contradiction;subst identifier.
  all:eexists;split;[reflexivity|].
  all:split;[reflexivity|].
  all:split;[change(0<8);lia|].
  all:unfold gateway_module_mutable_globals;cbn;auto 12.
Qed.

Theorem gateway_initializer_classes_loaded {World}native memory(world:World):
  gateway_native_loader_boundary(Clight.globalenv prog)memory ->
  gateway_native_storage_boundary native(Clight.globalenv prog)memory world ->
  gateway_native_region_owned native(gateway_initializer_class_region(Clight.globalenv prog))memory world.
Proof.
  intros LOADER STORAGE object position(identifier &NAME &SYMBOL).
  destruct(gateway_initializer_class_registration identifier NAME)as(variable &DEFINITION &NONVOLATILE &POSITIVE &MUTABLE).
  destruct(gateway_native_initialized _ _ LOADER identifier variable DEFINITION NONVOLATILE POSITIVE)as(actual &VIEW).
  assert(SAME:actual=object)by(destruct VIEW as(_ & _ &ACTUAL & _);congruence);subst actual.
  split.
  - destruct VIEW as[_[_[_[BOUND READABLE BYTES VALUES]]]].
    eapply Mem.perm_valid_block;apply(READABLE 0);lia.
  - eapply gateway_loaded_native;[exact STORAGE|right;exact MUTABLE|exact VIEW].
Qed.

Theorem gateway_actual_public_bootstrap_class_roles {World Event}(backend:gateway_backend World Event)
    io native stable base thread_errno heap_allocation python objects current identifier module_filename canonicalizes
    (threads:gateway_thread_runtime backend io native stable base thread_errno)
    (reference_threads:gateway_reference_thread_contract backend native stable base heap_allocation python objects)
    (interpreter:gateway_interpreter_runtime backend io native stable base python objects current identifier)
    (runtime:gateway_bootstrap_runtime backend io native stable base module_filename canonicalizes)
    (profile:gateway_bootstrap_python_profile native base python objects)
    (references:gateway_bootstrap_reference_runtime backend python objects)
    decimal_float ledger retired held before world events value after next:
  gateway_native_loader_boundary(Clight.globalenv prog)before ->
  gateway_native_readonly_mapping(Clight.globalenv prog)before ->
  gateway_native_storage_boundary native(Clight.globalenv prog)before world ->base None before world ->
  gateway_reference_history_scope python objects decimal_float ledger retired held world ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_PyInit__host)[]Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  identifier world=Int64.zero /\exists symbols entry parameters outer_parameters prefix bootstrap suffix called called_world changed changed_world,
    events=prefix++bootstrap++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_PyInit__host)[]Kstop before)world)prefix
      (gateway_live(Callstate(Internal f_host_bootstrap)[]
        (CallContexts.plug_cont(GatewayInitializationBootstrap.initializer_bootstrap_cont parameters)
          (GatewayInitializationEntrySource.initialization_body_cont outer_parameters))called)called_world) /\
    gateway_steps backend(Clight.globalenv prog)(gateway_live(Callstate(Internal f_host_bootstrap)[]Kstop called)called_world)bootstrap
      (gateway_live(Returnstate(Vint Int.zero)Kstop changed)changed_world) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)
        (CallContexts.plug_cont(GatewayInitializationBootstrap.initializer_bootstrap_cont parameters)
          (GatewayInitializationEntrySource.initialization_body_cont outer_parameters))changed)changed_world)suffix
      (gateway_live(Returnstate value Kstop after)next) /\
    Genv.find_symbol(Clight.globalenv prog)_PyInit__host=Some entry /\
    gateway_bootstrap_named_paths native base module_filename canonicalizes entry
      (initialization_root symbols)(initialization_engine symbols)(initialization_results symbols)changed changed_world /\
    gateway_module_descriptor_regions(Clight.globalenv prog)changed /\
    gateway_reference_history_scope python objects decimal_float ledger retired held changed_world /\
    gateway_initialization_flag_state native base symbols Int.one Int.zero changed changed_world /\
    gateway_native_region_owned native(gateway_initializer_class_region(Clight.globalenv prog))changed changed_world.
Proof.
  intros LOADER READONLY STORAGE INITIAL HISTORY RUN NONNULL.
  set(region:=gateway_initializer_class_region(Clight.globalenv prog)).
  set(side:=gateway_native_region_discipline native base region).
  assert(HELD:gateway_native_region_owned native region before world)
    by(exact(gateway_initializer_classes_loaded native before world LOADER STORAGE)).
  pose proof(gateway_thread_with_native_region backend io native stable base thread_errno threads region)as THREADS.
  pose proof(@gateway_reference_threads_with_native_roles World Event backend native stable base region
    heap_allocation python objects reference_threads)as REFERENCE_THREADS.
  pose proof(gateway_interpreter_with_native_roles backend io native stable base region python objects current identifier interpreter)as INTERPRETER.
  pose proof(gateway_bootstrap_with_native_roles backend io native stable base region module_filename canonicalizes runtime)as RUNTIME.
  pose proof(@gateway_bootstrap_profile_with_native_roles World native base region python objects profile)as PROFILE.
  destruct(gateway_actual_public_bootstrap_connection backend io native stable side thread_errno heap_allocation python objects current identifier
    module_filename canonicalizes THREADS REFERENCE_THREADS INTERPRETER RUNTIME PROFILE references
    decimal_float ledger retired held before world events value after next LOADER READONLY STORAGE(conj INITIAL HELD)HISTORY RUN NONNULL)
    as[MAIN(symbols &entry &parameters &outer_parameters &prefix &bootstrap &suffix &called &called_world &changed &changed_world
      &EVENTS &PREFIX &BOOTSTRAP &SUFFIX &ENTRY &PATHS &DESCRIPTORS &FINAL_HISTORY &FLAGS)].
  pose proof(initialization_flags_side _ _ _ _ _ _ _ FLAGS)as[FINAL_SIDE FINAL_ROLES].
  assert(BASE_PATHS:gateway_bootstrap_named_paths native base module_filename canonicalizes entry
    (initialization_root symbols)(initialization_engine symbols)(initialization_results symbols)changed changed_world).
  { exact(proj2(gateway_bootstrap_named_discipline native side base module_filename canonicalizes entry
      (initialization_root symbols)(initialization_engine symbols)(initialization_results symbols)changed changed_world
      ltac:(intros mode memory owner[BASE OWNED];exact BASE)PATHS)). }
  assert(BASE_FLAGS:gateway_initialization_flag_state native base symbols Int.one Int.zero changed changed_world).
  { destruct FLAGS as[SIDE ACTIVE_CAPACITY COMPLETE_CAPACITY ACTIVE_VALUE COMPLETE_VALUE];constructor;try assumption;exact FINAL_SIDE. }
  split;[exact MAIN|]. exists symbols,entry,parameters,outer_parameters,prefix,bootstrap,suffix,called,called_world,changed,changed_world.
  exact(conj EVENTS(conj PREFIX(conj BOOTSTRAP(conj SUFFIX(conj ENTRY(conj BASE_PATHS
    (conj DESCRIPTORS(conj FINAL_HISTORY(conj BASE_FLAGS FINAL_ROLES))))))))).
Qed.
