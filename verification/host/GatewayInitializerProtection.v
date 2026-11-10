(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Actual ELF descriptors survive source-owned initialization writes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayLoaderRegions GatewayModuleRegions
  GatewayBootstrapRegions GatewayBootstrapBuffers GatewayBootstrapCapacities GatewayBootstrapRuntime
  GatewayBootstrapGuarantee GatewayBootstrapLoaderSetup GatewayBootstrapLoadedSetup GatewayBootstrapRealpathSetup
  GatewayBootstrapCanonicalSetup GatewayBootstrapReturn GatewayProtectedMemory GatewayProtectedThreads
  GatewayProtectedBootstrap GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_descriptor_object (ge : Clight.genv) (object : block) : Prop :=
  exists identifier variable,
    gateway_program_definition identifier global_definitions = Some (Gvar variable) /\
    gvar_volatile variable = false /\ 0 < init_data_list_size (gvar_init variable) /\
    gateway_module_descriptor identifier variable /\ Genv.find_symbol ge identifier = Some object.

Definition gateway_immutable_object (ge : Clight.genv) (object : block) : Prop :=
  exists identifier variable,
    gateway_program_definition identifier global_definitions = Some (Gvar variable) /\
    gvar_readonly variable = true /\ Genv.find_symbol ge identifier = Some object.

(* An at-load ELF permission fact, not a later descriptor-retention premise. *)
Definition gateway_native_readonly_mapping (ge : Clight.genv) (memory : mem) : Prop :=
  forall identifier variable object,
    gateway_program_definition identifier global_definitions = Some (Gvar variable) ->
    gvar_readonly variable = true -> Genv.find_symbol ge identifier = Some object ->
    forall position, ~ Mem.perm memory object position Cur Writable.

Theorem gateway_descriptors_initial {World} native ge memory world :
  gateway_native_loader_boundary ge memory -> gateway_native_readonly_mapping ge memory ->
  @gateway_native_storage_boundary World native ge memory world ->
  gateway_protected_memory native (gateway_descriptor_object ge) (gateway_immutable_object ge) memory memory world.
Proof.
  intros LOADER READONLY STORAGE.
  assert (VIEW : forall object, gateway_descriptor_object ge object ->
    exists identifier variable, gateway_module_descriptor identifier variable /\
      gateway_native_initializer_view ge identifier variable object memory).
  { intros object [identifier [variable [DEFINITION [NONVOLATILE [POSITIVE [SELECTED SYMBOL]]]]]].
    destruct (gateway_native_initialized ge memory LOADER identifier variable DEFINITION NONVOLATILE POSITIVE)
      as [actual INITIALIZER].
    assert (SAME : actual = object) by (destruct INITIALIZER as [_ [_ [BOUND REGION]]]; congruence).
    subst actual; exists identifier, variable; split; assumption. }
  constructor.
  - intros object GUARDED; destruct (VIEW object GUARDED) as [identifier [variable [SELECTED INITIALIZER]]].
    destruct INITIALIZER as [_ [_ [_ [BOUND READABLE BYTES VALUES]]]].
    eapply Mem.perm_valid_block; apply (READABLE 0); lia.
  - intros object GUARDED; destruct (VIEW object GUARDED) as [identifier [variable [SELECTED INITIALIZER]]].
    eapply gateway_loaded_native; [exact STORAGE |left; exact SELECTED |exact INITIALIZER].
  - intros object GUARDED [identifier [variable [DEFINITION [IMMUTABLE SYMBOL]]]].
    exact (READONLY identifier variable object DEFINITION IMMUTABLE SYMBOL).
  - apply Mem.unchanged_on_refl.
Qed.

Theorem gateway_descriptor_mutable_separate (ge : Clight.genv) written object :
  In written gateway_module_mutable_globals -> Genv.find_symbol ge written = Some object ->
  ~ gateway_descriptor_object ge object.
Proof.
  intros MUTABLE SYMBOL [identifier [variable [DEFINITION [NONVOLATILE [POSITIVE [SELECTED SAME]]]]]].
  assert (DIFFERENT : identifier <> written).
  { intro EQUAL; subst written; eapply actual_module_mutable_not_descriptor; eassumption. }
  eapply (Genv.global_addresses_distinct ge DIFFERENT SAME SYMBOL); reflexivity.
Qed.

Theorem gateway_bootstrap_protected_inputs {World} native stable discipline root engine results suffix executable results_literal
    memory world :
  Genv.find_symbol (Clight.globalenv prog) _host_root = Some root ->
  Genv.find_symbol (Clight.globalenv prog) _host_engine = Some engine ->
  Genv.find_symbol (Clight.globalenv prog) _host_default_results = Some results ->
  Genv.find_symbol (Clight.globalenv prog) _suffix = Some suffix ->
  Genv.find_symbol (Clight.globalenv prog) _executable = Some executable ->
  Genv.find_symbol (Clight.globalenv prog) _results = Some results_literal ->
  @gateway_protected_memory World native (gateway_descriptor_object (Clight.globalenv prog))
    (gateway_immutable_object (Clight.globalenv prog)) memory memory world ->
  gateway_bootstrap_buffers native stable discipline
    (bootstrap_loaded_capacities root engine results suffix executable results_literal)
    (bootstrap_loaded_literals suffix executable results_literal) memory world ->
  gateway_bootstrap_buffers
    (gateway_protected_native native (gateway_descriptor_object (Clight.globalenv prog))
      (gateway_immutable_object (Clight.globalenv prog))) stable
    (gateway_protected_discipline discipline native (gateway_descriptor_object (Clight.globalenv prog))
      (gateway_immutable_object (Clight.globalenv prog)) memory)
    (bootstrap_loaded_capacities root engine results suffix executable results_literal)
    (bootstrap_loaded_literals suffix executable results_literal) memory world.
Proof.
  intros ROOT ENGINE RESULTS SUFFIX EXECUTABLE RESULTS_LITERAL STATE [SIDE [CAPACITIES LITERALS]].
  assert (ROOT_SAFE : ~ gateway_descriptor_object (Clight.globalenv prog) root).
  { eapply gateway_descriptor_mutable_separate with (written := _host_root); [unfold gateway_module_mutable_globals; cbn; auto |exact ROOT]. }
  assert (ENGINE_SAFE : ~ gateway_descriptor_object (Clight.globalenv prog) engine).
  { eapply gateway_descriptor_mutable_separate with (written := _host_engine); [unfold gateway_module_mutable_globals; cbn; auto |exact ENGINE]. }
  assert (RESULTS_SAFE : ~ gateway_descriptor_object (Clight.globalenv prog) results).
  { eapply gateway_descriptor_mutable_separate with (written := _host_default_results); [unfold gateway_module_mutable_globals; cbn; auto |exact RESULTS]. }
  assert (SUFFIX_SAFE : gateway_immutable_object (Clight.globalenv prog) suffix).
  { exists _suffix, v_suffix; split; [reflexivity |split; [reflexivity |exact SUFFIX]]. }
  assert (EXECUTABLE_SAFE : gateway_immutable_object (Clight.globalenv prog) executable).
  { exists _executable, v_executable; split; [reflexivity |split; [reflexivity |exact EXECUTABLE]]. }
  assert (LITERAL_SAFE : gateway_immutable_object (Clight.globalenv prog) results_literal).
  { exists _results, v_results; split; [reflexivity |split; [reflexivity |exact RESULTS_LITERAL]]. }
  assert (SAFE : forall object amount access,
    In (object, amount, access) (bootstrap_loaded_capacities root engine results suffix executable results_literal) ->
    gateway_descriptor_object (Clight.globalenv prog) object -> gateway_immutable_object (Clight.globalenv prog) object).
  { intros object amount access MEMBER; unfold bootstrap_loaded_capacities in MEMBER; cbn [In] in MEMBER.
    repeat destruct MEMBER as [SAME |MEMBER]; try contradiction; inversion SAME; subst object amount access;
      intuition. }
  split; [split; assumption |]. split.
  - intros object amount access MEMBER; destruct (CAPACITIES object amount access MEMBER) as [PRIVATE REST].
    split; [split; [exact PRIVATE |eapply SAFE; exact MEMBER] |exact REST].
  - intros object bytes MEMBER; destruct (LITERALS object bytes MEMBER) as [actual [offset [POINTER [BYTES OWNED]]]].
    inversion POINTER; subst actual.
    assert (IMMUTABLE : gateway_immutable_object (Clight.globalenv prog) object).
    { unfold bootstrap_loaded_literals in MEMBER; cbn [In] in MEMBER.
      repeat destruct MEMBER as [SAME |MEMBER]; try contradiction; inversion SAME; subst object bytes; assumption. }
    exists object, offset; split; [exact POINTER |]. split; [exact BYTES |].
    intros position RANGE; destruct (OWNED position RANGE) as [PRIVATE |READONLY];
      [left; split; [exact PRIVATE |intros; exact IMMUTABLE] |right; exact READONLY].
Qed.

Theorem gateway_bootstrap_named_unprotect {World} native discipline protected immutable snapshot module_filename canonicalizes
    entry root engine results memory world :
  @gateway_bootstrap_named_paths World (gateway_protected_native native protected immutable)
    (gateway_protected_discipline discipline native protected immutable snapshot)
    module_filename canonicalizes entry root engine results memory world ->
  gateway_bootstrap_named_paths native discipline module_filename canonicalizes entry root engine results memory world /\
  gateway_protected_memory native protected immutable snapshot memory world.
Proof.
  intros [original [located [LOADER [ORIGINAL_SIZE [ORIGINAL_SLASH [ORIGINAL_SUFFIX
    [canonical [before [resolved [CANONICAL [CANONICAL_SIZE [CANONICAL_SLASH [CANONICAL_SUFFIX
      [[SIDE SNAPSHOT] [[ROOT [ENGINE RESULTS]] STRINGS]]]]]]]]]]]]]]].
  split; [|exact SNAPSHOT].
  exists original, located; split; [exact LOADER |]. split; [exact ORIGINAL_SIZE |].
  split; [exact ORIGINAL_SLASH |]. split; [exact ORIGINAL_SUFFIX |].
  exists canonical, before, resolved; split; [exact CANONICAL |]. split; [exact CANONICAL_SIZE |].
  split; [exact CANONICAL_SLASH |]. split; [exact CANONICAL_SUFFIX |].
  split; [exact SIDE |]. split; [|exact STRINGS].
  split; [|split]; destruct ROOT as [ROOT_PRIVATE ROOT_CAP]; destruct ENGINE as [ENGINE_PRIVATE ENGINE_CAP];
    destruct RESULTS as [RESULTS_PRIVATE RESULTS_CAP].
  - split; [exact (proj1 ROOT_PRIVATE) |exact ROOT_CAP].
  - split; [exact (proj1 ENGINE_PRIVATE) |exact ENGINE_CAP].
  - split; [exact (proj1 RESULTS_PRIVATE) |exact RESULTS_CAP].
Qed.

Theorem gateway_protected_descriptors {World} native ge snapshot memory world :
  gateway_module_descriptor_regions ge snapshot ->
  @gateway_protected_memory World native (gateway_descriptor_object ge) (gateway_immutable_object ge) snapshot memory world ->
  gateway_module_descriptor_regions ge memory.
Proof.
  intros REGIONS STATE; eapply gateway_module_regions_retained; [exact REGIONS |].
  intros identifier variable object SELECTED INITIALIZER.
  destruct INITIALIZER as [DEFINITION [NONVOLATILE [SYMBOL REGION]]].
  eapply Mem.unchanged_on_implies; [eapply gateway_protected_snapshot; exact STATE |].
  intros candidate position SAME; subst candidate.
  exists identifier, variable; split; [exact DEFINITION |]. split; [exact NONVOLATILE |].
  split; [exact (proj1 (gateway_loaded_region_bound _ _ _ _ REGION)) |]. split; assumption.
Qed.
