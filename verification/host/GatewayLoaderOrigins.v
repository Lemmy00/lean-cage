(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Loaded storage and relocations supply the actual entry scope. *)
From Stdlib Require Import ZArith List Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayLoaderRegions GatewayGlobalAddresses
  GatewayPointerOrigins GatewayPointerMemory GatewayPointerControl GatewayModuleRegions GatewayBootstrapRegions
  GatewayLinkedSource.
Import ListNotations.

Definition gateway_loaded_relocation (ge : Clight.genv) object : Prop :=
  exists owner variable identifier delta,
    In (owner, Gvar variable) global_definitions /\ In (Init_addrof identifier delta) (gvar_init variable) /\
    Genv.find_symbol ge identifier = Some object.

Definition gateway_loaded_runtime_symbol (ge : Clight.genv) (runtime : list (ident * Ctypes.fundef function)) object : Prop :=
  exists identifier definition, In (identifier, definition) runtime /\ Genv.find_symbol ge identifier = Some object.

(* A per-fragment at-load ABI observation, not a later application frame. *)
Definition gateway_loaded_value_origin ge runtime storage value : Prop :=
  match value with
  | Vptr object _ => storage object \/ gateway_loaded_relocation ge object \/ gateway_loaded_runtime_symbol ge runtime object
  | _ => True
  end.

Definition gateway_loaded_fragment_origins ge runtime storage memory : Prop :=
  forall object offset value quantity index,
    ZMap.get offset (PMap.get object (Mem.mem_contents memory)) = Fragment value quantity index ->
    gateway_loaded_value_origin ge runtime storage value /\
    match value with Vptr target _ => Mem.valid_block memory target | _ => True end.

Theorem gateway_private_name_mutable identifier :
  gateway_private_cell_name identifier = true -> In identifier gateway_module_mutable_globals.
Proof.
  unfold gateway_private_cell_name; intro SELECTED; apply existsb_exists in SELECTED.
  destruct SELECTED as [name [MEMBER SAME]]; apply Pos.eqb_eq in SAME; subst name.
  cbn [In] in MEMBER; repeat destruct MEMBER as [SAME |MEMBER]; try contradiction; subst identifier;
    unfold gateway_module_mutable_globals; cbn; tauto.
Qed.

Theorem gateway_loaded_private_cell_native {World} ge memory (native : World -> block -> Prop) world object :
  gateway_native_loader_boundary ge memory -> gateway_native_storage_boundary native ge memory world ->
  gateway_private_cell ge object -> native world object.
Proof.
  intros LOADER STORAGE [identifier [PRIVATE SYMBOL]].
  destruct (gateway_private_cell_initializers identifier PRIVATE) as [variable [DEFINITION [NONVOLATILE POSITIVE]]].
  destruct (gateway_native_initialized ge memory LOADER identifier variable DEFINITION NONVOLATILE POSITIVE)
    as [actual VIEW].
  assert (SAME : actual = object) by (destruct VIEW as [_ [_ [BOUND REGION]]]; congruence); subst actual.
  eapply gateway_loaded_native; [exact STORAGE |right; apply gateway_private_name_mutable; exact PRIVATE |exact VIEW].
Qed.

Theorem gateway_loaded_relocation_avoids ge object :
  gateway_loaded_relocation ge object -> ~ gateway_private_cell ge object.
Proof.
  intros [owner [variable [identifier [delta [SOURCE [RELOCATION SYMBOL]]]]]]
    [private [PRIVATE SAME]].
  assert (DIFFERENT : identifier <> private).
  { intro EQUAL; subst identifier; exact (gateway_actual_initializer_address_absent owner variable delta private SOURCE PRIVATE RELOCATION). }
  exact (Genv.global_addresses_distinct ge DIFFERENT SYMBOL SAME eq_refl).
Qed.

Theorem gateway_loaded_runtime_symbol_avoids ge runtime object :
  gateway_runtime_registration runtime -> gateway_loaded_runtime_symbol ge runtime object -> ~ gateway_private_cell ge object.
Proof.
  intros [_ [_ SEPARATE]] [identifier [definition [RUNTIME SYMBOL]]] [private [PRIVATE SAME]].
  destruct (gateway_private_cell_initializers private PRIVATE) as [variable [DEFINITION REST]].
  pose proof (gateway_program_definition_present _ _ _ DEFINITION) as SOURCE.
  assert (DIFFERENT : private <> identifier).
  { apply SEPARATE.
    - apply in_map_iff; exists (private, Gvar variable); split; [reflexivity |exact SOURCE].
    - apply in_map_iff; exists (identifier, definition); split; [reflexivity |exact RUNTIME]. }
  exact (Genv.global_addresses_distinct ge DIFFERENT SAME SYMBOL eq_refl).
Qed.

Theorem gateway_loaded_memory_origin {World} ge runtime memory storage (native : World -> block -> Prop) world :
  gateway_runtime_registration runtime -> gateway_native_loader_boundary ge memory ->
  gateway_native_storage_boundary native ge memory world ->
  (forall object, storage object -> ~ native world object) ->
  gateway_loaded_fragment_origins ge runtime storage memory ->
  gateway_memory_avoids (gateway_private_cell ge) memory.
Proof.
  intros REGISTERED LOADER NATIVE STORAGE ORIGINS object offset.
  destruct (ZMap.get offset (PMap.get object (Mem.mem_contents memory))) as [|byte |value quantity index] eqn:CONTENTS;
    try exact I.
  destruct (ORIGINS object offset value quantity index CONTENTS) as [ORIGIN ALLOCATED].
  destruct value; try exact I.
  destruct ORIGIN as [RUNTIME |[RELOCATION |SYMBOL]].
  - intro PRIVATE; apply (STORAGE b RUNTIME); eapply gateway_loaded_private_cell_native; eassumption.
  - apply gateway_loaded_relocation_avoids; exact RELOCATION.
  - eapply gateway_loaded_runtime_symbol_avoids; eassumption.
Qed.

Theorem gateway_loaded_initializer_pointer_scope {World} runtime memory storage
    (native : World -> block -> Prop) world :
  gateway_runtime_registration runtime ->
  gateway_native_loader_boundary (Clight.globalenv (gateway_linked_program runtime)) memory ->
  gateway_native_storage_boundary native (Clight.globalenv (gateway_linked_program runtime)) memory world ->
  (forall object, storage object -> ~ native world object) ->
  gateway_loaded_fragment_origins (Clight.globalenv (gateway_linked_program runtime)) runtime storage memory ->
  gateway_pointer_source (Clight.globalenv (gateway_linked_program runtime))
    (Callstate (Internal f_PyInit__host) [] Kstop memory).
Proof.
  intros REGISTERED LOADER NATIVE STORAGE ORIGINS; split.
  - eapply gateway_loaded_memory_origin; eassumption.
  - split; [apply gateway_loaded_private_cells_valid; exact LOADER |].
    split; [vm_compute; reflexivity |split; [exact I |constructor]].
Qed.
