(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Validation uses the retained source table and field-name bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayRegistry GatewayGlobals
  GatewayLoaderRegions GatewayInitializerRetention GatewayModuleRegions GatewayBootstrapRegions GatewayNativeRegions
  GatewayOutcome GatewayOutcomeGetsets GatewayGetsets GatewayOutcomeValidationContext GatewayOutcomeValidationPaths GatewayErrorRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition gateway_validation_source_region (ge : Clight.genv) (object : block) (_ : Z) : Prop :=
  exists identifier variable,
    gateway_program_definition identifier global_definitions = Some (Gvar variable) /\
    gvar_volatile variable = false /\ 0 < init_data_list_size (gvar_init variable) /\
    gateway_module_descriptor identifier variable /\ Genv.find_symbol ge identifier = Some object.

Theorem gateway_validation_source_region_loaded {World} (python : World -> python_world) ge memory world :
  gateway_native_loader_boundary ge memory ->
  gateway_native_storage_boundary (fun current object => gateway_native_private (python current) object) ge memory world ->
  gateway_native_region_owned (fun current object => gateway_native_private (python current) object)
    (gateway_validation_source_region ge) memory world.
Proof.
  intros LOADER STORAGE object position [identifier [variable [DEFINITION [NONVOLATILE [POSITIVE [DESCRIPTOR SYMBOL]]]]]].
  destruct (gateway_native_initialized _ _ LOADER identifier variable DEFINITION NONVOLATILE POSITIVE) as [actual VIEW].
  assert (SAME : actual = object) by (destruct VIEW as [_ [_ [BINDING REGION]]]; congruence); subst actual.
  split.
  - eapply gateway_loaded_region_live; exact (proj2 (proj2 (proj2 VIEW))).
  - exact (gateway_loaded_native (fun current object => gateway_native_private (python current) object)
      ge memory world STORAGE identifier variable object (or_introl DESCRIPTOR) VIEW).
Qed.

Theorem gateway_validation_current_regions {World} python objects decimal_float ledger held reserved captured original source environment memory world :
  @gateway_outcome_validation_context World python objects decimal_float ledger held reserved captured original
    (gateway_validation_source_region (Clight.globalenv prog)) source environment memory world ->
  gateway_module_descriptor_regions (Clight.globalenv prog) source ->
  gateway_module_descriptor_regions (Clight.globalenv prog) memory.
Proof.
  intros CONTEXT REGIONS; eapply gateway_module_regions_retained; [exact REGIONS |].
  intros identifier variable object DESCRIPTOR VIEW.
  eapply Mem.unchanged_on_implies; [exact (gateway_validation_region_frame _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT) |].
  intros candidate position SAME LIVE; subst candidate.
  destruct VIEW as [DEFINITION [NONVOLATILE [SYMBOL REGION]]].
  exists identifier, variable; split; [exact DEFINITION |split; [exact NONVOLATILE |split; [|auto]]].
  exact (proj1 (gateway_loaded_region_bound _ _ _ _ REGION)).
Qed.

Lemma gateway_validation_relocated_pointer (ge : Clight.genv) memory table names origin index identifier :
  Genv.load_store_init_data (Clight.genv_genv ge) memory table origin (map (fun name => Init_addrof name Ptrofs.zero) names) ->
  nth_error names index = Some identifier ->
  exists object, Genv.find_symbol ge identifier = Some object /\
    Mem.load Mptr memory table (origin + 8 * Z.of_nat index) = Some (Vptr object Ptrofs.zero).
Proof.
  revert origin index; induction names as [|first rest IH]; intros origin index INITIAL SELECTED.
  - destruct index; discriminate.
  - cbn [map Genv.load_store_init_data] in INITIAL; destruct INITIAL as [[object [SYMBOL LOAD]] TAIL].
    destruct index as [|index].
    + cbn in SELECTED; inversion SELECTED; subst identifier; exists object; split; [exact SYMBOL |].
      replace (origin + 8 * Z.of_nat 0) with origin by lia; exact LOAD.
    + cbn in SELECTED; destruct (IH (origin + size_chunk Mptr) index TAIL SELECTED) as [selected [NEXT_SYMBOL NEXT_LOAD]].
      exists selected; split; [exact NEXT_SYMBOL |].
      replace (origin + 8 * Z.of_nat (S index)) with (origin + size_chunk Mptr + 8 * Z.of_nat index)
        by (change (size_chunk Mptr) with 8; rewrite Nat2Z.inj_succ; lia); exact NEXT_LOAD.
Qed.

Lemma gateway_validation_source_name index characters :
  nth_error gateway_outcome_names index = Some characters ->
  exists identifier named,
    nth_error gateway_outcome_name_symbols index = Some identifier /\ In named gateway_outcome_property_sources /\
    gateway_getset_name_symbol named = identifier /\ gateway_getset_source_name named = map Byte.repr characters /\
    Forall (fun character => 0 <= character < 128) characters.
Proof.
  intro SELECTED.
  exists (nth index gateway_outcome_name_symbols ___stringlit_50),
    (nth index gateway_outcome_property_sources
      {| gateway_getset_name_symbol := ___stringlit_50; gateway_getset_source_name := [];
         gateway_getset_getter_symbol := _host_outcome_get; gateway_getset_setter_symbol := Some _host_outcome_set;
         gateway_getset_source_closure := 0 |}).
  do 14 (destruct index as [|index];
    [cbn in SELECTED; inversion SELECTED; subst characters;
      split; [reflexivity |split; [cbn; tauto |split; [reflexivity |split; [reflexivity |repeat constructor; lia]]]] |]).
  destruct index; discriminate.
Qed.

Lemma gateway_validation_ascii_text characters :
  Forall (fun character => 0 <= character < 128) characters -> gateway_utf8_text (map Byte.repr characters) characters.
Proof.
  intro ASCII; induction ASCII; [constructor |].
  change (gateway_utf8_text ([Byte.repr x] ++ map Byte.repr l) (x :: l)).
  eapply gateway_utf8_next; [|exact IHASCII].
  replace x with (Byte.unsigned (Byte.repr x)) at 2 by (rewrite Byte.unsigned_repr; [reflexivity |change Byte.max_unsigned with 255; lia]).
  apply gateway_utf8_ascii; rewrite Byte.unsigned_repr; [lia |change Byte.max_unsigned with 255; lia].
Qed.

Lemma gateway_validation_error_object_name memory object bytes characters :
  gateway_error_cstring memory (Vptr object Ptrofs.zero) bytes ->
  gateway_utf8_text bytes characters -> gateway_object_name memory (Vptr object Ptrofs.zero) characters.
Proof.
  intros [actual [offset [SAME [NONZERO [BOUND LOAD]]]]] UTF8; inversion SAME; subst actual offset.
  change (Ptrofs.unsigned Ptrofs.zero) with 0 in LOAD, BOUND.
  exists bytes; split; [|auto].
  exists object, Ptrofs.zero; split; [reflexivity |split].
  - eapply Mem.perm_valid_block with (ofs := 0) (k := Cur) (p := Readable).
    apply (Mem.loadbytes_range_perm _ _ _ _ _ LOAD 0); lia.
  - split.
    + rewrite length_app, Nat2Z.inj_add.
      change (Ptrofs.unsigned Ptrofs.zero) with 0; change (Z.of_nat (length [Byte.zero])) with 1; lia.
    + rewrite length_app, Nat2Z.inj_add.
      change (Ptrofs.unsigned Ptrofs.zero) with 0; change (Z.of_nat (length [Byte.zero])) with 1; exact LOAD.
Qed.

Lemma gateway_validation_name_offset_unsigned index :
  (index < 14)%nat -> Ptrofs.unsigned (gateway_validation_name_offset index) = 8 * Z.of_nat index.
Proof. intro BOUND; do 14 (destruct index as [|index]; [reflexivity |]); lia. Qed.

Theorem gateway_validation_actual_name memory index characters table :
  gateway_module_descriptor_regions (Clight.globalenv prog) memory ->
  Genv.find_symbol (Clight.globalenv prog) _host_outcome_fields = Some table ->
  nth_error gateway_outcome_names index = Some characters ->
  exists name,
    (exists identifier, nth_error gateway_outcome_name_symbols index = Some identifier /\
      Genv.find_symbol (Clight.globalenv prog) identifier = Some name) /\
    Mem.loadv Mptr memory (Vptr table (gateway_validation_name_offset index)) = Some (Vptr name Ptrofs.zero) /\
    gateway_object_name memory (Vptr name Ptrofs.zero) characters.
Proof.
  intros REGIONS TABLE SELECTED.
  destruct (gateway_validation_source_name index characters SELECTED)
    as [identifier [named [NAME [MEMBER [IDENTIFIER [BYTES ASCII]]]]]].
  assert (DEFINITION : gateway_program_definition _host_outcome_fields global_definitions = Some (Gvar v_host_outcome_fields)) by reflexivity.
  destruct (REGIONS _host_outcome_fields v_host_outcome_fields DEFINITION eq_refl ltac:(change (0 < 112); lia)
    ltac:(right; cbn; tauto)) as [actual VIEW].
  assert (SAME : actual = table) by (destruct VIEW as [_ [_ [SYMBOL REGION]]]; congruence); subst actual.
  pose proof (gateway_loaded_region_values _ _ _ _ (proj2 (proj2 (proj2 VIEW)))) as INITIAL.
  rewrite actual_outcome_fields_are_source_data in INITIAL.
  destruct (gateway_validation_relocated_pointer _ _ _ _ 0 index identifier INITIAL NAME) as [name [SYMBOL LOAD]].
  exists name; split; [exists identifier; auto |split].
  - unfold Mem.loadv.
    assert (BOUND : (index < 14)%nat).
    { change (index < length gateway_outcome_names)%nat.
      apply (proj1 (nth_error_Some gateway_outcome_names index)); rewrite SELECTED; discriminate. }
    rewrite gateway_validation_name_offset_unsigned by exact BOUND.
    replace (8 * Z.of_nat index) with (0 + 8 * Z.of_nat index) by lia.
    destruct zle; [exact LOAD |change (size_chunk Mptr) with 8 in *; change Ptrofs.modulus with 18446744073709551616 in *; lia].
  - apply gateway_validation_error_object_name with (bytes := map Byte.repr characters); [|apply gateway_validation_ascii_text; exact ASCII].
    rewrite <- BYTES; eapply gateway_module_regions_outcome_names; [exact REGIONS |exact MEMBER |rewrite IDENTIFIER; exact SYMBOL].
Qed.

Theorem gateway_validation_name_context {World} python objects decimal_float ledger held reserved captured original source environment
    table index characters :
  gateway_module_descriptor_regions (Clight.globalenv prog) source ->
  Genv.find_symbol (Clight.globalenv prog) _host_outcome_fields = Some table ->
  nth_error gateway_outcome_names index = Some characters ->
  exists name, forall memory world,
    @gateway_outcome_validation_context World python objects decimal_float ledger held reserved captured original
      (gateway_validation_source_region (Clight.globalenv prog)) source environment memory world ->
    Mem.loadv Mptr memory (Vptr table (gateway_validation_name_offset index)) = Some (Vptr name Ptrofs.zero) /\
      gateway_object_name memory (Vptr name Ptrofs.zero) characters.
Proof.
  intros REGIONS TABLE SELECTED.
  destruct (gateway_validation_actual_name source index characters table REGIONS TABLE SELECTED)
    as [name [[identifier [NAME SYMBOL]] [LOAD TEXT]]].
  exists name; intros memory world CONTEXT.
  destruct (gateway_validation_actual_name memory index characters table
    (gateway_validation_current_regions _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT REGIONS) TABLE SELECTED)
    as [actual [[current_identifier [CURRENT_NAME CURRENT_SYMBOL]] [CURRENT_LOAD CURRENT_TEXT]]].
  assert (SAME_IDENTIFIER : current_identifier = identifier) by congruence; subst current_identifier.
  assert (SAME_OBJECT : actual = name) by congruence; subst actual; auto.
Qed.

Theorem gateway_validation_json_name memory name :
  gateway_module_descriptor_regions (Clight.globalenv prog) memory ->
  Genv.find_symbol (Clight.globalenv prog) ___stringlit_51 = Some name ->
  gateway_object_name memory (Vptr name Ptrofs.zero) [106; 115; 111; 110].
Proof.
  intros REGIONS NAME.
  assert (LITERAL : gateway_static_cstring ___stringlit_51 v___stringlit_51 (map Byte.repr [106; 115; 111; 110])).
  { eapply gateway_static_string_from_registration;
      [vm_compute; reflexivity |reflexivity |reflexivity |vm_compute; intuition discriminate |change (5 <= 18446744073709551616); lia]. }
  destruct (REGIONS ___stringlit_51 v___stringlit_51 eq_refl eq_refl ltac:(change (0 < 5); lia)
    ltac:(left; reflexivity)) as [actual VIEW].
  assert (SAME : actual = name) by (destruct VIEW as [_ [_ [SYMBOL REGION]]]; congruence); subst actual.
  eapply gateway_validation_error_object_name.
  - eapply gateway_loaded_region_cstring; eassumption.
  - apply gateway_validation_ascii_text; repeat constructor; lia.
Qed.
