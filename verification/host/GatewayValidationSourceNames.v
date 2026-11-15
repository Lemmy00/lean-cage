(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Validation names come from the same loaded source descriptors, including SDK-linked images. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayRegistry GatewayGlobals
  GatewayLoaderRegions GatewayInitializerRetention GatewayModuleRegions GatewayNativeRegions GatewayErrorRuntime
  GatewayOutcome GatewayOutcomeGetsets GatewayGetsets GatewayOutcomeValidationContext GatewayOutcomeValidationPaths GatewayValidationNames.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_validation_linked_regions {World} python objects decimal_float ledger held reserved captured original ge source environment memory world :
  @gateway_outcome_validation_context World python objects decimal_float ledger held reserved captured original
    (gateway_validation_source_region ge) source environment memory world ->
  gateway_module_descriptor_regions ge source -> gateway_module_descriptor_regions ge memory.
Proof.
  intros CONTEXT REGIONS; eapply gateway_module_regions_retained; [exact REGIONS |].
  intros identifier variable object DESCRIPTOR VIEW.
  eapply Mem.unchanged_on_implies; [exact (gateway_validation_region_frame _ _ _ _ _ _ _ _ _ _ _ _ _ CONTEXT) |].
  intros candidate position SAME LIVE; subst candidate.
  destruct VIEW as [DEFINITION [NONVOLATILE [SYMBOL REGION]]].
  exists identifier, variable; split; [exact DEFINITION |split; [exact NONVOLATILE |split; [|auto]]].
  exact (proj1 (gateway_loaded_region_bound _ _ _ _ REGION)).
Qed.

Lemma gateway_validation_property_initializers source variable :
  In source gateway_outcome_property_sources ->
  gateway_program_definition (gateway_getset_name_symbol source) global_definitions = Some (Gvar variable) ->
  gvar_init variable = map (fun byte => Init_int8 (Int.repr (Byte.unsigned byte)))
    (gateway_getset_source_name source ++ [Byte.zero]).
Proof.
  cbn [gateway_outcome_property_sources gateway_outcome_name_symbols gateway_outcome_names
    gateway_observation_name combine seq map app In].
  intro MEMBER; repeat destruct MEMBER as [SAME |MEMBER]; try contradiction; subst source;
    intro DEFINITION; cbn [gateway_program_definition] in DEFINITION; inversion DEFINITION; subst variable; vm_compute; reflexivity.
Qed.

Lemma gateway_validation_loaded_cstring ge identifier variable object memory bytes :
  gateway_static_cstring identifier variable bytes ->
  gvar_init variable = map (fun byte => Init_int8 (Int.repr (Byte.unsigned byte))) (bytes ++ [Byte.zero]) ->
  gateway_native_initializer_view ge identifier variable object memory ->
  gateway_error_cstring memory (Vptr object Ptrofs.zero) bytes.
Proof.
  intros [_ [_ [NONZERO [BOUND [SIZE CONTENTS]]]]] INITIALIZERS [_ [_ [_ REGION]]].
  destruct REGION as [WIDTH READABLE LOAD VALUES].
  exists object, Ptrofs.zero; split; [reflexivity |split; [exact NONZERO |split]].
  - change (0 + Z.of_nat (length bytes) + 1 <= Ptrofs.modulus); exact BOUND.
  - change (Mem.loadbytes memory object 0 (Z.of_nat (length bytes) + 1) = Some (inj_bytes (bytes ++ [Byte.zero]))).
    rewrite SIZE, INITIALIZERS, gateway_byte_initial_contents in LOAD; exact LOAD.
Qed.

Theorem gateway_validation_source_name_literal (ge : Clight.genv) memory source name :
  gateway_module_descriptor_regions ge memory -> In source gateway_outcome_property_sources ->
  Genv.find_symbol ge (gateway_getset_name_symbol source) = Some name ->
  gateway_error_cstring memory (Vptr name Ptrofs.zero) (gateway_getset_source_name source).
Proof.
  intros REGIONS MEMBER SYMBOL.
  destruct (actual_outcome_property_literal source MEMBER) as [variable [DEFINITION [READONLY STATIC]]].
  assert (POSITIVE : 0 < init_data_list_size (gvar_init variable)).
  { destruct STATIC as [_ [_ [_ [_ [SIZE BYTES]]]]]; rewrite SIZE; lia. }
  assert (NONVOLATILE : gvar_volatile variable = false) by (exact (proj1 (proj2 STATIC))).
  destruct (REGIONS _ _ DEFINITION NONVOLATILE POSITIVE (or_introl READONLY)) as [object VIEW].
  assert (SAME : object = name) by (destruct VIEW as [_ [_ [ACTUAL REGION]]]; congruence); subst object.
  eapply gateway_validation_loaded_cstring; [exact STATIC | |exact VIEW].
  eapply gateway_validation_property_initializers; eassumption.
Qed.

Theorem gateway_validation_linked_name (ge : Clight.genv) memory index characters table :
  gateway_module_descriptor_regions ge memory -> Genv.find_symbol ge _host_outcome_fields = Some table ->
  nth_error gateway_outcome_names index = Some characters ->
  exists name identifier,
    nth_error gateway_outcome_name_symbols index = Some identifier /\ Genv.find_symbol ge identifier = Some name /\
    Mem.loadv Mptr memory (Vptr table (gateway_validation_name_offset index)) = Some (Vptr name Ptrofs.zero) /\
    gateway_object_name memory (Vptr name Ptrofs.zero) characters.
Proof.
  intros REGIONS TABLE SELECTED.
  destruct (gateway_validation_source_name index characters SELECTED)
    as [identifier [named [NAME [MEMBER [IDENTIFIER [BYTES ASCII]]]]]].
  destruct (REGIONS _host_outcome_fields v_host_outcome_fields eq_refl eq_refl ltac:(change (0 < 112); lia)
    ltac:(right; cbn; tauto)) as [actual VIEW].
  assert (SAME : actual = table) by (destruct VIEW as [_ [_ [SYMBOL REGION]]]; congruence); subst actual.
  pose proof (gateway_loaded_region_values _ _ _ _ (proj2 (proj2 (proj2 VIEW)))) as INITIAL.
  rewrite actual_outcome_fields_are_source_data in INITIAL.
  destruct (gateway_validation_relocated_pointer ge memory table gateway_outcome_name_symbols 0 index identifier INITIAL NAME)
    as [name [SYMBOL LOAD]].
  exists name, identifier; split; [exact NAME |split; [exact SYMBOL |split]].
  - unfold Mem.loadv.
    assert (BOUND : (index < 14)%nat).
    { change (index < length gateway_outcome_names)%nat.
      apply (proj1 (nth_error_Some gateway_outcome_names index)); rewrite SELECTED; discriminate. }
    rewrite gateway_validation_name_offset_unsigned by exact BOUND.
    replace (8 * Z.of_nat index) with (0 + 8 * Z.of_nat index) by lia.
    destruct zle; [exact LOAD |change (size_chunk Mptr) with 8 in *; change Ptrofs.modulus with 18446744073709551616 in *; lia].
  - apply gateway_validation_error_object_name with (bytes := map Byte.repr characters); [|apply gateway_validation_ascii_text; exact ASCII].
    rewrite <- BYTES; eapply gateway_validation_source_name_literal; [exact REGIONS |exact MEMBER |rewrite IDENTIFIER; exact SYMBOL].
Qed.

Theorem gateway_validation_linked_names_context {World} python objects decimal_float ledger held reserved captured original ge source environment table :
  gateway_module_descriptor_regions ge source -> Genv.find_symbol ge _host_outcome_fields = Some table ->
  forall index, (index < 14)%nat -> exists characters name,
    nth_error gateway_outcome_names index = Some characters /\ forall memory world,
    @gateway_outcome_validation_context World python objects decimal_float ledger held reserved captured original
      (gateway_validation_source_region ge) source environment memory world ->
    Mem.loadv Mptr memory (Vptr table (gateway_validation_name_offset index)) = Some (Vptr name Ptrofs.zero) /\
      gateway_object_name memory (Vptr name Ptrofs.zero) characters.
Proof.
  intros REGIONS TABLE index BOUND.
  assert (EXISTS : exists characters, nth_error gateway_outcome_names index = Some characters).
  { destruct (nth_error gateway_outcome_names index) eqn:NAME; [eauto |].
    apply nth_error_None in NAME; change (14 <= index)%nat in NAME; lia. }
  destruct EXISTS as [characters CHARACTERS].
  destruct (gateway_validation_linked_name ge source index characters table REGIONS TABLE CHARACTERS)
    as (name &identifier &NAME &SYMBOL &LOAD &TEXT).
  exists characters, name; split; [exact CHARACTERS |intros memory world CONTEXT].
  destruct (gateway_validation_linked_name ge memory index characters table
    (gateway_validation_linked_regions python objects decimal_float ledger held reserved captured original ge source environment memory world CONTEXT REGIONS) TABLE CHARACTERS)
    as (actual &current_identifier &CURRENT_NAME &CURRENT_SYMBOL &CURRENT_LOAD &CURRENT_TEXT).
  assert (SAME_IDENTIFIER : current_identifier = identifier) by congruence; subst current_identifier.
  assert (SAME_NAME : actual = name) by congruence; subst actual; auto.
Qed.

Theorem gateway_validation_linked_json_name (ge : Clight.genv) memory name :
  gateway_module_descriptor_regions ge memory -> Genv.find_symbol ge ___stringlit_51 = Some name ->
  gateway_object_name memory (Vptr name Ptrofs.zero) [106; 115; 111; 110].
Proof.
  intros REGIONS NAME.
  assert (LITERAL : gateway_static_cstring ___stringlit_51 v___stringlit_51 (map Byte.repr [106; 115; 111; 110])).
  { eapply gateway_static_string_from_registration;
      [vm_compute; reflexivity |reflexivity |reflexivity |vm_compute; intuition discriminate |change (5 <= 18446744073709551616); lia]. }
  destruct (REGIONS ___stringlit_51 v___stringlit_51 eq_refl eq_refl ltac:(change (0 < 5); lia)
    ltac:(left; reflexivity)) as [actual VIEW].
  assert (SAME : actual = name) by (destruct VIEW as [_ [_ [SYMBOL REGION]]]; congruence); subst actual.
  eapply gateway_validation_error_object_name; [eapply gateway_validation_loaded_cstring; [exact LITERAL |vm_compute; reflexivity |exact VIEW] |].
  apply gateway_validation_ascii_text; repeat constructor; lia.
Qed.

Theorem gateway_validation_linked_files_name (ge : Clight.genv) memory name :
  gateway_module_descriptor_regions ge memory -> Genv.find_symbol ge ___stringlit_41 = Some name ->
  gateway_object_name memory (Vptr name Ptrofs.zero) [102; 105; 108; 101; 115].
Proof.
  intros REGIONS NAME.
  assert (LITERAL : gateway_static_cstring ___stringlit_41 v___stringlit_41 (map Byte.repr [102; 105; 108; 101; 115])).
  { eapply gateway_static_string_from_registration;
      [vm_compute; reflexivity |reflexivity |reflexivity |vm_compute; intuition discriminate |change (6 <= 18446744073709551616); lia]. }
  destruct (REGIONS ___stringlit_41 v___stringlit_41 eq_refl eq_refl ltac:(change (0 < 6); lia)
    ltac:(left; reflexivity)) as [actual VIEW].
  assert (SAME : actual = name) by (destruct VIEW as [_ [_ [SYMBOL REGION]]]; congruence); subst actual.
  eapply gateway_validation_error_object_name; [eapply gateway_validation_loaded_cstring; [exact LITERAL |vm_compute; reflexivity |exact VIEW] |].
  apply gateway_validation_ascii_text; repeat constructor; lia.
Qed.
