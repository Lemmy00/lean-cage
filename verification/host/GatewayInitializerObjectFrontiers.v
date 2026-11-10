(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Actual object return and global-store frontiers. *)
From Stdlib Require Import ZArith List String.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayInitializerObjectsSource
  GatewayInitializerGlobalStores GatewaySourcePaths GatewaySourceBoundCalls GatewaySourceSegments
  GatewaySourceSegmentAutomation GatewayUnaryExpressions GatewayFramedRuntime GatewayObjectAddresses
  GatewayReferenceSourceExecution GatewayModuleSource GatewayModulePublication.
Import ListNotations.
Local Open Scope string_scope.

Theorem gateway_initializer_path_store_frontier {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters value memory :
  gateway_ambient_closed backend property ->
  exists changed,
    gateway_source_segment backend ge property
      (Returnstate value (initializer_attribute_cont parameters) memory)
      (State f_host_initialize (initializer_pointer_assignment _host_path_class _t'5)
        (Kseq initializer_after_attribute Kstop) empty_env changed memory) property /\
    changed ! _t'5 = Some value /\
    (forall identifier, identifier <> _t'5 -> changed ! identifier = parameters ! identifier).
Proof.
  intro CLOSED; eexists; split.
  - gateway_segment_dynamic CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
  - split; [apply PTree.gss |]. intros identifier OTHER; apply PTree.gso; congruence.
Qed.

Theorem gateway_initializer_cancel_store_frontier {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters value memory :
  gateway_ambient_closed backend property ->
  exists changed,
    gateway_source_segment backend ge property
      (Returnstate value (initializer_cancel_cont parameters) memory)
      (State f_host_initialize (initializer_pointer_assignment _host_cancellation_class _t'9)
        (Kseq initializer_after_cancel Kstop) empty_env changed memory) property /\
    changed ! _t'9 = Some value /\
    (forall identifier, identifier <> _t'9 -> changed ! identifier = parameters ! identifier).
Proof.
  intro CLOSED; eexists; split.
  - gateway_segment_dynamic CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
  - split; [apply PTree.gss |]. intros identifier OTHER; apply PTree.gso; congruence.
Qed.

Theorem gateway_initializer_outcome_store_frontier {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters value memory :
  gateway_ambient_closed backend property ->
  exists changed,
    gateway_source_segment backend ge property
      (Returnstate value (module_outcome_cont parameters Kstop) memory)
      (State f_host_initialize (initializer_pointer_assignment _host_outcome_class _t'11)
        (Kseq module_outcome_rest Kstop) empty_env changed memory) property /\
    changed ! _t'11 = Some value /\
    (forall identifier, identifier <> _t'11 -> changed ! identifier = parameters ! identifier).
Proof.
  intro CLOSED; eexists; split.
  - gateway_segment_dynamic CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
  - split; [apply PTree.gss |]. intros identifier OTHER; apply PTree.gso; congruence.
Qed.

Theorem gateway_initializer_pathlib_release_source {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters library memory symbol :
  gateway_ambient_closed backend property -> parameters ! _pathlib = Some library ->
  (exists object offset, library = Vptr object offset) ->
  Genv.find_symbol ge _Py_DecRef = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some gateway_reference_decref_definition ->
  gateway_source_path backend ge gateway_reference_decref_definition [library]
    (initializer_pathlib_cont parameters) property
    (State f_host_initialize Sskip (Kseq initializer_after_attribute Kstop) empty_env parameters memory) property.
Proof.
  intros CLOSED LIBRARY (object & offset & POINTER) SYMBOL FUNCTION; subst library.
  gateway_bound_source_call CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
  initializer_object_call CLOSED symbol SYMBOL FUNCTION.
  apply cons_argument_values with (v := Vptr object offset);
    [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |
     reflexivity |apply no_argument_values].
Qed.

Lemma initializer_global_pointer_expression (ge : Clight.genv) parameters memory global symbol value :
  Genv.find_symbol ge global = Some symbol -> Mem.load Mptr memory symbol 0 = Some value ->
  expression_value ge empty_env parameters memory (Evar global (tptr (Tstruct __object noattr))) value.
Proof.
  intros SYMBOL LOAD; eapply location_read_value; [apply global_location_value; [reflexivity |exact SYMBOL] |].
  eapply deref_loc_value; [reflexivity |exact LOAD].
Qed.

Ltac initializer_live_negation live :=
  lazymatch type of live with
  | forall memory world, ?property memory world ->
      Mem.weak_valid_pointer memory ?object (Ptrofs.unsigned ?offset) = true =>
    eapply gateway_unary_expression_value with (value := Vptr object offset) (result := Vint Int.zero);
      [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |
       match goal with GOOD : property ?current ?world |- _ =>
         change (option_map (fun flag => Val.of_bool (negb flag))
           (if Mem.weak_valid_pointer current object (Ptrofs.unsigned offset) then Some true else None) = Some (Vint Int.zero));
         rewrite (live current world GOOD); reflexivity end]
  end.

Theorem gateway_initializer_module_source {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters path path_offset memory symbol descriptor path_cell :
  gateway_ambient_closed backend property ->
  (forall memory world, property memory world ->
    Mem.weak_valid_pointer memory path (Ptrofs.unsigned path_offset) = true) ->
  (forall memory world, property memory world -> Mem.load Mptr memory path_cell 0 = Some (Vptr path path_offset)) ->
  Genv.find_symbol ge _host_path_class = Some path_cell ->
  Genv.find_symbol ge _PyModule_Create2 = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some initializer_module_definition ->
  Genv.find_symbol ge _host_module = Some descriptor ->
  exists changed,
    gateway_source_path backend ge initializer_module_definition [Vptr descriptor Ptrofs.zero; Vint (Int.repr 3)]
      (initializer_module_cont changed) property
      (Returnstate Vundef (initializer_pathlib_cont parameters) memory) property /\
    (forall identifier, identifier <> _t'17 -> changed ! identifier = parameters ! identifier).
Proof.
  intros CLOSED LIVE LOAD PATH SYMBOL FUNCTION DESCRIPTOR; eexists; split.
  - gateway_bound_source_call CLOSED
      ltac:(fun _ => first [initializer_live_negation LIVE |
        match goal with GOOD : property ?current ?world |- _ =>
          apply initializer_global_pointer_expression with (symbol := path_cell); [exact PATH |exact (LOAD current world GOOD)] end])
      ltac:(fun _ => reflexivity).
    initializer_object_call CLOSED symbol SYMBOL FUNCTION.
    apply cons_argument_values with (v := Vptr descriptor Ptrofs.zero);
      [apply gateway_global_address_expression; [reflexivity |exact DESCRIPTOR] |reflexivity |].
    apply cons_argument_values with (v := Vint (Int.repr 3));
      [apply old_expression_value, value_int |reflexivity |apply no_argument_values].
  - intros identifier OTHER; unfold set_opttemp; rewrite PTree.gso by congruence; reflexivity.
Qed.

Theorem gateway_initializer_workspace_source {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters module module_offset memory symbol specification :
  gateway_ambient_closed backend property ->
  (forall memory world, property memory world -> Mem.weak_valid_pointer memory module (Ptrofs.unsigned module_offset) = true) ->
  Genv.find_symbol ge _PyType_FromSpec = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some initializer_type_definition ->
  Genv.find_symbol ge _host_workspace_spec = Some specification ->
  exists changed,
    gateway_source_path backend ge initializer_type_definition [Vptr specification Ptrofs.zero]
      (initializer_workspace_cont changed) property
      (Returnstate (Vptr module module_offset) (initializer_module_cont parameters) memory) property /\
    changed ! _module = Some (Vptr module module_offset) /\
    (forall identifier, identifier <> _module -> identifier <> _t'6 -> changed ! identifier = parameters ! identifier).
Proof.
  intros CLOSED LIVE SYMBOL FUNCTION SPECIFICATION; eexists; split.
  - gateway_bound_source_call CLOSED ltac:(fun _ => initializer_live_negation LIVE) ltac:(fun _ => reflexivity).
    initializer_object_call CLOSED symbol SYMBOL FUNCTION.
    apply cons_argument_values with (v := Vptr specification Ptrofs.zero);
      [apply gateway_global_address_expression; [reflexivity |exact SPECIFICATION] |reflexivity |apply no_argument_values].
  - split; [apply PTree.gss |]. intros identifier A B; unfold set_opttemp;
      repeat rewrite PTree.gso by congruence; reflexivity.
Qed.

Theorem gateway_initializer_workspace_publication_source {World Event}
    (backend : gateway_backend World Event) (ge : Clight.genv) (property : mem -> World -> Prop)
    parameters workspace workspace_offset module memory symbol name :
  gateway_ambient_closed backend property -> parameters ! _module = Some module ->
  (exists object offset, module = Vptr object offset) ->
  (forall memory world, property memory world ->
    Mem.weak_valid_pointer memory workspace (Ptrofs.unsigned workspace_offset) = true) ->
  Genv.find_symbol ge _PyModule_AddObject = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some initializer_add_definition ->
  Genv.find_symbol ge ___stringlit_129 = Some name ->
  exists changed,
    gateway_source_path backend ge initializer_add_definition
      [module; Vptr name Ptrofs.zero; Vptr workspace workspace_offset]
      (initializer_workspace_add_cont changed) property
      (Returnstate (Vptr workspace workspace_offset) (initializer_workspace_cont parameters) memory) property /\
    changed ! _workspace = Some (Vptr workspace workspace_offset) /\
    (forall identifier, identifier <> _workspace -> identifier <> _t'7 -> changed ! identifier = parameters ! identifier).
Proof.
  intros CLOSED MODULE (object & offset & POINTER) LIVE SYMBOL FUNCTION NAME; subst module; eexists; split.
  - gateway_bound_source_call CLOSED ltac:(fun _ => initializer_live_negation LIVE) ltac:(fun _ => reflexivity).
    initializer_object_call CLOSED symbol SYMBOL FUNCTION.
    apply cons_argument_values with (v := Vptr object offset);
      [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |reflexivity |].
    apply cons_argument_values with (v := Vptr name Ptrofs.zero);
      [apply initializer_literal_reference; exact NAME |reflexivity |].
    apply cons_argument_values with (v := Vptr workspace workspace_offset);
      [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |reflexivity |apply no_argument_values].
  - split; [apply PTree.gss |]. intros identifier A B; unfold set_opttemp;
      repeat rewrite PTree.gso by congruence; reflexivity.
Qed.

Theorem gateway_initializer_cancel_source {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters memory symbol specification :
  gateway_ambient_closed backend property ->
  Genv.find_symbol ge _PyType_FromSpec = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some initializer_type_definition ->
  Genv.find_symbol ge _host_cancellation_spec = Some specification ->
  exists changed,
    gateway_source_path backend ge initializer_type_definition [Vptr specification Ptrofs.zero]
      (initializer_cancel_cont changed) property
      (Returnstate (Vint Int.zero) (initializer_workspace_add_cont parameters) memory) property /\
    (forall identifier, identifier <> _t'8 -> changed ! identifier = parameters ! identifier).
Proof.
  intros CLOSED SYMBOL FUNCTION SPECIFICATION; eexists; split.
  - gateway_bound_source_call CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
    initializer_object_call CLOSED symbol SYMBOL FUNCTION.
    apply cons_argument_values with (v := Vptr specification Ptrofs.zero);
      [apply gateway_global_address_expression; [reflexivity |exact SPECIFICATION] |reflexivity |apply no_argument_values].
  - intros identifier OTHER; unfold set_opttemp; rewrite PTree.gso by congruence; reflexivity.
Qed.

Theorem gateway_initializer_cancel_publication_source {World Event}
    (backend : gateway_backend World Event) (ge : Clight.genv) (property : mem -> World -> Prop)
    parameters class class_offset module memory symbol name class_cell :
  gateway_ambient_closed backend property -> parameters ! _module = Some module ->
  (exists object offset, module = Vptr object offset) ->
  (forall memory world, property memory world ->
    Mem.weak_valid_pointer memory class (Ptrofs.unsigned class_offset) = true) ->
  (forall memory world, property memory world -> Mem.load Mptr memory class_cell 0 = Some (Vptr class class_offset)) ->
  Genv.find_symbol ge _host_cancellation_class = Some class_cell ->
  Genv.find_symbol ge _PyModule_AddObjectRef = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (External
    (EF_external "PyModule_AddObjectRef" (mksignature [Xptr; Xptr; Xptr] Xint cc_default))
    [tptr (Tstruct __object noattr); tptr tschar; tptr (Tstruct __object noattr)] tint cc_default) ->
  Genv.find_symbol ge ___stringlit_130 = Some name ->
  exists changed,
    gateway_source_path backend ge (External
      (EF_external "PyModule_AddObjectRef" (mksignature [Xptr; Xptr; Xptr] Xint cc_default))
      [tptr (Tstruct __object noattr); tptr tschar; tptr (Tstruct __object noattr)] tint cc_default)
      [module; Vptr name Ptrofs.zero; Vptr class class_offset]
      (initializer_cancel_add_cont changed) property
      (State f_host_initialize Sskip (Kseq initializer_after_cancel Kstop) empty_env parameters memory) property /\
    changed ! _t'15 = Some (Vptr class class_offset) /\
    (forall identifier, identifier <> _t'15 -> identifier <> _t'16 -> changed ! identifier = parameters ! identifier).
Proof.
  intros CLOSED MODULE (object & offset & POINTER) LIVE LOAD CLASS SYMBOL FUNCTION NAME; subst module; eexists; split.
  - gateway_bound_source_call CLOSED
      ltac:(fun _ => first [initializer_live_negation LIVE |
        match goal with GOOD : property ?current ?world |- _ =>
          apply initializer_global_pointer_expression with (symbol := class_cell); [exact CLASS |exact (LOAD current world GOOD)] end])
      ltac:(fun _ => reflexivity).
    initializer_object_call CLOSED symbol SYMBOL FUNCTION.
    apply cons_argument_values with (v := Vptr object offset);
      [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |reflexivity |].
    apply cons_argument_values with (v := Vptr name Ptrofs.zero);
      [apply initializer_literal_reference; exact NAME |reflexivity |].
    apply cons_argument_values with (v := Vptr class class_offset);
      [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |reflexivity |apply no_argument_values].
  - split; [apply PTree.gss |]. intros identifier A B; unfold set_opttemp;
      repeat rewrite PTree.gso by congruence; reflexivity.
Qed.

Theorem gateway_initializer_outcome_source {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters memory symbol specification :
  gateway_ambient_closed backend property ->
  Genv.find_symbol ge _PyType_FromSpec = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some initializer_type_definition ->
  Genv.find_symbol ge _host_outcome_spec = Some specification ->
  exists changed,
    gateway_source_path backend ge initializer_type_definition [Vptr specification Ptrofs.zero]
      (module_outcome_cont changed Kstop) property
      (Returnstate (Vint Int.zero) (initializer_cancel_add_cont parameters) memory) property /\
    (forall identifier, identifier <> _t'10 -> changed ! identifier = parameters ! identifier).
Proof.
  intros CLOSED SYMBOL FUNCTION SPECIFICATION; eexists; split.
  - gateway_bound_source_call CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
    initializer_object_call CLOSED symbol SYMBOL FUNCTION.
    apply cons_argument_values with (v := Vptr specification Ptrofs.zero);
      [apply gateway_global_address_expression; [reflexivity |exact SPECIFICATION] |reflexivity |apply no_argument_values].
  - intros identifier OTHER; unfold set_opttemp; rewrite PTree.gso by congruence; reflexivity.
Qed.

Theorem gateway_initializer_outcome_publication_source {World Event}
    (backend : gateway_backend World Event) (ge : Clight.genv) (property : mem -> World -> Prop)
    parameters class class_offset module memory symbol name class_cell :
  gateway_ambient_closed backend property -> parameters ! _module = Some module ->
  (exists object offset, module = Vptr object offset) ->
  (forall memory world, property memory world ->
    Mem.weak_valid_pointer memory class (Ptrofs.unsigned class_offset) = true) ->
  (forall memory world, property memory world -> Mem.load Mptr memory class_cell 0 = Some (Vptr class class_offset)) ->
  Genv.find_symbol ge _host_outcome_class = Some class_cell ->
  Genv.find_symbol ge _PyModule_AddObjectRef = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (External
    (EF_external "PyModule_AddObjectRef" (mksignature [Xptr; Xptr; Xptr] Xint cc_default))
    [tptr (Tstruct __object noattr); tptr tschar; tptr (Tstruct __object noattr)] tint cc_default) ->
  Genv.find_symbol ge ___stringlit_131 = Some name ->
  exists changed,
    gateway_source_path backend ge (External
      (EF_external "PyModule_AddObjectRef" (mksignature [Xptr; Xptr; Xptr] Xint cc_default))
      [tptr (Tstruct __object noattr); tptr tschar; tptr (Tstruct __object noattr)] tint cc_default)
      [module; Vptr name Ptrofs.zero; Vptr class class_offset]
      (module_outcome_add_cont changed Kstop) property
      (State f_host_initialize Sskip (Kseq module_outcome_rest Kstop) empty_env parameters memory) property /\
    changed ! _t'13 = Some (Vptr class class_offset) /\
    (forall identifier, identifier <> _t'13 -> identifier <> _t'14 -> changed ! identifier = parameters ! identifier).
Proof.
  intros CLOSED MODULE (object & offset & POINTER) LIVE LOAD CLASS SYMBOL FUNCTION NAME; subst module; eexists; split.
  - gateway_bound_source_call CLOSED
      ltac:(fun _ => first [initializer_live_negation LIVE |
        match goal with GOOD : property ?current ?world |- _ =>
          apply initializer_global_pointer_expression with (symbol := class_cell); [exact CLASS |exact (LOAD current world GOOD)] end])
      ltac:(fun _ => reflexivity).
    initializer_object_call CLOSED symbol SYMBOL FUNCTION.
    apply cons_argument_values with (v := Vptr object offset);
      [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |reflexivity |].
    apply cons_argument_values with (v := Vptr name Ptrofs.zero);
      [apply initializer_literal_reference; exact NAME |reflexivity |].
    apply cons_argument_values with (v := Vptr class class_offset);
      [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |reflexivity |apply no_argument_values].
  - split; [apply PTree.gss |]. intros identifier A B; unfold _t'13, _t'14 in A, B; unfold set_opttemp;
      repeat rewrite PTree.gso by congruence; reflexivity.
Qed.
