(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Object construction follows the actual
   post-bootstrap initializer spine. *)
From Stdlib Require Import ZArith List String.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayInitializationBootstrap GatewayJsonNumberSource
  GatewaySourcePaths GatewaySourceBoundCalls GatewaySourceSegmentAutomation GatewayUnaryExpressions GatewayFramedRuntime
  GatewayValueReturns GatewayFailurePaths GatewaySourceCuts GatewayObjectAddresses GatewayModuleSource.
Import ListNotations.
Local Open Scope string_scope.

Definition initializer_import_group := json_number_first initializer_after_bootstrap.
Definition initializer_import_assign := json_number_rest initializer_import_group.
Definition initializer_after_import := json_number_rest initializer_after_bootstrap.
Definition initializer_import_guard := json_number_first initializer_after_import.
Definition initializer_after_import_guard := json_number_rest initializer_after_import.
Definition initializer_attribute_group := json_number_first initializer_after_import_guard.
Definition initializer_path_store := json_number_rest initializer_attribute_group.
Definition initializer_after_attribute := json_number_rest initializer_after_import_guard.
Definition initializer_pathlib_release := json_number_first initializer_after_attribute.
Definition initializer_after_pathlib := json_number_rest initializer_after_attribute.
Definition initializer_path_guard := json_number_first initializer_after_pathlib.
Definition initializer_after_path_guard := json_number_rest initializer_after_pathlib.
Definition initializer_module_group := json_number_first initializer_after_path_guard.
Definition initializer_module_assign := json_number_rest initializer_module_group.
Definition initializer_after_module := json_number_rest initializer_after_path_guard.
Definition initializer_module_guard := json_number_first initializer_after_module.
Definition initializer_after_module_guard := json_number_rest initializer_after_module.
Definition initializer_workspace_group := json_number_first initializer_after_module_guard.
Definition initializer_workspace_assign := json_number_rest initializer_workspace_group.
Definition initializer_after_workspace := json_number_rest initializer_after_module_guard.
Definition initializer_workspace_guard := json_number_first initializer_after_workspace.
Definition initializer_after_workspace_guard := json_number_rest initializer_after_workspace.
Definition initializer_workspace_publication := json_number_first initializer_after_workspace_guard.
Definition initializer_after_workspace_publication := json_number_rest initializer_after_workspace_guard.
Definition initializer_cancel_group := json_number_first initializer_after_workspace_publication.
Definition initializer_cancel_store := json_number_rest initializer_cancel_group.
Definition initializer_after_cancel := json_number_rest initializer_after_workspace_publication.
Definition initializer_cancel_guard := json_number_first initializer_after_cancel.
Definition initializer_after_cancel_guard := json_number_rest initializer_after_cancel.
Definition initializer_cancel_publication := json_number_first initializer_after_cancel_guard.
Definition initializer_after_cancel_publication := json_number_rest initializer_after_cancel_guard.

Definition initializer_import_cont parameters := Kcall (Some _t'4) f_host_initialize empty_env parameters
  (Kseq initializer_import_assign (Kseq initializer_after_import Kstop)).
Definition initializer_attribute_cont parameters := Kcall (Some _t'5) f_host_initialize empty_env parameters
  (Kseq initializer_path_store (Kseq initializer_after_attribute Kstop)).
Definition initializer_pathlib_cont parameters := Kcall None f_host_initialize empty_env parameters
  (Kseq initializer_after_pathlib Kstop).
Definition initializer_module_cont parameters := Kcall (Some _t'6) f_host_initialize empty_env parameters
  (Kseq initializer_module_assign (Kseq initializer_after_module Kstop)).
Definition initializer_workspace_cont parameters := Kcall (Some _t'7) f_host_initialize empty_env parameters
  (Kseq initializer_workspace_assign (Kseq initializer_after_workspace Kstop)).
Definition initializer_workspace_add_cont parameters := Kcall (Some _t'8) f_host_initialize empty_env parameters
  (Kseq (json_number_rest initializer_workspace_publication) (Kseq initializer_after_workspace_publication Kstop)).
Definition initializer_cancel_cont parameters := Kcall (Some _t'9) f_host_initialize empty_env parameters
  (Kseq initializer_cancel_store (Kseq initializer_after_cancel Kstop)).
Definition initializer_cancel_add_cont parameters := Kcall (Some _t'10) f_host_initialize empty_env parameters
  (Kseq (json_number_rest initializer_cancel_publication) (Kseq initializer_after_cancel_publication Kstop)).

Definition initializer_import_definition : Ctypes.fundef Clight.function := External
  (EF_external "PyImport_ImportModule" (mksignature [Xptr] Xptr cc_default)) [tptr tschar] (tptr (Tstruct __object noattr)) cc_default.
Definition initializer_attribute_definition : Ctypes.fundef Clight.function := External
  (EF_external "PyObject_GetAttrString" (mksignature [Xptr; Xptr] Xptr cc_default))
  [tptr (Tstruct __object noattr); tptr tschar] (tptr (Tstruct __object noattr)) cc_default.
Definition initializer_module_definition : Ctypes.fundef Clight.function := External
  (EF_external "PyModule_Create2" (mksignature [Xptr; Xint] Xptr cc_default))
  [tptr (Tstruct _PyModuleDef noattr); tint] (tptr (Tstruct __object noattr)) cc_default.
Definition initializer_type_definition : Ctypes.fundef Clight.function := External
  (EF_external "PyType_FromSpec" (mksignature [Xptr] Xptr cc_default))
  [tptr (Tstruct __5268 noattr)] (tptr (Tstruct __object noattr)) cc_default.
Definition initializer_add_definition : Ctypes.fundef Clight.function := External
  (EF_external "PyModule_AddObject" (mksignature [Xptr; Xptr; Xptr] Xint cc_default))
  [tptr (Tstruct __object noattr); tptr tschar; tptr (Tstruct __object noattr)] tint cc_default.

Theorem actual_initializer_object_spine :
  initializer_path_store = Sassign (Evar _host_path_class (tptr (Tstruct __object noattr)))
    (Etempvar _t'5 (tptr (Tstruct __object noattr))) /\
  initializer_cancel_store = Sassign (Evar _host_cancellation_class (tptr (Tstruct __object noattr)))
    (Etempvar _t'9 (tptr (Tstruct __object noattr))) /\
  initializer_after_cancel_publication = module_outcome_creation.
Proof. repeat split; reflexivity. Qed.

Lemma initializer_literal_reference (ge : Clight.genv) parameters memory identifier count object :
  Genv.find_symbol ge identifier = Some object ->
  expression_value ge empty_env parameters memory (Evar identifier (tarray tschar count)) (Vptr object Ptrofs.zero).
Proof.
  intro SYMBOL; eapply location_read_value; [apply global_location_value; [reflexivity |exact SYMBOL] |].
  apply deref_loc_reference; reflexivity.
Qed.

Ltac initializer_object_call closed symbol symbol_fact function_fact :=
  lazymatch goal with
  | |- gateway_source_path _ _ ?definition ?arguments ?continuation _
      (State ?owner ?body ?saved ?environment ?parameters ?memory) _ =>
    eapply gateway_source_same with (target := Callstate definition arguments continuation memory);
      [exact closed |cbn; tauto |intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero);
        [reflexivity |apply old_expression_value; eapply value_function; [reflexivity |exact symbol_fact |reflexivity] |
         idtac |exact function_fact |reflexivity] |apply gateway_source_reached; auto]
  end.

Theorem gateway_initializer_import_source {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters memory symbol name :
  gateway_ambient_closed backend property ->
  Genv.find_symbol ge _PyImport_ImportModule = Some symbol -> Genv.find_funct_ptr ge symbol = Some initializer_import_definition ->
  Genv.find_symbol ge ___stringlit_127 = Some name ->
  exists called_parameters,
    gateway_source_path backend ge initializer_import_definition [Vptr name Ptrofs.zero]
      (initializer_import_cont called_parameters) property
      (Returnstate (Vint Int.zero) (initializer_bootstrap_cont parameters) memory) property /\
    (forall identifier, identifier <> _t'3 -> called_parameters ! identifier = parameters ! identifier).
Proof.
  intros CLOSED SYMBOL FUNCTION NAME; eexists; split.
  - gateway_bound_source_call CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
    initializer_object_call CLOSED symbol SYMBOL FUNCTION.
    apply cons_argument_values with (v := Vptr name Ptrofs.zero);
      [apply initializer_literal_reference; exact NAME |reflexivity |apply no_argument_values].
  - intros identifier OTHER; unfold set_opttemp; rewrite PTree.gso by congruence; reflexivity.
Qed.

Theorem gateway_initializer_attribute_source {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters library library_offset memory symbol name :
  gateway_ambient_closed backend property ->
  (forall memory world, property memory world -> Mem.weak_valid_pointer memory library (Ptrofs.unsigned library_offset) = true) ->
  Genv.find_symbol ge _PyObject_GetAttrString = Some symbol -> Genv.find_funct_ptr ge symbol = Some initializer_attribute_definition ->
  Genv.find_symbol ge ___stringlit_128 = Some name ->
  exists called_parameters,
    gateway_source_path backend ge initializer_attribute_definition [Vptr library library_offset; Vptr name Ptrofs.zero]
      (initializer_attribute_cont called_parameters) property
      (Returnstate (Vptr library library_offset) (initializer_import_cont parameters) memory) property /\
    called_parameters ! _pathlib = Some (Vptr library library_offset) /\
    (forall identifier, identifier <> _pathlib -> identifier <> _t'4 -> called_parameters ! identifier = parameters ! identifier).
Proof.
  intros CLOSED LIVE SYMBOL FUNCTION NAME; eexists; split.
  - gateway_bound_source_call CLOSED
      ltac:(fun _ => eapply gateway_unary_expression_value with (value := Vptr library library_offset) (result := Vint Int.zero);
        [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |
          match goal with GOOD : property ?current ?world |- _ =>
            change (option_map (fun flag => Val.of_bool (negb flag))
              (if Mem.weak_valid_pointer current library (Ptrofs.unsigned library_offset) then Some true else None) = Some (Vint Int.zero));
            rewrite (LIVE current world GOOD); reflexivity end]) ltac:(fun _ => reflexivity).
    initializer_object_call CLOSED symbol SYMBOL FUNCTION.
    apply cons_argument_values with (v := Vptr library library_offset);
      [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |reflexivity |].
    apply cons_argument_values with (v := Vptr name Ptrofs.zero);
      [apply initializer_literal_reference; exact NAME |reflexivity |apply no_argument_values].
  - split; [apply PTree.gss |]. intros identifier A B; unfold set_opttemp; repeat rewrite PTree.gso by congruence; reflexivity.
Qed.
