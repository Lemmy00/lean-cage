(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual post-field path validates its original metadata before the files lookup. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue
  GatewayObjectThreads GatewayObjectDiscipline GatewayOutcomeValidationContext GatewayValidationGraphFacts GatewayValidationFieldLayouts
  GatewayValidationCheckCut GatewayValidationLookupCut GatewayValidationFailureJoin GatewayObjectInstances GatewayOutcomeMetadata
  GatewayOutcomeValidationSource GatewayOutcomeValidationPaths GatewayOutcomeValidationMetadata GatewaySourcePaths GatewayContexts
  GatewayThreadRuntime GatewayStreamInterface GatewayLocalRuntime GatewayReferenceThreads GatewayFramedRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Section ValidationMetadataCheck.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (python : World -> python_world) (objects : World -> gateway_object_heap)
    (decimal_float : list Z -> Floats.float -> Prop) (detached : val -> mem -> World -> Prop)
    (io : Event -> option gateway_native_io) (stable : World -> block -> Z -> Prop)
    (thread_errno : World -> int) (heap_allocation : block -> Z -> Prop) (leases : World -> nat -> val -> Prop)
    (threads : gateway_thread_runtime backend io (fun current object => gateway_native_private (python current) object) stable
      (gateway_python_discipline python objects detached) thread_errno)
    (references : gateway_reference_thread_contract backend (fun current object => gateway_native_private (python current) object) stable
      (gateway_python_discipline python objects detached) heap_allocation python objects)
    (instances : gateway_instance_runtime backend ge python objects leases)
    (containers : gateway_container_runtime backend python objects).
Context (ledger : GatewayReferenceLedger.gateway_reference_ledger) (held : list gateway_held_value) (reserved : list val)
    (captured : gateway_object_heap) (data : block) (data_offset : ptrofs) (protected : block -> Z -> Prop) (source : mem) (environment : env).
Let original := Vptr data data_offset.
Let base := gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment.
Context (type_symbol dictionary none instance_symbol lookup_symbol json_name files_name : block)
    (instance_definition lookup_definition : fundef)
    (LOCAL : forall identifier, In identifier [_host_has_type; _PyDict_Type; _PyDict_GetItemString; ___stringlit_51; ___stringlit_41] ->
      environment ! identifier = None)
    (TYPE_SYMBOL : Genv.find_symbol ge _host_has_type = Some type_symbol)
    (TYPE_FUNCTION : Genv.find_funct_ptr ge type_symbol = Some (Internal f_host_has_type))
    (DICTIONARY : Genv.find_symbol ge _PyDict_Type = Some dictionary) (NONE : Genv.find_symbol ge __Py_NoneStruct = Some none)
    (INSTANCE_SYMBOL : Genv.find_symbol ge _PyObject_IsInstance = Some instance_symbol)
    (INSTANCE_FUNCTION : Genv.find_funct_ptr ge instance_symbol = Some instance_definition)
    (INSTANCE_DEFINITION : gateway_object_api_definition gateway_api_is_instance = Some instance_definition)
    (INSTANCE_TYPE : type_of_fundef instance_definition = Tfunction [tptr (Tstruct __object noattr); tptr (Tstruct __object noattr)] tint cc_default)
    (LOOKUP_SYMBOL : Genv.find_symbol ge _PyDict_GetItemString = Some lookup_symbol)
    (LOOKUP_FUNCTION : Genv.find_funct_ptr ge lookup_symbol = Some lookup_definition)
    (LOOKUP_DEFINITION : gateway_object_api_definition gateway_api_dict_get_string = Some lookup_definition)
    (LOOKUP_TYPE : type_of_fundef lookup_definition = Tfunction [tptr (Tstruct __object noattr); tptr tschar] (tptr (Tstruct __object noattr)) cc_default)
    (JSON_NAME : Genv.find_symbol ge ___stringlit_51 = Some json_name)
    (FILES_NAME : Genv.find_symbol ge ___stringlit_41 = Some files_name)
    (JSON_TEXT : forall memory current, base memory current -> gateway_object_name memory (Vptr json_name Ptrofs.zero) gateway_outcome_json_name).

Theorem gateway_actual_validation_metadata fields parameters before world events returned after next :
  gateway_object_values captured original = Some (gateway_dict_object fields) ->
  parameters ! _valid = Some (Vint Int.one) -> parameters ! _index = Some (Vint (Int.repr 14)) ->
  parameters ! _data = Some original -> base before world -> returned <> Vnullptr ->
  gateway_steps backend ge
    (gateway_live (State f_host_outcome_from gateway_outcome_validation_loop_body gateway_validation_iteration_cont environment parameters before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix selected memory current metadata_field metadata_fields,
    events = prefix ++ suffix /\ selected ! _data = parameters ! _data /\
    gateway_dictionary_lookup gateway_outcome_json_name fields = Some metadata_field /\
    gateway_object_values captured (gateway_dictionary_value metadata_field) = Some (gateway_dict_object metadata_fields) /\
    gateway_steps backend ge
      (gateway_live (State f_host_outcome_from gateway_outcome_validation_loop_body gateway_validation_iteration_cont environment parameters before) world) prefix
      (gateway_live (Callstate lookup_definition [original; Vptr files_name Ptrofs.zero]
        (GatewayOutcomeLookupSource.gateway_outcome_files_lookup_cont environment selected) memory) current) /\
    base memory current /\
    gateway_steps backend ge
      (gateway_live (Callstate lookup_definition [original; Vptr files_name Ptrofs.zero]
        (GatewayOutcomeLookupSource.gateway_outcome_files_lookup_cont environment selected) memory) current) suffix
      (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intros FIELDS VALID INDEX DATA BASE NONNULL RUN.
  assert (CLOSED : gateway_ambient_closed backend base).
  { exact (gateway_validation_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
      threads references ledger held reserved captured original protected source environment). }
  destruct (gateway_validation_exhausted_json backend ge base environment parameters before Int.one data data_offset json_name lookup_symbol lookup_definition
    CLOSED VALID ltac:(change (0 < 1); lia) INDEX DATA (LOCAL _PyDict_GetItemString ltac:(cbn; tauto))
    (LOCAL ___stringlit_51 ltac:(cbn; tauto)) LOOKUP_SYMBOL LOOKUP_FUNCTION JSON_NAME LOOKUP_TYPE)
    as (json_parameters &JSON_PATH &JSON_DATA &JSON_VALID).
  destruct (gateway_source_path_cut backend ge _ _ _ base _ base JSON_PATH before world events returned after next BASE RUN)
    as (json_prefix &json_rest &json_memory &json_world &JSON_EVENTS &JSON_QUIET &TO_JSON &JSON_BASE &JSON_REST).
  destruct (gateway_actual_validation_lookup backend ge python objects decimal_float detached io stable thread_errno heap_allocation
    threads references containers ledger held reserved captured original protected source environment lookup_definition
    (Vptr json_name Ptrofs.zero) gateway_outcome_json_name fields (gateway_validation_json_lookup_cont environment json_parameters)
    json_memory json_world json_rest returned after next LOOKUP_DEFINITION I
    ltac:(cbn [gateway_validation_json_lookup_cont gateway_cont_weight]; lia) FIELDS JSON_TEXT
    ltac:(intros memory first current es result last following TRUE EXEC; cbn in EXEC;
      eapply gateway_validation_missing_json_returns_null;
        [exact (LOCAL _host_has_type ltac:(cbn; tauto)) |exact (LOCAL _PyDict_Type ltac:(cbn; tauto)) |
         exact TYPE_SYMBOL |exact TYPE_FUNCTION |exact DICTIONARY |exact EXEC])
    JSON_BASE NONNULL JSON_REST)
    as (json_operation &type_events &field_memory &field_world &field &JSON_REST_EVENTS &LOOKUP &REACHED &JSON_OPERATION &FIELD_BASE &FROM_JSON).
  destruct (gateway_validation_captured_builtin _ _ _ _ _ _ _ _ _ _ _ _ _ _ FIELD_BASE REACHED)
    as (description &kind &object &offset &DESCRIPTION &KIND &POINTER).
  rewrite POINTER in REACHED, DESCRIPTION, FROM_JSON, JSON_OPERATION.
  pose proof (gateway_validation_json_type backend ge base environment json_parameters field_memory (Vptr object offset) dictionary type_symbol
    CLOSED ltac:(right; eauto) (LOCAL _host_has_type ltac:(cbn; tauto)) (LOCAL _PyDict_Type ltac:(cbn; tauto))
    TYPE_SYMBOL TYPE_FUNCTION DICTIONARY) as TYPE_PATH.
  destruct (gateway_source_path_cut backend ge _ _ _ base _ base TYPE_PATH field_memory field_world type_events returned after next FIELD_BASE FROM_JSON)
    as (type_prefix &type_rest &type_memory &type_world &TYPE_EVENTS &TYPE_QUIET &TO_TYPE &TYPE_BASE &TYPE_REST).
  set (type_parameters := set_opttemp (Some _t'11) (Vptr object offset) json_parameters).
  destruct (gateway_actual_positive_validation_call backend ge python objects decimal_float detached io stable thread_errno heap_allocation leases
    threads references instances ledger held reserved captured original protected source environment (fun _ _ => True)
    ltac:(auto) ltac:(auto) object offset description kind gateway_dict_kind dictionary Ptrofs.zero none Int.zero
    (gateway_outcome_json_type_cont environment type_parameters) type_memory type_world type_rest returned after next instance_symbol instance_definition
    I ltac:(cbn [gateway_outcome_json_type_cont gateway_cont_weight]; lia) TYPE_BASE I REACHED DESCRIPTION KIND
    (gateway_builtin_dictionary_type ge dictionary DICTIONARY) (or_introl eq_refl) NONE
    INSTANCE_SYMBOL INSTANCE_FUNCTION INSTANCE_DEFINITION INSTANCE_TYPE
    ltac:(intros; apply gateway_outcome_json_nonpositive_null; assumption) NONNULL TYPE_REST)
    as (type_operation &files_events &after_type &after_type_world &TYPE_REST_EVENTS &TYPE_OPERATION &AFTER_TYPE &EXTRA &ACCEPT &FROM_TYPE).
  assert (ACCEPTED : gateway_builtin_accepts gateway_dict_kind kind = true).
  { destruct ACCEPT as [[IMPOSSIBLE SAME] |GOOD]; [discriminate IMPOSSIBLE |exact GOOD]. }
  destruct (gateway_validation_dictionary_layout description kind KIND ACCEPTED) as [metadata_fields SAME]; subst description.
  destruct (gateway_validation_files_getter backend ge base environment type_parameters after_type Int.one data data_offset files_name lookup_symbol lookup_definition
    CLOSED ltac:(change (0 < 1); lia) ltac:(unfold type_parameters, set_opttemp; rewrite PTree.gso by discriminate; rewrite JSON_DATA; exact DATA)
    (LOCAL _PyDict_GetItemString ltac:(cbn; tauto)) (LOCAL ___stringlit_41 ltac:(cbn; tauto))
    LOOKUP_SYMBOL LOOKUP_FUNCTION FILES_NAME LOOKUP_TYPE) as (selected &FILES_PATH &FILES_DATA &FILES_VALID).
  destruct (gateway_source_path_cut backend ge _ _ _ base _ base FILES_PATH after_type after_type_world files_events returned after next AFTER_TYPE FROM_TYPE)
    as (files_prefix &suffix &memory &current &FILES_EVENTS &FILES_QUIET &TO_FILES &GOOD &REST).
  exists (json_prefix ++ json_operation ++ type_prefix ++ type_operation ++ files_prefix), suffix, selected, memory, current, field, metadata_fields.
  split; [rewrite JSON_EVENTS, JSON_REST_EVENTS, TYPE_EVENTS, TYPE_REST_EVENTS, FILES_EVENTS; repeat rewrite app_assoc; reflexivity |].
  split.
  - rewrite FILES_DATA; unfold type_parameters, set_opttemp; rewrite PTree.gso by discriminate; exact JSON_DATA.
  - split; [exact LOOKUP |split; [rewrite POINTER; exact DESCRIPTION |split]].
    + eapply gateway_steps_append; [exact TO_JSON |].
      eapply gateway_steps_append; [exact (gateway_plug_steps backend ge _ _ _ (gateway_validation_json_lookup_cont environment json_parameters) I JSON_OPERATION) |].
      eapply gateway_steps_append; [exact TO_TYPE |].
      eapply gateway_steps_append; [exact (gateway_plug_steps backend ge _ _ _ (gateway_outcome_json_type_cont environment type_parameters) I TYPE_OPERATION) |exact TO_FILES].
    + exact (conj GOOD REST).
Qed.
End ValidationMetadataCheck.
