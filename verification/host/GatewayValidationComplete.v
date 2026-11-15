(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Original constructor execution produces all validation facts at its own private-copy call. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue
  GatewayObjectThreads GatewayObjectDiscipline GatewayOutcomeValidationContext GatewayValidationEntry GatewayOutcomeEntry
  GatewayValidationFirstCheck GatewayValidationFields GatewayValidationFieldLoop GatewayValidationMetadataCheck GatewayValidationFilesCopy
  GatewayValidationNames GatewayValidationSourceNames GatewayModuleRegions GatewayDictionaryIteration GatewayObjectInstances
  GatewayValidationReceivedContext GatewayReferenceLedger GatewayReferenceGraphCapture GatewayNativeRegions
  GatewayOutcomeMetadata GatewayOutcomeCopySource GatewayThreadRuntime GatewayStreamInterface GatewayLocalRuntime GatewayReferenceThreads.
Import ListNotations.
Local Close Scope lean_scope.

Section CompleteValidation.
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
    (containers : gateway_container_runtime backend python objects)
    (iteration : gateway_dictionary_iteration_runtime backend python objects).
Context (ledger : GatewayReferenceLedger.gateway_reference_ledger) (held : list gateway_held_value) (reserved : list val)
    (captured : gateway_object_heap) (data : block) (data_offset : ptrofs) (source : mem)
    (REGIONS : gateway_module_descriptor_regions ge source).
Let original := Vptr data data_offset.
Let protected := gateway_validation_source_region ge.
Context (type_symbol dictionary integer bytes unicode none instance_symbol lookup_symbol next_symbol copy_symbol table json_name files_name : block)
    (instance_definition lookup_definition next_definition copy_definition : fundef)
    (TYPE_SYMBOL : Genv.find_symbol ge _host_has_type = Some type_symbol)
    (TYPE_FUNCTION : Genv.find_funct_ptr ge type_symbol = Some (Internal f_host_has_type))
    (DICTIONARY : Genv.find_symbol ge _PyDict_Type = Some dictionary) (INTEGER : Genv.find_symbol ge _PyLong_Type = Some integer)
    (BYTES : Genv.find_symbol ge _PyBytes_Type = Some bytes) (UNICODE : Genv.find_symbol ge _PyUnicode_Type = Some unicode)
    (NONE : Genv.find_symbol ge __Py_NoneStruct = Some none)
    (INSTANCE_SYMBOL : Genv.find_symbol ge _PyObject_IsInstance = Some instance_symbol)
    (INSTANCE_FUNCTION : Genv.find_funct_ptr ge instance_symbol = Some instance_definition)
    (INSTANCE_DEFINITION : gateway_object_api_definition gateway_api_is_instance = Some instance_definition)
    (INSTANCE_TYPE : type_of_fundef instance_definition = Tfunction [tptr (Tstruct __object noattr); tptr (Tstruct __object noattr)] tint cc_default)
    (LOOKUP_SYMBOL : Genv.find_symbol ge _PyDict_GetItemString = Some lookup_symbol)
    (LOOKUP_FUNCTION : Genv.find_funct_ptr ge lookup_symbol = Some lookup_definition)
    (LOOKUP_DEFINITION : gateway_object_api_definition gateway_api_dict_get_string = Some lookup_definition)
    (LOOKUP_TYPE : type_of_fundef lookup_definition = Tfunction [tptr (Tstruct __object noattr); tptr tschar] (tptr (Tstruct __object noattr)) cc_default)
    (NEXT_SYMBOL : Genv.find_symbol ge _PyDict_Next = Some next_symbol)
    (NEXT_FUNCTION : Genv.find_funct_ptr ge next_symbol = Some next_definition)
    (NEXT_DEFINITION : gateway_object_api_definition gateway_api_dict_next = Some next_definition)
    (NEXT_TYPE : type_of_fundef next_definition = Tfunction [tptr (Tstruct __object noattr); tptr tlong;
      tptr (tptr (Tstruct __object noattr)); tptr (tptr (Tstruct __object noattr))] tint cc_default)
    (COPY_SYMBOL : Genv.find_symbol ge _PyDict_Copy = Some copy_symbol)
    (COPY_FUNCTION : Genv.find_funct_ptr ge copy_symbol = Some copy_definition)
    (COPY_TYPE : type_of_fundef copy_definition = Tfunction [tptr (Tstruct __object noattr)] (tptr (Tstruct __object noattr)) cc_default)
    (TABLE : Genv.find_symbol ge _host_outcome_fields = Some table)
    (JSON_NAME : Genv.find_symbol ge ___stringlit_51 = Some json_name)
    (FILES_NAME : Genv.find_symbol ge ___stringlit_41 = Some files_name).

Theorem gateway_actual_outcome_validation before world events returned after next :
  gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source empty_env before world ->
  returned <> Vnullptr ->
  gateway_steps backend ge (gateway_live (Callstate (Internal f_host_outcome_from) [original] Kstop before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists fields metadata_field metadata_fields prefix suffix environment parameters memory current,
    gateway_object_values captured original = Some (gateway_dict_object fields) /\
    gateway_validated_fields none captured fields 14 /\
    gateway_dictionary_lookup gateway_outcome_json_name fields = Some metadata_field /\
    gateway_object_values captured (gateway_dictionary_value metadata_field) = Some (gateway_dict_object metadata_fields) /\
    events = prefix ++ suffix /\
    gateway_steps backend ge (gateway_live (Callstate (Internal f_host_outcome_from) [original] Kstop before) world) prefix
      (gateway_live (Callstate copy_definition [original] (gateway_outcome_copy_cont environment parameters) memory) current) /\
    gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment memory current /\
    gateway_steps backend ge
      (gateway_live (Callstate copy_definition [original] (gateway_outcome_copy_cont environment parameters) memory) current) suffix
      (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intros INPUT NONNULL RUN.
  destruct (gateway_actual_validation_entry backend python objects decimal_float detached io stable thread_errno heap_allocation threads references
    ge ledger held reserved captured original protected source before world events returned after next INPUT RUN)
    as (pending &body_events &entry_memory &entry_world &environment &allocated &ENTRY_EVENTS &PENDING &ENTRY &BUFFERS &BODY_BASE &BODY_RUN).
  destruct BUFFERS as [ALLOCATED [STACK [FRAME ABSENT]]].
  set (base := gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment).
  assert (LOCAL : forall identifier, In identifier [_host_has_type; _PyDict_Type; _PyLong_Type; _PyBytes_Type; _PyUnicode_Type;
    _host_outcome_fields; _PyDict_GetItemString; _PyDict_Next; _PyDict_Copy; ___stringlit_51; ___stringlit_41] -> environment ! identifier = None).
  { intros identifier PRESENT; apply ABSENT; cbn in PRESENT.
    repeat destruct PRESENT as [SAME |PRESENT]; try contradiction; subst identifier; cbn; intuition discriminate. }
  destruct (ALLOCATED _position tlong ltac:(cbn; tauto)) as [position [POSITION POSITION_FRESH]].
  destruct (ALLOCATED _key (tptr (Tstruct __object noattr)) ltac:(cbn; tauto)) as [key [KEY KEY_FRESH]].
  destruct (ALLOCATED _value__1 (tptr (Tstruct __object noattr)) ltac:(cbn; tauto)) as [value [VALUE VALUE_FRESH]].
  assert (POSITION_KEY : position <> key).
  { eapply (proj2 STACK); [exact POSITION |exact KEY |discriminate]. }
  assert (POSITION_VALUE : position <> value).
  { eapply (proj2 STACK); [exact POSITION |exact VALUE |discriminate]. }
  assert (KEY_VALUE : key <> value).
  { eapply (proj2 STACK); [exact KEY |exact VALUE |discriminate]. }
  destruct (gateway_actual_validation_first_check backend ge python objects decimal_float detached io stable thread_errno heap_allocation leases
    threads references instances ledger held reserved captured data data_offset protected source environment (gateway_outcome_parameters original)
    allocated entry_world body_events returned after next type_symbol dictionary none instance_symbol instance_definition
    ltac:(apply PTree.gss) (LOCAL _host_has_type ltac:(cbn; tauto)) (LOCAL _PyDict_Type ltac:(cbn; tauto))
    TYPE_SYMBOL TYPE_FUNCTION DICTIONARY NONE INSTANCE_SYMBOL INSTANCE_FUNCTION INSTANCE_DEFINITION INSTANCE_TYPE BODY_BASE NONNULL BODY_RUN)
    as (fields &first_prefix &field_events &first_parameters &first_memory &first_world &FIELDS &FIRST_EVENTS &FIRST_VALID &FIRST_INDEX &FIRST_DATA &TO_FIRST &FIRST_BASE &FROM_FIRST).
  destruct (gateway_actual_validation_field_loop backend ge python objects decimal_float detached io stable thread_errno heap_allocation leases
    threads references instances containers ledger held reserved captured data data_offset protected source environment
    type_symbol dictionary integer bytes unicode none instance_symbol lookup_symbol table instance_definition lookup_definition
    ltac:(intros identifier PRESENT; apply LOCAL; cbn in PRESENT |- *; tauto)
    TYPE_SYMBOL TYPE_FUNCTION DICTIONARY INTEGER BYTES UNICODE NONE INSTANCE_SYMBOL INSTANCE_FUNCTION INSTANCE_DEFINITION INSTANCE_TYPE
    LOOKUP_SYMBOL LOOKUP_FUNCTION LOOKUP_DEFINITION LOOKUP_TYPE TABLE
    (gateway_validation_linked_names_context python objects decimal_float ledger held reserved captured original ge source environment table REGIONS TABLE)
    fields 14 0 first_parameters first_memory first_world field_events returned after next
    eq_refl ltac:(intros index IMPOSSIBLE; lia) FIELDS FIRST_VALID FIRST_INDEX
    ltac:(rewrite FIRST_DATA; apply PTree.gss) FIRST_BASE NONNULL FROM_FIRST)
    as [VALIDATED [field_prefix [metadata_events [field_parameters [field_memory [field_world
      [FIELD_EVENTS [FIELD_VALID [FIELD_INDEX [FIELD_DATA [TO_FIELDS [FIELD_BASE FROM_FIELDS]]]]]]]]]]]].
  destruct (gateway_actual_validation_metadata backend ge python objects decimal_float detached io stable thread_errno heap_allocation leases
    threads references instances containers ledger held reserved captured data data_offset protected source environment
    type_symbol dictionary none instance_symbol lookup_symbol json_name files_name instance_definition lookup_definition
    ltac:(intros identifier PRESENT; apply LOCAL; cbn in PRESENT |- *; tauto)
    TYPE_SYMBOL TYPE_FUNCTION DICTIONARY NONE INSTANCE_SYMBOL INSTANCE_FUNCTION INSTANCE_DEFINITION INSTANCE_TYPE
    LOOKUP_SYMBOL LOOKUP_FUNCTION LOOKUP_DEFINITION LOOKUP_TYPE JSON_NAME FILES_NAME
    ltac:(intros memory current GOOD; eapply gateway_validation_linked_json_name;
      [eapply gateway_validation_linked_regions; [exact GOOD |exact REGIONS] |exact JSON_NAME])
    fields field_parameters field_memory field_world metadata_events returned after next
    FIELDS FIELD_VALID FIELD_INDEX ltac:(rewrite FIELD_DATA, FIRST_DATA; apply PTree.gss) FIELD_BASE NONNULL FROM_FIELDS)
    as (metadata_prefix &files_events &files_parameters &files_memory &files_world &metadata_field &metadata_fields &METADATA_EVENTS &METADATA_DATA
      &METADATA_LOOKUP &METADATA_DESCRIPTION &TO_METADATA &METADATA_BASE &FROM_METADATA).
  destruct (gateway_actual_validation_files_copy backend ge python objects decimal_float detached io stable thread_errno heap_allocation leases
    threads references instances containers iteration ledger held reserved captured data data_offset protected source environment position key value
    POSITION KEY VALUE POSITION_KEY POSITION_VALUE KEY_VALUE
    type_symbol unicode bytes none instance_symbol next_symbol copy_symbol files_name instance_definition next_definition copy_definition lookup_definition
    ltac:(intros identifier PRESENT; apply LOCAL; cbn in PRESENT |- *; tauto)
    TYPE_SYMBOL TYPE_FUNCTION UNICODE BYTES NONE INSTANCE_SYMBOL INSTANCE_FUNCTION INSTANCE_DEFINITION INSTANCE_TYPE
    NEXT_SYMBOL NEXT_FUNCTION NEXT_DEFINITION NEXT_TYPE COPY_SYMBOL COPY_FUNCTION COPY_TYPE LOOKUP_DEFINITION
    ltac:(intros memory current GOOD; eapply gateway_validation_linked_files_name;
      [eapply gateway_validation_linked_regions; [exact GOOD |exact REGIONS] |exact FILES_NAME])
    fields files_parameters files_memory files_world files_events returned after next FIELDS
    (VALIDATED 10%nat ltac:(lia)) ltac:(rewrite METADATA_DATA, FIELD_DATA, FIRST_DATA; apply PTree.gss) METADATA_BASE NONNULL FROM_METADATA)
    as (files_prefix &suffix &parameters &memory &current &FILES_EVENTS &TO_COPY &GOOD &REST).
  exists fields, metadata_field, metadata_fields,
    (pending ++ gateway_source E0 :: (first_prefix ++ field_prefix ++ metadata_prefix ++ files_prefix)), suffix, environment, parameters, memory, current.
  split; [exact FIELDS |split; [exact VALIDATED |split; [exact METADATA_LOOKUP |split; [exact METADATA_DESCRIPTION |split]]]].
  - rewrite ENTRY_EVENTS, FIRST_EVENTS, FIELD_EVENTS, METADATA_EVENTS, FILES_EVENTS.
    repeat rewrite <- app_assoc; cbn [app]; repeat rewrite <- app_assoc; reflexivity.
  - split.
    + eapply gateway_steps_append; [exact PENDING |].
      econstructor; [apply gateway_internal; [exact I |apply step_internal_function; exact ENTRY] |].
      eapply gateway_steps_append; [exact TO_FIRST |].
      eapply gateway_steps_append; [exact TO_FIELDS |].
      eapply gateway_steps_append; [exact TO_METADATA |exact TO_COPY].
    + exact (conj GOOD REST).
Qed.

Theorem gateway_actual_captured_outcome_validation ticket wire before world events returned after next :
  gateway_objects_ready (python world) (objects world) before ->
  gateway_reference_scope python objects decimal_float ledger held world ->
  In (gateway_reference_graph_capture ticket original wire captured) held ->
  (forall pointer, (count_occ Val.eq reserved pointer + gateway_reference_count ledger pointer <= python_native_strong (python world) pointer)%nat) ->
  gateway_native_region_owned (fun current object => gateway_native_private (python current) object) protected before world ->
  Mem.unchanged_on protected source before -> returned <> Vnullptr ->
  gateway_steps backend ge (gateway_live (Callstate (Internal f_host_outcome_from) [original] Kstop before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists fields metadata_field metadata_fields prefix suffix environment parameters memory current,
    gateway_object_values captured original = Some (gateway_dict_object fields) /\
    gateway_validated_fields none captured fields 14 /\
    gateway_dictionary_lookup gateway_outcome_json_name fields = Some metadata_field /\
    gateway_object_values captured (gateway_dictionary_value metadata_field) = Some (gateway_dict_object metadata_fields) /\
    events = prefix ++ suffix /\
    gateway_steps backend ge (gateway_live (Callstate (Internal f_host_outcome_from) [original] Kstop before) world) prefix
      (gateway_live (Callstate copy_definition [original] (gateway_outcome_copy_cont environment parameters) memory) current) /\
    gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment memory current /\
    gateway_steps backend ge
      (gateway_live (Callstate copy_definition [original] (gateway_outcome_copy_cont environment parameters) memory) current) suffix
      (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intros READY SCOPE MEMBER BUDGET OWNED FRAME NONNULL RUN.
  apply (gateway_actual_outcome_validation before world events returned after next); [|exact NONNULL |exact RUN].
  eapply gateway_validation_context_from_capture; eassumption.
Qed.
End CompleteValidation.
