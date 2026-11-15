(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual required files lookup, cursor initialization and loop reach the same copy call. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue
  GatewayObjectThreads GatewayObjectDiscipline GatewayOutcomeValidationContext GatewayValidationGraphFacts GatewayValidationFields GatewayValidationFieldLayouts
  GatewayValidationLookupCut GatewayValidationPositionEntry GatewayValidationFilesLoop GatewayDictionaryIteration GatewayObjectInstances
  GatewayOutcomeLookupSource GatewayOutcomeFilesSource GatewayOutcomeCopySource GatewayContexts GatewaySourceCuts
  GatewayThreadRuntime GatewayStreamInterface GatewayLocalRuntime GatewayReferenceThreads.
Import ListNotations.
Local Close Scope lean_scope.

Section ValidationFilesCopy.
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
    (captured : gateway_object_heap) (data : block) (data_offset : ptrofs) (protected : block -> Z -> Prop) (source : mem) (environment : env)
    (position key value : block)
    (POSITION : environment ! _position = Some (position, tlong))
    (KEY : environment ! _key = Some (key, tptr (Tstruct __object noattr)))
    (VALUE : environment ! _value__1 = Some (value, tptr (Tstruct __object noattr)))
    (POSITION_KEY : position <> key) (POSITION_VALUE : position <> value) (KEY_VALUE : key <> value).
Let original := Vptr data data_offset.
Let base := gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment.
Context (type_symbol unicode bytes none instance_symbol next_symbol copy_symbol files_name : block)
    (instance_definition next_definition copy_definition lookup_definition : fundef)
    (LOCAL : forall identifier, In identifier [_host_has_type; _PyUnicode_Type; _PyBytes_Type; _PyDict_Next; _PyDict_Copy] ->
      environment ! identifier = None)
    (TYPE_SYMBOL : Genv.find_symbol ge _host_has_type = Some type_symbol)
    (TYPE_FUNCTION : Genv.find_funct_ptr ge type_symbol = Some (Internal f_host_has_type))
    (UNICODE : Genv.find_symbol ge _PyUnicode_Type = Some unicode) (BYTES : Genv.find_symbol ge _PyBytes_Type = Some bytes)
    (NONE : Genv.find_symbol ge __Py_NoneStruct = Some none)
    (INSTANCE_SYMBOL : Genv.find_symbol ge _PyObject_IsInstance = Some instance_symbol)
    (INSTANCE_FUNCTION : Genv.find_funct_ptr ge instance_symbol = Some instance_definition)
    (INSTANCE_DEFINITION : gateway_object_api_definition gateway_api_is_instance = Some instance_definition)
    (INSTANCE_TYPE : type_of_fundef instance_definition = Tfunction [tptr (Tstruct __object noattr); tptr (Tstruct __object noattr)] tint cc_default)
    (NEXT_SYMBOL : Genv.find_symbol ge _PyDict_Next = Some next_symbol)
    (NEXT_FUNCTION : Genv.find_funct_ptr ge next_symbol = Some next_definition)
    (NEXT_DEFINITION : gateway_object_api_definition gateway_api_dict_next = Some next_definition)
    (NEXT_TYPE : type_of_fundef next_definition = Tfunction [tptr (Tstruct __object noattr); tptr tlong;
      tptr (tptr (Tstruct __object noattr)); tptr (tptr (Tstruct __object noattr))] tint cc_default)
    (COPY_SYMBOL : Genv.find_symbol ge _PyDict_Copy = Some copy_symbol)
    (COPY_FUNCTION : Genv.find_funct_ptr ge copy_symbol = Some copy_definition)
    (COPY_TYPE : type_of_fundef copy_definition = Tfunction [tptr (Tstruct __object noattr)] (tptr (Tstruct __object noattr)) cc_default)
    (LOOKUP_DEFINITION : gateway_object_api_definition gateway_api_dict_get_string = Some lookup_definition)
    (FILES_TEXT : forall memory current, base memory current -> gateway_object_name memory (Vptr files_name Ptrofs.zero) [102; 105; 108; 101; 115]).

Theorem gateway_actual_validation_files_copy fields parameters before world events returned after next :
  gateway_object_values captured original = Some (gateway_dict_object fields) -> gateway_validated_field none captured fields 10 ->
  parameters ! _data = Some original -> base before world -> returned <> Vnullptr ->
  gateway_steps backend ge
    (gateway_live (Callstate lookup_definition [original; Vptr files_name Ptrofs.zero]
      (gateway_outcome_files_lookup_cont environment parameters) before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix selected memory current,
    events = prefix ++ suffix /\
    gateway_steps backend ge
      (gateway_live (Callstate lookup_definition [original; Vptr files_name Ptrofs.zero]
        (gateway_outcome_files_lookup_cont environment parameters) before) world) prefix
      (gateway_live (Callstate copy_definition [original] (gateway_outcome_copy_cont environment selected) memory) current) /\
    base memory current /\
    gateway_steps backend ge
      (gateway_live (Callstate copy_definition [original] (gateway_outcome_copy_cont environment selected) memory) current) suffix
      (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intros FIELDS VALIDATED DATA BASE NONNULL RUN.
  destruct (gateway_validated_files_dictionary none captured fields VALIDATED) as (file_field &contents &FILES_LOOKUP &FILES_DESCRIPTION).
  destruct (gateway_actual_validation_lookup backend ge python objects decimal_float detached io stable thread_errno heap_allocation
    threads references containers ledger held reserved captured original protected source environment lookup_definition
    (Vptr files_name Ptrofs.zero) [102; 105; 108; 101; 115] fields (gateway_outcome_files_lookup_cont environment parameters)
    before world events returned after next LOOKUP_DEFINITION I ltac:(cbn [gateway_outcome_files_lookup_cont gateway_cont_weight]; lia)
    FIELDS FILES_TEXT
    ltac:(intros memory first current es result last following TRUE EXEC; cbn in EXEC;
      exact (gateway_actual_outcome_missing_files_returns_null backend ge environment parameters first current es result last following EXEC))
    BASE NONNULL RUN)
    as (lookup_operation &position_events &field_memory &field_world &field &LOOKUP_EVENTS &LOOKUP &REACHED &LOOKUP_OPERATION &FIELD_BASE &FROM_LOOKUP).
  assert (SAME_FIELD : file_field = field) by congruence; subst file_field.
  destruct (gateway_validation_captured_builtin _ _ _ _ _ _ _ _ _ _ _ _ _ _ FIELD_BASE REACHED)
    as (description &kind &files &files_offset &DESCRIPTION &KIND &POINTER).
  rewrite POINTER in REACHED, FILES_DESCRIPTION, FROM_LOOKUP, LOOKUP_OPERATION.
  destruct (gateway_actual_validation_position_entry backend ge python objects decimal_float detached io stable thread_errno heap_allocation
    threads references ledger held reserved captured original protected source environment parameters field_memory field_world position_events returned after next
    files files_offset position key value next_symbol next_definition REACHED POSITION KEY VALUE (LOCAL _PyDict_Next ltac:(cbn; tauto))
    NEXT_SYMBOL NEXT_FUNCTION NEXT_TYPE FIELD_BASE FROM_LOOKUP)
    as (position_prefix &loop_events &loop_parameters &loop_memory &loop_world &POSITION_EVENTS &LOOP_FILES &LOOP_DATA &TO_LOOP &LOOP_BASE &CURSOR &FROM_LOOP).
  destruct (gateway_actual_validation_files_loop backend ge python objects decimal_float detached io stable thread_errno heap_allocation leases
    threads references instances iteration ledger held reserved captured data data_offset protected source environment files files_offset contents position key value
    REACHED FILES_DESCRIPTION POSITION KEY VALUE POSITION_KEY POSITION_VALUE KEY_VALUE LOCAL
    type_symbol unicode bytes none instance_symbol next_symbol copy_symbol instance_definition next_definition copy_definition
    TYPE_SYMBOL TYPE_FUNCTION UNICODE BYTES NONE INSTANCE_SYMBOL INSTANCE_FUNCTION INSTANCE_DEFINITION INSTANCE_TYPE
    NEXT_SYMBOL NEXT_FUNCTION NEXT_DEFINITION NEXT_TYPE COPY_SYMBOL COPY_FUNCTION COPY_TYPE
    loop_parameters loop_memory loop_world loop_events returned after next Int64.zero
    LOOP_FILES ltac:(rewrite LOOP_DATA; exact DATA) LOOP_BASE CURSOR NONNULL FROM_LOOP)
    as (loop_prefix &suffix &selected &memory &current &LOOP_EVENTS &TO_COPY &GOOD &REST).
  exists (lookup_operation ++ position_prefix ++ loop_prefix), suffix, selected, memory, current.
  split; [rewrite LOOKUP_EVENTS, POSITION_EVENTS, LOOP_EVENTS; repeat rewrite app_assoc; reflexivity |split].
  - eapply gateway_steps_append; [exact (gateway_plug_steps backend ge _ _ _ (gateway_outcome_files_lookup_cont environment parameters) I LOOKUP_OPERATION) |].
    eapply gateway_steps_append; [exact TO_LOOP |exact TO_COPY].
  - exact (conj GOOD REST).
Qed.
End ValidationFilesCopy.
