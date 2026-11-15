(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Each real validation iteration produces its indexed positive fact before advancing. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue
  GatewayObjectThreads GatewayObjectDiscipline GatewayOutcomeValidationContext GatewayValidationGraphFacts GatewayValidationFields
  GatewayValidationCheckCut GatewayValidationLookupCut GatewayValidationFailureJoin GatewayObjectInstances
  GatewayOutcomeValidationSource GatewayOutcomeValidationPaths GatewayOutcomeValidationProgress GatewaySourcePaths GatewaySourceSegments
  GatewayContexts GatewayFramedRuntime GatewayThreadRuntime GatewayStreamInterface GatewayLocalRuntime GatewayReferenceThreads GatewayOutcome.
Import ListNotations.
Local Close Scope lean_scope.

Section ValidationFieldStep.
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
Context (type_symbol dictionary integer bytes unicode none instance_symbol lookup_symbol table : block)
    (instance_definition lookup_definition : fundef)
    (LOCAL : forall identifier, In identifier [_host_has_type; _PyDict_Type; _PyLong_Type; _PyBytes_Type; _PyUnicode_Type;
      _host_outcome_fields; _PyDict_GetItemString] -> environment ! identifier = None)
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
    (TABLE : Genv.find_symbol ge _host_outcome_fields = Some table).

Theorem gateway_actual_validation_field_step fields index characters name parameters before world events returned after next :
  (index < 14)%nat -> nth_error gateway_outcome_names index = Some characters ->
  gateway_object_values captured original = Some (gateway_dict_object fields) ->
  parameters ! _valid = Some (Vint Int.one) -> parameters ! _index = Some (Vint (Int.repr (Z.of_nat index))) ->
  parameters ! _data = Some original ->
  (forall memory current, base memory current ->
    Mem.loadv Mptr memory (Vptr table (gateway_validation_name_offset index)) = Some (Vptr name Ptrofs.zero) /\
    gateway_object_name memory (Vptr name Ptrofs.zero) characters) ->
  base before world -> returned <> Vnullptr ->
  gateway_steps backend ge
    (gateway_live (State f_host_outcome_from gateway_outcome_validation_loop_body gateway_validation_iteration_cont environment parameters before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  gateway_validated_field none captured fields index /\
  exists prefix suffix selected memory current,
    events = prefix ++ suffix /\ selected ! _valid = Some (Vint Int.one) /\
    selected ! _index = Some (Vint (Int.repr (Z.of_nat (S index)))) /\ selected ! _data = parameters ! _data /\
    gateway_steps backend ge
      (gateway_live (State f_host_outcome_from gateway_outcome_validation_loop_body gateway_validation_iteration_cont environment parameters before) world) prefix
      (gateway_live (State f_host_outcome_from gateway_outcome_validation_loop_body gateway_validation_iteration_cont environment selected memory) current) /\
    base memory current /\
    gateway_steps backend ge
      (gateway_live (State f_host_outcome_from gateway_outcome_validation_loop_body gateway_validation_iteration_cont environment selected memory) current) suffix
      (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intros BOUND CHARACTERS FIELDS VALID INDEX DATA NAME BASE NONNULL RUN.
  assert (CLOSED : gateway_ambient_closed backend base).
  { exact (gateway_validation_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
      threads references ledger held reserved captured original protected source environment). }
  assert (TYPE_LOCAL : forall identifier, In identifier [_host_has_type; _PyDict_Type; _PyLong_Type; _PyBytes_Type; _PyUnicode_Type] ->
    environment ! identifier = None).
  { intros identifier PRESENT; apply LOCAL; cbn in PRESENT |- *; tauto. }
  destruct (gateway_validation_iteration_getter backend ge base environment parameters before Int.one index data data_offset table name lookup_symbol lookup_definition
    CLOSED VALID ltac:(change (0 < 1); lia) BOUND INDEX DATA (LOCAL _host_outcome_fields ltac:(cbn; tauto))
    (LOCAL _PyDict_GetItemString ltac:(cbn; tauto)) TABLE ltac:(intros; exact (proj1 (NAME _ _ H))) LOOKUP_SYMBOL LOOKUP_FUNCTION LOOKUP_TYPE)
    as (lookup_parameters &LOOKUP_PATH &LOOKUP_INDEX &LOOKUP_DATA &LOOKUP_NAME).
  destruct (gateway_source_path_cut backend ge _ _ _ base _ base LOOKUP_PATH before world events returned after next BASE RUN)
    as (lookup_prefix &lookup_rest &lookup_memory &lookup_world &LOOKUP_EVENTS &LOOKUP_QUIET &TO_LOOKUP &LOOKUP_BASE &LOOKUP_REST).
  destruct (gateway_actual_validation_lookup backend ge python objects decimal_float detached io stable thread_errno heap_allocation
    threads references containers ledger held reserved captured original protected source environment lookup_definition
    (Vptr name Ptrofs.zero) characters fields (gateway_validation_lookup_cont environment lookup_parameters)
    lookup_memory lookup_world lookup_rest returned after next LOOKUP_DEFINITION I
    ltac:(cbn [gateway_validation_lookup_cont gateway_cont_weight]; lia) FIELDS ltac:(intros; exact (proj2 (NAME _ _ H)))
    ltac:(intros memory first current es result last following TRUE EXEC; cbn in EXEC;
      eapply gateway_validation_missing_field_returns_null;
        [exact BOUND |rewrite LOOKUP_INDEX; exact INDEX |exact TYPE_LOCAL |exact TYPE_SYMBOL |exact TYPE_FUNCTION |
         exact DICTIONARY |exact INTEGER |exact BYTES |exact UNICODE |exact EXEC])
    LOOKUP_BASE NONNULL LOOKUP_REST)
    as (lookup_operation &type_events &field_memory &field_world &field &LOOKUP_REST_EVENTS &LOOKUP &REACHED &LOOKUP_OPERATION &FIELD_BASE &FROM_LOOKUP).
  destruct (gateway_validation_captured_builtin _ _ _ _ _ _ _ _ _ _ _ _ _ _ FIELD_BASE REACHED)
    as (description &kind &object &offset &DESCRIPTION &KIND &POINTER).
  rewrite POINTER in REACHED, DESCRIPTION, FROM_LOOKUP, LOOKUP_OPERATION.
  destruct (gateway_validation_lookup_type backend ge base environment lookup_parameters field_memory index (Vptr object offset)
    dictionary integer bytes unicode type_symbol CLOSED BOUND ltac:(right; eauto) ltac:(rewrite LOOKUP_INDEX; exact INDEX)
    TYPE_LOCAL TYPE_SYMBOL TYPE_FUNCTION DICTIONARY INTEGER BYTES UNICODE)
    as (type_parameters &TYPE_PATH &TYPE_INDEX &TYPE_DATA &TYPE_VALUE).
  destruct (gateway_source_path_cut backend ge _ _ _ base _ base TYPE_PATH field_memory field_world type_events returned after next FIELD_BASE FROM_LOOKUP)
    as (type_prefix &type_rest &type_memory &type_world &TYPE_EVENTS &TYPE_QUIET &TO_TYPE &TYPE_BASE &TYPE_REST).
  destruct (gateway_actual_positive_validation_call backend ge python objects decimal_float detached io stable thread_errno heap_allocation leases
    threads references instances ledger held reserved captured original protected source environment (fun _ _ => True)
    ltac:(auto) ltac:(auto) object offset description kind (gateway_validation_field_kind index)
    (gateway_validation_field_class dictionary integer bytes unicode index) Ptrofs.zero none (gateway_validation_optional index)
    (gateway_outcome_field_type_cont environment type_parameters) type_memory type_world type_rest returned after next instance_symbol instance_definition
    I ltac:(cbn [gateway_outcome_field_type_cont gateway_cont_weight]; lia) TYPE_BASE I REACHED DESCRIPTION KIND
    (gateway_validation_field_class_binding ge dictionary integer bytes unicode index DICTIONARY INTEGER BYTES UNICODE)
    (gateway_validation_field_optional index) NONE INSTANCE_SYMBOL INSTANCE_FUNCTION INSTANCE_DEFINITION INSTANCE_TYPE
    ltac:(intros status memory NONPOS; apply gateway_outcome_field_nonpositive_null with (index := Int.repr (Z.of_nat index));
      [rewrite TYPE_INDEX, LOOKUP_INDEX; exact INDEX |exact NONPOS]) NONNULL TYPE_REST)
    as (type_operation &update_events &after_type &after_type_world &TYPE_REST_EVENTS &TYPE_OPERATION &AFTER_TYPE &EXTRA &ACCEPT &FROM_TYPE).
  split.
  - exists characters, field, description, kind; split; [exact CHARACTERS |split; [exact LOOKUP |]].
    rewrite POINTER; exact (conj DESCRIPTION (conj KIND ACCEPT)).
  - pose proof (gateway_validation_field_update backend ge base environment type_parameters after_type Int.one CLOSED) as UPDATE_PATH.
    destruct (gateway_source_segment_cut backend ge _ _ _ _ UPDATE_PATH after_type after_type_world update_events returned after next AFTER_TYPE FROM_TYPE)
      as (update_prefix &turn_events &updated &updated_world &UPDATE_EVENTS &UPDATE_QUIET &UPDATE_PREFIX &UPDATED &TURN_EVENTS).
    set (updated_parameters := gateway_validation_after_field type_parameters Int.one).
    assert (UPDATED_INDEX : updated_parameters ! _index = Some (Vint (Int.repr (Z.of_nat index)))).
    { unfold updated_parameters, gateway_validation_after_field, set_opttemp; repeat rewrite PTree.gso by discriminate.
      rewrite TYPE_INDEX, LOOKUP_INDEX; exact INDEX. }
    pose proof (gateway_validation_loop_turn backend ge base environment updated_parameters updated (Int.repr (Z.of_nat index)) CLOSED UPDATED_INDEX) as TURN_PATH.
    destruct (gateway_source_segment_cut backend ge _ _ _ _ TURN_PATH updated updated_world turn_events returned after next UPDATED TURN_EVENTS)
      as (turn_prefix &suffix &memory &current &TURN_EVENT_LIST &TURN_QUIET &TO_NEXT &GOOD &REST).
    exists (lookup_prefix ++ lookup_operation ++ type_prefix ++ type_operation ++ update_prefix ++ turn_prefix), suffix,
      (PTree.set _index (Vint (Int.add (Int.repr (Z.of_nat index)) Int.one)) updated_parameters), memory, current.
    split; [rewrite LOOKUP_EVENTS, LOOKUP_REST_EVENTS, TYPE_EVENTS, TYPE_REST_EVENTS, UPDATE_EVENTS, TURN_EVENT_LIST;
      repeat rewrite app_assoc; reflexivity |split].
    + rewrite PTree.gso by discriminate; unfold updated_parameters, gateway_validation_after_field; apply PTree.gss.
    + split; [rewrite PTree.gss, gateway_validation_field_counter by exact BOUND; reflexivity |split].
      * rewrite PTree.gso by discriminate; unfold updated_parameters, gateway_validation_after_field, set_opttemp;
          repeat rewrite PTree.gso by discriminate; rewrite TYPE_DATA; exact LOOKUP_DATA.
      * split.
        -- eapply gateway_steps_append; [exact TO_LOOKUP |].
           eapply gateway_steps_append; [exact (gateway_plug_steps backend ge _ _ _ (gateway_validation_lookup_cont environment lookup_parameters) I LOOKUP_OPERATION) |].
           eapply gateway_steps_append; [exact TO_TYPE |].
           eapply gateway_steps_append; [exact (gateway_plug_steps backend ge _ _ _ (gateway_outcome_field_type_cont environment type_parameters) I TYPE_OPERATION) |].
           eapply gateway_steps_append; [exact UPDATE_PREFIX |exact TO_NEXT].
        -- exact (conj GOOD REST).
Qed.
End ValidationFieldStep.
