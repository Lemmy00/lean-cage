(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Successful file checks reach the next actual iterator with the same original inputs. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue
  GatewayObjectThreads GatewayObjectDiscipline GatewayOutcomeValidationContext GatewayValidationGraphFacts
  GatewayValidationCheckCut GatewayValidationSlots GatewayValidationFilesInputs GatewayValidationIterationRuntime
  GatewayOutcomeFilesSource GatewayOutcomeFilesIteration GatewayOutcomeValidationPaths GatewaySourcePaths GatewayContexts
  GatewayFramedRuntime GatewayThreadRuntime GatewayStreamInterface GatewayLocalRuntime GatewayReferenceThreads GatewayObjectInstances.
Import ListNotations.
Local Close Scope lean_scope.

Section ValidationFileChecks.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (python : World -> python_world) (objects : World -> gateway_object_heap)
    (decimal_float : list Z -> Floats.float -> Prop) (detached : val -> mem -> World -> Prop)
    (io : Event -> option gateway_native_io) (stable : World -> block -> Z -> Prop)
    (thread_errno : World -> int) (heap_allocation : block -> Z -> Prop) (leases : World -> nat -> val -> Prop)
    (threads : gateway_thread_runtime backend io (fun current object => gateway_native_private (python current) object) stable
      (gateway_python_discipline python objects detached) thread_errno)
    (references : gateway_reference_thread_contract backend (fun current object => gateway_native_private (python current) object) stable
      (gateway_python_discipline python objects detached) heap_allocation python objects)
    (instances : gateway_instance_runtime backend ge python objects leases).
Context (ledger : GatewayReferenceLedger.gateway_reference_ledger) (held : list gateway_held_value) (reserved : list val)
    (captured : gateway_object_heap) (original : val) (protected : block -> Z -> Prop) (source : mem) (environment : env).
Let base := gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment.
Let slots saved := fun memory world => base memory world /\ gateway_validation_slot_snapshot environment saved memory world.

Theorem gateway_actual_validation_file_checks parameters before world events returned after next
    field files files_offset position key value cursor type_symbol unicode bytes none instance_symbol instance_definition next_symbol next_definition :
  parameters ! _files = Some (Vptr files files_offset) ->
  environment ! _position = Some (position, tlong) -> environment ! _key = Some (key, tptr (Tstruct __object noattr)) ->
  environment ! _value__1 = Some (value, tptr (Tstruct __object noattr)) ->
  (forall identifier, In identifier [_host_has_type; _PyUnicode_Type; _PyBytes_Type; _PyDict_Next] -> environment ! identifier = None) ->
  Genv.find_symbol ge _host_has_type = Some type_symbol -> Genv.find_funct_ptr ge type_symbol = Some (Internal f_host_has_type) ->
  Genv.find_symbol ge _PyUnicode_Type = Some unicode -> Genv.find_symbol ge _PyBytes_Type = Some bytes ->
  Genv.find_symbol ge __Py_NoneStruct = Some none ->
  Genv.find_symbol ge _PyObject_IsInstance = Some instance_symbol -> Genv.find_funct_ptr ge instance_symbol = Some instance_definition ->
  gateway_object_api_definition gateway_api_is_instance = Some instance_definition ->
  type_of_fundef instance_definition = Tfunction [tptr (Tstruct __object noattr); tptr (Tstruct __object noattr)] tint cc_default ->
  Genv.find_symbol ge _PyDict_Next = Some next_symbol -> Genv.find_funct_ptr ge next_symbol = Some next_definition ->
  type_of_fundef next_definition = Tfunction [tptr (Tstruct __object noattr); tptr tlong;
    tptr (tptr (Tstruct __object noattr)); tptr (tptr (Tstruct __object noattr))] tint cc_default ->
  gateway_object_reachable captured original (gateway_dictionary_key field) ->
  gateway_object_reachable captured original (gateway_dictionary_value field) ->
  base before world -> Mem.load Mint64 before position 0 = Some (Vlong cursor) ->
  Mem.load Mptr before key 0 = Some (gateway_dictionary_key field) ->
  Mem.load Mptr before value 0 = Some (gateway_dictionary_value field) -> returned <> Vnullptr ->
  gateway_steps backend ge
    (gateway_live (Returnstate (Vint Int.one) (gateway_validation_next_cont environment parameters) before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix selected memory current,
    events = prefix ++ suffix /\ selected ! _files = parameters ! _files /\ selected ! _data = parameters ! _data /\
    gateway_steps backend ge
      (gateway_live (Returnstate (Vint Int.one) (gateway_validation_next_cont environment parameters) before) world) prefix
      (gateway_live (Callstate next_definition [Vptr files files_offset; Vptr position Ptrofs.zero; Vptr key Ptrofs.zero; Vptr value Ptrofs.zero]
        (gateway_validation_next_cont environment selected) memory) current) /\
    base memory current /\ Mem.load Mint64 memory position 0 = Some (Vlong cursor) /\
    gateway_steps backend ge
      (gateway_live (Callstate next_definition [Vptr files files_offset; Vptr position Ptrofs.zero; Vptr key Ptrofs.zero; Vptr value Ptrofs.zero]
        (gateway_validation_next_cont environment selected) memory) current) suffix
      (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intros FILES POSITION KEY VALUE LOCAL TYPE_SYMBOL TYPE_FUNCTION UNICODE BYTES NONE INSTANCE_SYMBOL INSTANCE_FUNCTION INSTANCE_DEFINITION INSTANCE_TYPE
    NEXT_SYMBOL NEXT_FUNCTION NEXT_TYPE KEY_REACHED VALUE_REACHED BASE CURSOR KEY_LOAD VALUE_LOAD NONNULL RUN.
  destruct (gateway_validation_captured_builtin _ _ _ _ _ _ _ _ _ _ _ _ _ _ BASE KEY_REACHED)
    as (key_description &key_kind &name &name_offset &KEY_DESCRIPTION &KEY_KIND &NAME).
  destruct (gateway_validation_captured_builtin _ _ _ _ _ _ _ _ _ _ _ _ _ _ BASE VALUE_REACHED)
    as (value_description &value_kind &data &data_offset &VALUE_DESCRIPTION &VALUE_KIND &DATA).
  rewrite NAME in KEY_REACHED, KEY_DESCRIPTION, KEY_LOAD; rewrite DATA in VALUE_REACHED, VALUE_DESCRIPTION, VALUE_LOAD.
  assert (CLOSED : gateway_ambient_closed backend (slots before)).
  { eapply gateway_validation_iteration_slots_closed; eassumption. }
  assert (KEY_SAVED : forall memory current, slots before memory current -> Mem.load Mptr memory key 0 = Some (Vptr name name_offset)).
  { intros memory current [GOOD SNAPSHOT]; eapply gateway_validation_saved_slot; [exact BASE |exact SNAPSHOT |exact KEY |exact KEY_LOAD]. }
  assert (VALUE_SAVED : forall memory current, slots before memory current -> Mem.load Mptr memory value 0 = Some (Vptr data data_offset)).
  { intros memory current [GOOD SNAPSHOT]; eapply gateway_validation_saved_slot; [exact BASE |exact SNAPSHOT |exact VALUE |exact VALUE_LOAD]. }
  destruct (gateway_validation_file_name_inputs backend ge (slots before) environment parameters before key name name_offset unicode type_symbol
    CLOSED KEY KEY_SAVED (LOCAL _host_has_type ltac:(cbn; tauto)) (LOCAL _PyUnicode_Type ltac:(cbn; tauto)) TYPE_SYMBOL TYPE_FUNCTION UNICODE)
    as (name_parameters &NAME_PATH &NAME_FILES &NAME_DATA).
  destruct (gateway_source_path_cut backend ge _ _ _ (slots before) _ (slots before) NAME_PATH before world events returned after next
    (conj BASE (Mem.unchanged_on_refl _ _)) RUN)
    as (name_prefix &name_rest &name_memory &name_world &NAME_EVENTS &NAME_QUIET &TO_NAME &[NAME_BASE NAME_SNAPSHOT] &NAME_REST).
  destruct (gateway_actual_positive_validation_call backend ge python objects decimal_float detached io stable thread_errno heap_allocation leases
    threads references instances ledger held reserved captured original protected source environment
    (gateway_validation_slot_snapshot environment before)
    ltac:(intros; eapply gateway_validation_slots_ambient; [exact threads |eassumption |eassumption |eassumption])
    ltac:(intros; eapply gateway_validation_slots_observer; eassumption)
    name name_offset key_description key_kind gateway_unicode_kind unicode Ptrofs.zero none Int.zero
    (gateway_validation_name_cont environment name_parameters) name_memory name_world name_rest returned after next instance_symbol instance_definition
    I ltac:(cbn [gateway_validation_name_cont gateway_cont_weight]; lia) NAME_BASE NAME_SNAPSHOT
    KEY_REACHED KEY_DESCRIPTION KEY_KIND (gateway_builtin_unicode_type ge unicode UNICODE) (or_introl eq_refl) NONE
    INSTANCE_SYMBOL INSTANCE_FUNCTION INSTANCE_DEFINITION INSTANCE_TYPE
    ltac:(intros; apply gateway_validation_bad_file_name; assumption) NONNULL NAME_REST)
    as (name_operation &bytes_events &after_name &after_name_world &NAME_REST_EVENTS &NAME_OPERATION &AFTER_NAME &AFTER_NAME_SNAPSHOT &NAME_ACCEPT &FROM_NAME).
  destruct (gateway_validation_file_bytes_inputs backend ge (slots before) environment name_parameters after_name value data data_offset bytes type_symbol
    CLOSED VALUE VALUE_SAVED (LOCAL _host_has_type ltac:(cbn; tauto)) (LOCAL _PyBytes_Type ltac:(cbn; tauto)) TYPE_SYMBOL TYPE_FUNCTION BYTES)
    as (bytes_parameters &BYTES_PATH &BYTES_FILES &BYTES_DATA).
  destruct (gateway_source_path_cut backend ge _ _ _ (slots before) _ (slots before) BYTES_PATH after_name after_name_world bytes_events returned after next
    (conj AFTER_NAME AFTER_NAME_SNAPSHOT) FROM_NAME)
    as (bytes_prefix &bytes_rest &bytes_memory &bytes_world &BYTES_EVENTS &BYTES_QUIET &TO_BYTES &[BYTES_BASE BYTES_SNAPSHOT] &BYTES_REST).
  destruct (gateway_actual_positive_validation_call backend ge python objects decimal_float detached io stable thread_errno heap_allocation leases
    threads references instances ledger held reserved captured original protected source environment
    (gateway_validation_slot_snapshot environment before)
    ltac:(intros; eapply gateway_validation_slots_ambient; [exact threads |eassumption |eassumption |eassumption])
    ltac:(intros; eapply gateway_validation_slots_observer; eassumption)
    data data_offset value_description value_kind gateway_bytes_kind bytes Ptrofs.zero none Int.zero
    (gateway_validation_bytes_cont environment bytes_parameters) bytes_memory bytes_world bytes_rest returned after next instance_symbol instance_definition
    I ltac:(cbn [gateway_validation_bytes_cont gateway_cont_weight]; lia) BYTES_BASE BYTES_SNAPSHOT
    VALUE_REACHED VALUE_DESCRIPTION VALUE_KIND (gateway_builtin_bytes_type ge bytes BYTES) (or_introl eq_refl) NONE
    INSTANCE_SYMBOL INSTANCE_FUNCTION INSTANCE_DEFINITION INSTANCE_TYPE
    ltac:(intros; apply gateway_validation_bad_file_bytes; assumption) NONNULL BYTES_REST)
    as (bytes_operation &next_events &after_bytes &after_bytes_world &BYTES_REST_EVENTS &BYTES_OPERATION &AFTER_BYTES &AFTER_BYTES_SNAPSHOT &BYTES_ACCEPT &FROM_BYTES).
  destruct (gateway_validation_iterator_again backend ge (slots before) environment bytes_parameters after_bytes Int.one files files_offset position key value next_symbol next_definition
    CLOSED ltac:(change (0 < 1); lia) ltac:(rewrite BYTES_FILES, NAME_FILES; exact FILES)
    POSITION KEY VALUE (LOCAL _PyDict_Next ltac:(cbn; tauto)) NEXT_SYMBOL NEXT_FUNCTION NEXT_TYPE)
    as (selected &NEXT_PATH &NEXT_FILES &NEXT_DATA).
  destruct (gateway_source_path_cut backend ge _ _ _ (slots before) _ (slots before) NEXT_PATH after_bytes after_bytes_world next_events returned after next
    (conj AFTER_BYTES AFTER_BYTES_SNAPSHOT) FROM_BYTES)
    as (next_prefix &suffix &memory &current &NEXT_EVENTS &NEXT_QUIET &TO_NEXT &[GOOD SNAPSHOT] &REST).
  exists (name_prefix ++ name_operation ++ bytes_prefix ++ bytes_operation ++ next_prefix), suffix, selected, memory, current.
  split; [rewrite NAME_EVENTS, NAME_REST_EVENTS, BYTES_EVENTS, BYTES_REST_EVENTS, NEXT_EVENTS; repeat rewrite app_assoc; reflexivity |].
  split; [rewrite NEXT_FILES, BYTES_FILES; exact NAME_FILES |split; [rewrite NEXT_DATA, BYTES_DATA; exact NAME_DATA |split]].
  - eapply gateway_steps_append; [exact TO_NAME |].
    eapply gateway_steps_append; [exact (gateway_plug_steps backend ge _ _ _
      (gateway_validation_name_cont environment name_parameters) I NAME_OPERATION) |].
    eapply gateway_steps_append; [exact TO_BYTES |].
    eapply gateway_steps_append; [exact (gateway_plug_steps backend ge _ _ _
      (gateway_validation_bytes_cont environment bytes_parameters) I BYTES_OPERATION) |exact TO_NEXT].
  - split; [exact GOOD |split; [|exact REST]].
    eapply gateway_validation_saved_slot; [exact BASE |exact SNAPSHOT |exact POSITION |exact CURSOR].
Qed.
End ValidationFileChecks.
