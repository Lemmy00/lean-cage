(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The same actual constructor validates all fourteen source-indexed fields. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue
  GatewayObjectThreads GatewayObjectDiscipline GatewayOutcomeValidationContext GatewayValidationFields GatewayValidationFieldStep
  GatewayObjectInstances GatewayOutcomeValidationSource GatewayOutcomeValidationPaths GatewayOutcome
  GatewayThreadRuntime GatewayStreamInterface GatewayLocalRuntime GatewayReferenceThreads.
Import ListNotations.
Local Close Scope lean_scope.

Section ValidationFieldLoop.
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
Context (NAMES : forall index, (index < 14)%nat -> exists characters name,
    nth_error gateway_outcome_names index = Some characters /\ forall memory current, base memory current ->
      Mem.loadv Mptr memory (Vptr table (gateway_validation_name_offset index)) = Some (Vptr name Ptrofs.zero) /\
      gateway_object_name memory (Vptr name Ptrofs.zero) characters).

Theorem gateway_actual_validation_field_loop fields remaining index parameters before world events returned after next :
  (index + remaining = 14)%nat -> gateway_validated_fields none captured fields index ->
  gateway_object_values captured original = Some (gateway_dict_object fields) ->
  parameters ! _valid = Some (Vint Int.one) -> parameters ! _index = Some (Vint (Int.repr (Z.of_nat index))) ->
  parameters ! _data = Some original -> base before world -> returned <> Vnullptr ->
  gateway_steps backend ge
    (gateway_live (State f_host_outcome_from gateway_outcome_validation_loop_body gateway_validation_iteration_cont environment parameters before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  gateway_validated_fields none captured fields 14 /\
  exists prefix suffix selected memory current,
    events = prefix ++ suffix /\ selected ! _valid = Some (Vint Int.one) /\ selected ! _index = Some (Vint (Int.repr 14)) /\
    selected ! _data = parameters ! _data /\
    gateway_steps backend ge
      (gateway_live (State f_host_outcome_from gateway_outcome_validation_loop_body gateway_validation_iteration_cont environment parameters before) world) prefix
      (gateway_live (State f_host_outcome_from gateway_outcome_validation_loop_body gateway_validation_iteration_cont environment selected memory) current) /\
    base memory current /\
    gateway_steps backend ge
      (gateway_live (State f_host_outcome_from gateway_outcome_validation_loop_body gateway_validation_iteration_cont environment selected memory) current) suffix
      (gateway_live (Returnstate returned Kstop after) next).
Proof.
  revert index parameters before world events.
  induction remaining as [|remaining IH]; intros index parameters before world events BOUND VALIDATED FIELDS VALID INDEX DATA BASE NONNULL RUN.
  - assert (SAME : index = 14%nat) by lia; subst index.
    split; [exact VALIDATED |exists [], events, parameters, before, world; cbn].
    split; [reflexivity |split; [exact VALID |split; [exact INDEX |split; [reflexivity |split]]]].
    + constructor.
    + exact (conj BASE RUN).
  - assert (INDEX_BOUND : (index < 14)%nat) by lia.
    destruct (NAMES index INDEX_BOUND) as (characters &name &CHARACTERS &NAME).
    destruct (gateway_actual_validation_field_step backend ge python objects decimal_float detached io stable thread_errno heap_allocation leases
      threads references instances containers ledger held reserved captured data data_offset protected source environment
      type_symbol dictionary integer bytes unicode none instance_symbol lookup_symbol table instance_definition lookup_definition
      LOCAL TYPE_SYMBOL TYPE_FUNCTION DICTIONARY INTEGER BYTES UNICODE NONE INSTANCE_SYMBOL INSTANCE_FUNCTION INSTANCE_DEFINITION INSTANCE_TYPE
      LOOKUP_SYMBOL LOOKUP_FUNCTION LOOKUP_DEFINITION LOOKUP_TYPE TABLE
      fields index characters name parameters before world events returned after next
      INDEX_BOUND CHARACTERS FIELDS VALID INDEX DATA NAME BASE NONNULL RUN)
      as [FIELD [first [rest [intermediate [called [owner [EVENTS [CURRENT_VALID [CURRENT_INDEX [CURRENT_DATA [PREFIX [READY REST]]]]]]]]]]]].
    destruct (IH (S index) intermediate called owner rest ltac:(lia)
      (gateway_validation_fields_extend none captured fields index VALIDATED FIELD) FIELDS CURRENT_VALID CURRENT_INDEX
      ltac:(rewrite CURRENT_DATA; exact DATA) READY NONNULL REST)
      as [ALL [prefix [suffix [selected [memory [current [REST_EVENTS [FINAL_VALID [FINAL_INDEX [FINAL_DATA [TO_END [GOOD SUFFIX]]]]]]]]]]]].
    split; [exact ALL |exists (first ++ prefix), suffix, selected, memory, current].
    split; [rewrite EVENTS, REST_EVENTS, app_assoc; reflexivity |].
    split; [exact FINAL_VALID |split; [exact FINAL_INDEX |split; [rewrite FINAL_DATA; exact CURRENT_DATA |split]]].
    + eapply gateway_steps_append; [exact PREFIX |exact TO_END].
    + exact (conj GOOD SUFFIX).
Qed.
End ValidationFieldLoop.
