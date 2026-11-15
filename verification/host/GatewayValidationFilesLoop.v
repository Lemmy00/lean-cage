(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual files loop establishes the same private-copy frontier. *)
From Stdlib Require Import ZArith List Lia Arith.Wf_nat.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue
  GatewayObjectThreads GatewayObjectDiscipline GatewayOutcomeValidationContext GatewayValidationGraphFacts
  GatewayValidationFileChecks GatewayValidationIterationRuntime GatewayDictionaryIteration GatewayValidationCopyCut
  GatewayOutcomeFilesSource GatewayOutcomeFilesIteration GatewayOutcomeCopySource GatewayContexts
  GatewayThreadRuntime GatewayStreamInterface GatewayLocalRuntime GatewayReferenceThreads GatewayObjectInstances.
Import ListNotations.
Local Close Scope lean_scope.

Section ValidationFilesLoop.
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
    (iteration : gateway_dictionary_iteration_runtime backend python objects).
Context (ledger : GatewayReferenceLedger.gateway_reference_ledger) (held : list gateway_held_value) (reserved : list val)
    (captured : gateway_object_heap) (data : block) (data_offset : ptrofs) (protected : block -> Z -> Prop) (source : mem) (environment : env)
    (files : block) (files_offset : ptrofs) (fields : list gateway_dictionary_entry) (position key value : block).
Let original := Vptr data data_offset.
Let dictionary := Vptr files files_offset.
Let base := gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment.
Context (FILES_REACHED : gateway_object_reachable captured original dictionary)
    (FILES_DESCRIPTION : gateway_object_values captured dictionary = Some (gateway_dict_object fields))
    (POSITION : environment ! _position = Some (position, tlong))
    (KEY : environment ! _key = Some (key, tptr (Tstruct __object noattr)))
    (VALUE : environment ! _value__1 = Some (value, tptr (Tstruct __object noattr)))
    (POSITION_KEY : position <> key) (POSITION_VALUE : position <> value) (KEY_VALUE : key <> value)
    (LOCAL : forall identifier, In identifier [_host_has_type; _PyUnicode_Type; _PyBytes_Type; _PyDict_Next; _PyDict_Copy] ->
      environment ! identifier = None).
Context (type_symbol unicode bytes none instance_symbol next_symbol copy_symbol : block)
    (instance_definition next_definition copy_definition : fundef)
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
    (COPY_TYPE : type_of_fundef copy_definition = Tfunction [tptr (Tstruct __object noattr)] (tptr (Tstruct __object noattr)) cc_default).

Theorem gateway_actual_validation_files_loop parameters before world events returned after next cursor :
  parameters ! _files = Some dictionary -> parameters ! _data = Some original ->
  base before world -> Mem.load Mint64 before position 0 = Some (Vlong cursor) -> returned <> Vnullptr ->
  gateway_steps backend ge
    (gateway_live (Callstate next_definition [dictionary; Vptr position Ptrofs.zero; Vptr key Ptrofs.zero; Vptr value Ptrofs.zero]
      (gateway_validation_next_cont environment parameters) before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix selected memory current,
    events = prefix ++ suffix /\
    gateway_steps backend ge
      (gateway_live (Callstate next_definition [dictionary; Vptr position Ptrofs.zero; Vptr key Ptrofs.zero; Vptr value Ptrofs.zero]
        (gateway_validation_next_cont environment parameters) before) world) prefix
      (gateway_live (Callstate copy_definition [original] (gateway_outcome_copy_cont environment selected) memory) current) /\
    base memory current /\
    gateway_steps backend ge
      (gateway_live (Callstate copy_definition [original] (gateway_outcome_copy_cont environment selected) memory) current) suffix
      (gateway_live (Returnstate returned Kstop after) next).
Proof.
  remember (length events) as amount eqn:SIZE.
  revert events parameters before world cursor SIZE.
  induction amount using lt_wf_ind; intros events parameters before world cursor SIZE FILES DATA BASE CURSOR NONNULL RUN.
  destruct (gateway_return_cut backend ge next_definition
    [dictionary; Vptr position Ptrofs.zero; Vptr key Ptrofs.zero; Vptr value Ptrofs.zero]
    (gateway_validation_next_cont environment parameters) before world events (Returnstate returned Kstop after) next
    I ltac:(cbn [gateway_continuation gateway_validation_next_cont gateway_cont_weight]; lia) RUN)
    as (operation &rest &result &changed &following &EVENTS &OPERATION &REST).
  destruct (gateway_actual_validation_iterator backend ge python objects decimal_float detached io stable thread_errno heap_allocation
    threads references iteration ledger held reserved captured original protected source environment next_definition dictionary fields position key value cursor
    before world operation result changed following NEXT_DEFINITION FILES_REACHED FILES_DESCRIPTION POSITION KEY VALUE
    POSITION_KEY POSITION_VALUE KEY_VALUE BASE CURSOR OPERATION) as [POSITIVE [CHANGED [END |ITEM]]].
  - destruct END as [SAME CURSOR_SAME]; subst result.
    destruct (gateway_actual_validation_eof_copy backend ge python objects decimal_float detached io stable thread_errno heap_allocation
      threads references ledger held reserved captured data data_offset protected source environment parameters changed following rest returned after next copy_symbol copy_definition
      CHANGED DATA (LOCAL _PyDict_Copy ltac:(cbn; tauto)) COPY_SYMBOL COPY_FUNCTION COPY_TYPE REST)
      as (to_copy &suffix &memory &current &REST_EVENTS &TO_COPY &GOOD &SUFFIX).
    exists (operation ++ to_copy), suffix, (set_opttemp (Some _t'15) (Vint Int.zero) parameters), memory, current.
    split; [rewrite EVENTS, REST_EVENTS, app_assoc; reflexivity |split].
    + eapply gateway_steps_append; [exact (gateway_plug_steps backend ge _ _ _
        (gateway_validation_next_cont environment parameters) I OPERATION) |exact TO_COPY].
    + exact (conj GOOD SUFFIX).
  - destruct ITEM as [SAME [field [following_cursor [MEMBER [RANGE [POSITION_LOAD [KEY_LOAD VALUE_LOAD]]]]]]]; subst result.
    destruct (gateway_validation_dictionary_field_reachable captured original dictionary fields field FILES_REACHED FILES_DESCRIPTION MEMBER)
      as [KEY_REACHED VALUE_REACHED].
    destruct (gateway_actual_validation_file_checks backend ge python objects decimal_float detached io stable thread_errno heap_allocation leases
      threads references instances ledger held reserved captured original protected source environment parameters changed following rest returned after next
      field files files_offset position key value following_cursor type_symbol unicode bytes none instance_symbol instance_definition next_symbol next_definition
      FILES POSITION KEY VALUE ltac:(intros identifier PRESENT; apply LOCAL; cbn in PRESENT |- *; tauto)
      TYPE_SYMBOL TYPE_FUNCTION UNICODE BYTES NONE INSTANCE_SYMBOL INSTANCE_FUNCTION INSTANCE_DEFINITION INSTANCE_TYPE
      NEXT_SYMBOL NEXT_FUNCTION NEXT_TYPE KEY_REACHED VALUE_REACHED CHANGED POSITION_LOAD KEY_LOAD VALUE_LOAD NONNULL REST)
      as (checks &suffix &selected &memory &current &REST_EVENTS &SAME_FILES &SAME_DATA &CHECKS &GOOD &SAVED_CURSOR &SUFFIX).
    assert (SMALL : (length suffix < amount)%nat).
    { rewrite SIZE, EVENTS, REST_EVENTS, !length_app; lia. }
    destruct (H (length suffix) SMALL suffix selected memory current following_cursor eq_refl
      ltac:(rewrite SAME_FILES; exact FILES) ltac:(rewrite SAME_DATA; exact DATA) GOOD SAVED_CURSOR NONNULL SUFFIX)
      as (to_copy &final_suffix &copy_parameters &copy_memory &copy_world &SUFFIX_EVENTS &TO_COPY &COPY_READY &FINAL_SUFFIX).
    exists (operation ++ checks ++ to_copy), final_suffix, copy_parameters, copy_memory, copy_world.
    split; [rewrite EVENTS, REST_EVENTS, SUFFIX_EVENTS; repeat rewrite app_assoc; reflexivity |split].
    + eapply gateway_steps_append; [exact (gateway_plug_steps backend ge _ _ _
        (gateway_validation_next_cont environment parameters) I OPERATION) |].
      eapply gateway_steps_append; [exact CHECKS |exact TO_COPY].
    + exact (conj COPY_READY FINAL_SUFFIX).
Qed.
End ValidationFilesLoop.
