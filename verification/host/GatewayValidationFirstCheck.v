(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real first type check produces the dictionary required by later validation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue
  GatewayObjectThreads GatewayObjectDiscipline GatewayOutcomeValidationContext GatewayValidationGraphFacts GatewayValidationFieldLayouts
  GatewayValidationCheckCut GatewayObjectInstances GatewayOutcomeEntry GatewayOutcomeValidationSource GatewayOutcomeValidationProgress
  GatewayOutcomeValidationPaths GatewaySourcePaths GatewaySourceSegments GatewayContexts GatewayFramedRuntime
  GatewayThreadRuntime GatewayStreamInterface GatewayLocalRuntime GatewayReferenceThreads.
Import ListNotations.
Local Close Scope lean_scope.

Section ValidationFirstCheck.
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
    (captured : gateway_object_heap) (data : block) (data_offset : ptrofs) (protected : block -> Z -> Prop) (source : mem) (environment : env).
Let original := Vptr data data_offset.
Let base := gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment.

Theorem gateway_actual_validation_first_check parameters before world events returned after next type_symbol dictionary none instance_symbol instance_definition :
  parameters ! _data = Some original -> environment ! _host_has_type = None -> environment ! _PyDict_Type = None ->
  Genv.find_symbol ge _host_has_type = Some type_symbol -> Genv.find_funct_ptr ge type_symbol = Some (Internal f_host_has_type) ->
  Genv.find_symbol ge _PyDict_Type = Some dictionary -> Genv.find_symbol ge __Py_NoneStruct = Some none ->
  Genv.find_symbol ge _PyObject_IsInstance = Some instance_symbol -> Genv.find_funct_ptr ge instance_symbol = Some instance_definition ->
  gateway_object_api_definition gateway_api_is_instance = Some instance_definition ->
  type_of_fundef instance_definition = Tfunction [tptr (Tstruct __object noattr); tptr (Tstruct __object noattr)] tint cc_default ->
  base before world -> returned <> Vnullptr ->
  gateway_steps backend ge
    (gateway_live (State f_host_outcome_from (fn_body f_host_outcome_from) Kstop environment parameters before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists fields prefix suffix selected memory current,
    gateway_object_values captured original = Some (gateway_dict_object fields) /\ events = prefix ++ suffix /\
    selected ! _valid = Some (Vint Int.one) /\ selected ! _index = Some (Vint Int.zero) /\ selected ! _data = parameters ! _data /\
    gateway_steps backend ge
      (gateway_live (State f_host_outcome_from (fn_body f_host_outcome_from) Kstop environment parameters before) world) prefix
      (gateway_live (State f_host_outcome_from gateway_outcome_validation_loop_body gateway_validation_iteration_cont environment selected memory) current) /\
    base memory current /\
    gateway_steps backend ge
      (gateway_live (State f_host_outcome_from gateway_outcome_validation_loop_body gateway_validation_iteration_cont environment selected memory) current) suffix
      (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intros DATA LOCAL TYPE_LOCAL TYPE_SYMBOL TYPE_FUNCTION DICTIONARY NONE INSTANCE_SYMBOL INSTANCE_FUNCTION INSTANCE_DEFINITION INSTANCE_TYPE BASE NONNULL RUN.
  assert (CLOSED : gateway_ambient_closed backend base).
  { exact (gateway_validation_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
      threads references ledger held reserved captured original protected source environment). }
  destruct (gateway_validation_captured_builtin _ _ _ _ _ _ _ _ _ _ _ _ _ _ BASE ltac:(constructor))
    as (description &kind &object &offset &DESCRIPTION &KIND &SAME); inversion SAME; subst object offset.
  pose proof (gateway_outcome_first_type_source backend ge base environment parameters original before type_symbol dictionary
    CLOSED DATA ltac:(right; eauto) LOCAL TYPE_LOCAL TYPE_SYMBOL TYPE_FUNCTION DICTIONARY) as FIRST_PATH.
  destruct (gateway_source_path_cut backend ge _ _ _ base _ base FIRST_PATH before world events returned after next BASE RUN)
    as (first_prefix &first_rest &first_memory &first_world &FIRST_EVENTS &FIRST_QUIET &TO_FIRST &FIRST_BASE &FIRST_REST).
  destruct (gateway_actual_positive_validation_call backend ge python objects decimal_float detached io stable thread_errno heap_allocation leases
    threads references instances ledger held reserved captured original protected source environment (fun _ _ => True)
    ltac:(auto) ltac:(auto) data data_offset description kind gateway_dict_kind dictionary Ptrofs.zero none Int.zero
    (gateway_outcome_first_type_cont environment parameters) first_memory first_world first_rest returned after next instance_symbol instance_definition
    I ltac:(cbn [gateway_outcome_first_type_cont gateway_cont_weight]; lia) FIRST_BASE I ltac:(constructor) DESCRIPTION KIND
    (gateway_builtin_dictionary_type ge dictionary DICTIONARY) (or_introl eq_refl) NONE
    INSTANCE_SYMBOL INSTANCE_FUNCTION INSTANCE_DEFINITION INSTANCE_TYPE
    ltac:(intros; apply gateway_outcome_first_nonpositive_null; assumption) NONNULL FIRST_REST)
    as (first_operation &loop_events &after_first &after_first_world &FIRST_REST_EVENTS &FIRST_OPERATION &AFTER_FIRST &EXTRA &ACCEPT &FROM_FIRST).
  assert (ACCEPTED : gateway_builtin_accepts gateway_dict_kind kind = true).
  { destruct ACCEPT as [[IMPOSSIBLE EQUAL] |GOOD]; [discriminate IMPOSSIBLE |exact GOOD]. }
  destruct (gateway_validation_dictionary_layout description kind KIND ACCEPTED) as [fields SHAPE]; subst description.
  pose proof (gateway_validation_first_loop backend ge base environment parameters after_first Int.one CLOSED) as FIRST_LOOP_PATH.
  destruct (gateway_source_segment_cut backend ge _ _ _ _ FIRST_LOOP_PATH after_first after_first_world loop_events returned after next AFTER_FIRST FROM_FIRST)
    as (loop_prefix &entry_events &loop_memory &loop_world &LOOP_EVENTS &LOOP_QUIET &TO_LOOP &LOOP_BASE &FROM_LOOP).
  set (selected := gateway_validation_after_first parameters Int.one).
  pose proof (gateway_validation_loop_entry backend ge base environment selected loop_memory CLOSED) as LOOP_ENTRY_PATH.
  destruct (gateway_source_segment_cut backend ge _ _ _ _ LOOP_ENTRY_PATH loop_memory loop_world entry_events returned after next LOOP_BASE FROM_LOOP)
    as (entry_prefix &suffix &memory &current &ENTRY_EVENTS &ENTRY_QUIET &TO_ENTRY &GOOD &REST).
  exists fields, (first_prefix ++ first_operation ++ loop_prefix ++ entry_prefix), suffix, selected, memory, current.
  split; [exact DESCRIPTION |split].
  - rewrite FIRST_EVENTS, FIRST_REST_EVENTS, LOOP_EVENTS, ENTRY_EVENTS; repeat rewrite app_assoc; reflexivity.
  - split.
    + unfold selected, gateway_validation_after_first; rewrite PTree.gso by discriminate; apply PTree.gss.
    + split; [unfold selected, gateway_validation_after_first; apply PTree.gss |split].
      * unfold selected, gateway_validation_after_first, set_opttemp; repeat rewrite PTree.gso by discriminate; reflexivity.
      * split.
        -- eapply gateway_steps_append; [exact TO_FIRST |].
           eapply gateway_steps_append; [exact (gateway_plug_steps backend ge _ _ _ (gateway_outcome_first_type_cont environment parameters) I FIRST_OPERATION) |].
           eapply gateway_steps_append; [exact TO_LOOP |exact TO_ENTRY].
        -- exact (conj GOOD REST).
Qed.
End ValidationFirstCheck.
