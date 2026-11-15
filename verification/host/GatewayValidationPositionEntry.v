(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Files iteration starts with its actual source store of cursor zero. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine StoreSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue
  GatewayObjectThreads GatewayObjectDiscipline GatewayOutcomeValidationContext GatewayBuiltinValidation
  GatewayValidationSlots GatewayOutcomeFilesSource GatewayOutcomeLookupSource GatewaySourceSegments GatewaySourcePaths GatewaySourceCuts
  GatewayThreadRuntime GatewayStreamInterface GatewayLocalRuntime GatewayReferenceThreads GatewayFramedRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Section ValidationPositionEntry.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (python : World -> python_world) (objects : World -> gateway_object_heap)
    (decimal_float : list Z -> Floats.float -> Prop) (detached : val -> mem -> World -> Prop)
    (io : Event -> option gateway_native_io) (stable : World -> block -> Z -> Prop)
    (thread_errno : World -> int) (heap_allocation : block -> Z -> Prop)
    (threads : gateway_thread_runtime backend io (fun current object => gateway_native_private (python current) object) stable
      (gateway_python_discipline python objects detached) thread_errno)
    (references : gateway_reference_thread_contract backend (fun current object => gateway_native_private (python current) object) stable
      (gateway_python_discipline python objects detached) heap_allocation python objects).
Context (ledger : GatewayReferenceLedger.gateway_reference_ledger) (held : list gateway_held_value) (reserved : list val)
    (captured : gateway_object_heap) (original : val) (protected : block -> Z -> Prop) (source : mem) (environment : env).
Let base := gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source environment.

Theorem gateway_actual_validation_position_entry parameters before world events returned after next files files_offset position key value symbol definition :
  gateway_object_reachable captured original (Vptr files files_offset) ->
  environment ! _position = Some (position, tlong) -> environment ! _key = Some (key, tptr (Tstruct __object noattr)) ->
  environment ! _value__1 = Some (value, tptr (Tstruct __object noattr)) -> environment ! _PyDict_Next = None ->
  Genv.find_symbol ge _PyDict_Next = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr); tptr tlong;
    tptr (tptr (Tstruct __object noattr)); tptr (tptr (Tstruct __object noattr))] tint cc_default ->
  base before world ->
  gateway_steps backend ge
    (gateway_live (Returnstate (Vptr files files_offset) (gateway_outcome_files_lookup_cont environment parameters) before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix selected memory current,
    events = prefix ++ suffix /\ selected ! _files = Some (Vptr files files_offset) /\ selected ! _data = parameters ! _data /\
    gateway_steps backend ge
      (gateway_live (Returnstate (Vptr files files_offset) (gateway_outcome_files_lookup_cont environment parameters) before) world) prefix
      (gateway_live (Callstate definition [Vptr files files_offset; Vptr position Ptrofs.zero; Vptr key Ptrofs.zero; Vptr value Ptrofs.zero]
        (gateway_validation_next_cont environment selected) memory) current) /\
    base memory current /\ Mem.load Mint64 memory position 0 = Some (Vlong Int64.zero) /\
    gateway_steps backend ge
      (gateway_live (Callstate definition [Vptr files files_offset; Vptr position Ptrofs.zero; Vptr key Ptrofs.zero; Vptr value Ptrofs.zero]
        (gateway_validation_next_cont environment selected) memory) current) suffix
      (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intros REACHED POSITION KEY VALUE LOCAL SYMBOL FUNCTION TYPE BASE RUN.
  assert (CLOSED : gateway_ambient_closed backend base).
  { exact (gateway_validation_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
      threads references ledger held reserved captured original protected source environment). }
  assert (LIVE : forall memory current, base memory current -> Mem.weak_valid_pointer memory files (Ptrofs.unsigned files_offset) = true).
  { intros memory current GOOD.
    destruct (gateway_validation_reachable_builtin _ _ _ _ _ _ _ _ _ _ _ _ _ _ GOOD REACHED)
      as [ROOT [description [kind [object [offset [DESCRIPTION [KIND [SAME WEAK]]]]]]]].
    inversion SAME; subst object offset; exact WEAK. }
  pose proof (gateway_validation_files_position backend ge base environment parameters before files files_offset CLOSED LIVE) as POSITION_PATH.
  destruct (gateway_source_segment_cut backend ge _ _ _ _ POSITION_PATH before world events returned after next BASE RUN)
    as (position_prefix &position_events &position_memory &position_world &POSITION_EVENTS &POSITION_QUIET &TO_POSITION &POSITION_BASE &POSITION_REST).
  set (selected := PTree.set _files (Vptr files files_offset) (set_opttemp (Some _t'14) (Vptr files files_offset) parameters)).
  set (post := fun memory current => base memory current /\ Mem.load Mint64 memory position 0 = Some (Vlong Int64.zero)).
  assert (POST_CLOSED : gateway_ambient_closed backend post).
  { intros memory current changed following [GOOD LOAD] AMBIENT; split; [eapply CLOSED; eassumption |].
    eapply gateway_validation_saved_slot; [exact GOOD | |exact POSITION |exact LOAD].
    eapply gateway_validation_slots_ambient; [exact threads |exact GOOD |apply Mem.unchanged_on_refl |exact AMBIENT]. }
  assert (STORE_EDGE : forall memory current, base memory current -> exists changed,
    store_edge ge
      (State f_host_outcome_from gateway_validation_position_statement (Kseq gateway_validation_after_position Kstop) environment selected memory)
      (State f_host_outcome_from Sskip (Kseq gateway_validation_after_position Kstop) environment selected changed) /\ post changed current).
  { intros memory current GOOD.
    destruct (Mem.valid_access_store memory Mint64 position 0 (Vlong Int64.zero)
      (gateway_validation_slots _ _ _ _ _ _ _ _ _ _ _ _ _ GOOD _position position tlong POSITION)) as [changed STORE].
    exists changed; split; [apply gateway_validation_position_store with (position := position); assumption |split].
    - eapply gateway_validation_context_native_store;
        [exact GOOD |exact (proj2 (gateway_validation_environment _ _ _ _ _ _ _ _ _ _ _ _ _ GOOD _position position tlong POSITION)) |
         exact (gateway_validation_slots_outside _ _ _ _ _ _ _ _ _ _ _ _ _ GOOD _position position tlong POSITION) |exact STORE].
    - exact (Mem.load_store_same _ _ _ _ _ _ STORE). }
  destruct (gateway_source_edge_cut backend ge base post
    (State f_host_outcome_from gateway_validation_position_statement (Kseq gateway_validation_after_position Kstop) environment selected position_memory)
    (State f_host_outcome_from Sskip (Kseq gateway_validation_after_position Kstop) environment selected position_memory)
    position_memory position_world position_events returned after next CLOSED ltac:(cbn; tauto) STORE_EDGE POSITION_BASE POSITION_REST)
    as (pending &next_events &store_before &store_world &store_after &STORE_EVENTS &PENDING &STORE_PREFIX &STORE_BASE &EDGE &POST &FROM_STORE).
  pose proof (gateway_validation_next_source backend ge post environment selected store_after files files_offset position key value symbol definition
    POST_CLOSED ltac:(unfold selected; apply PTree.gss) POSITION KEY VALUE LOCAL SYMBOL FUNCTION TYPE) as NEXT_PATH.
  destruct (gateway_source_path_cut backend ge _ _ _ post _ post NEXT_PATH store_after store_world next_events returned after next POST FROM_STORE)
    as (next_prefix &suffix &memory &current &NEXT_EVENTS &NEXT_QUIET &TO_NEXT &[GOOD CURSOR] &REST).
  exists (position_prefix ++ pending ++ gateway_source E0 :: next_prefix), suffix, selected, memory, current.
  split; [rewrite POSITION_EVENTS, STORE_EVENTS, NEXT_EVENTS; repeat rewrite <- app_assoc; reflexivity |split].
  - unfold selected; apply PTree.gss.
  - split.
    + unfold selected, set_opttemp; repeat rewrite PTree.gso by discriminate; reflexivity.
    + split.
      * eapply gateway_steps_append; [exact TO_POSITION |].
        eapply gateway_steps_append; [exact STORE_PREFIX |].
        destruct EDGE as [INTERNAL [REAL UNIQUE]]; econstructor; [apply gateway_internal; [exact INTERNAL |exact REAL] |exact TO_NEXT].
      * exact (conj GOOD (conj CURSOR REST)).
Qed.
End ValidationPositionEntry.
