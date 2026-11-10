(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: The exported initializer owns the actual guarded private-body invocation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayInterpreterSource GatewayInterpreterRuntime
  GatewayInitializationInterpreter GatewayInitializationContext GatewayInitializationRegions GatewayInitializationEntrySource
  GatewayInitializationGuarded GatewayInitializationResult GatewaySourcePaths GatewayFramedRuntime GatewayBindings
  GatewayReferenceThreads GatewayReferenceHistoryThreads GatewayThreadRuntime GatewayNoLocalEntry GatewayLoaderRegions GatewayBootstrapRegions
  GatewayInitializerProtection.
Import ListNotations.

Theorem gateway_actual_initialization_body {World Event} (backend : gateway_backend World Event)
    io native stable base thread_errno heap_allocation python objects current identifier
    (threads : gateway_thread_runtime backend io native stable base thread_errno)
    (reference_threads : gateway_reference_thread_contract backend native stable base heap_allocation python objects)
    (interpreter : gateway_interpreter_runtime backend io native stable base python objects current identifier)
    symbols snapshot decimal_float ledger retired held pointer number before world events value after next :
  gateway_initialization_context native stable base symbols snapshot Int.zero Int.zero
    python objects decimal_float ledger retired held current identifier pointer number before world ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (Callstate (Internal f_PyInit__host) [] Kstop before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value <> Vnullptr ->
  number = Int64.zero /\
  exists prefix body suffix parameters called called_world returned changed changed_world,
    events = prefix ++ body ++ suffix /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Callstate (Internal f_PyInit__host) [] Kstop before) world) prefix
      (gateway_live (Callstate (Internal f_host_initialize) [] (initialization_body_cont parameters) called) called_world) /\
    gateway_initialization_context native stable base symbols snapshot Int.one Int.zero
      python objects decimal_float ledger retired held current identifier pointer number called called_world /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Callstate (Internal f_host_initialize) [] Kstop called) called_world) body
      (gateway_live (Returnstate returned Kstop changed) changed_world) /\ returned <> Vnullptr /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Returnstate returned (initialization_body_cont parameters) changed) changed_world) suffix
      (gateway_live (Returnstate value Kstop after) next).
Proof.
  intros INPUT RUN NONNULL.
  set (property := gateway_initialization_context native stable base symbols snapshot Int.zero Int.zero
    python objects decimal_float ledger retired held current identifier pointer number).
  assert (CLOSED : gateway_ambient_closed backend property).
  { eapply gateway_initialization_context_ambient; eassumption. }
  destruct (gateway_actual_no_local_entry backend (Clight.globalenv prog) f_PyInit__host [] property before world events value after next
    eq_refl CLOSED INPUT RUN) as (p0 & rest0 & entered & entry_world & parameters & EVENTS0 & PREFIX0 & READY0 & BODY).
  destruct (gateway_actual_initialization_interpreter backend io native stable base thread_errno heap_allocation python objects current identifier
    threads reference_threads interpreter symbols snapshot Int.zero Int.zero decimal_float ledger retired held pointer number true parameters
    entered entry_world rest0 value after next READY0 BODY NONNULL)
    as [MAIN (p1 & rest1 & checked & checked_world & EVENTS1 & PREFIX1 & READY1 & AFTER_CHECK)].
  destruct (gateway_actual_initialization_guarded_path backend io native stable base thread_errno heap_allocation python objects current identifier
    threads reference_threads interpreter symbols snapshot decimal_float ledger retired held pointer number (PTree.set _t'1 pointer parameters) checked)
    as [body_parameters PATH].
  destruct (gateway_source_path_cut backend (Clight.globalenv prog) _ _ _ _ _ _ PATH checked checked_world rest1 value after next READY1 AFTER_CHECK)
    as (p2 & rest2 & called & called_world & EVENTS2 & QUIET2 & PREFIX2 & CALLED & FROM_BODY).
  destruct (gateway_return_cut backend (Clight.globalenv prog) (Internal f_host_initialize) []
    (initialization_body_cont body_parameters) called called_world rest2 (Returnstate value Kstop after) next I ltac:(cbn; lia) FROM_BODY)
    as (body & suffix & returned & changed & changed_world & EVENTS3 & INNER & REST).
  pose proof (gateway_actual_initialization_body_nonnull backend (Clight.globalenv prog) body_parameters returned changed changed_world suffix
    value after next REST NONNULL) as BODY_NONNULL.
  split; [exact MAIN |]. exists (p0 ++ p1 ++ p2), body, suffix, body_parameters, called, called_world, returned, changed, changed_world.
  split; [rewrite EVENTS0, EVENTS1, EVENTS2, EVENTS3; repeat rewrite app_assoc; reflexivity |]. split.
  - eapply gateway_steps_append; [exact PREFIX0 |]. eapply gateway_steps_append; [exact PREFIX1 |exact PREFIX2].
  - split; [exact CALLED |]. split; [exact INNER |]. split; assumption.
Qed.

Theorem gateway_actual_loaded_initialization_body {World Event} (backend : gateway_backend World Event)
    io native stable base thread_errno heap_allocation python objects current identifier
    (threads : gateway_thread_runtime backend io native stable base thread_errno)
    (reference_threads : gateway_reference_thread_contract backend native stable base heap_allocation python objects)
    (interpreter : gateway_interpreter_runtime backend io native stable base python objects current identifier)
    decimal_float ledger retired held before world events value after next :
  gateway_native_loader_boundary (Clight.globalenv prog) before ->
  gateway_native_readonly_mapping (Clight.globalenv prog) before ->
  gateway_native_storage_boundary native (Clight.globalenv prog) before world -> base None before world ->
  gateway_reference_history_scope python objects decimal_float ledger retired held world ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (Callstate (Internal f_PyInit__host) [] Kstop before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value <> Vnullptr ->
  identifier world = Int64.zero /\
  exists symbols prefix body suffix parameters called called_world returned changed changed_world,
    events = prefix ++ body ++ suffix /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Callstate (Internal f_PyInit__host) [] Kstop before) world) prefix
      (gateway_live (Callstate (Internal f_host_initialize) [] (initialization_body_cont parameters) called) called_world) /\
    gateway_initialization_context native stable base symbols before Int.one Int.zero
      python objects decimal_float ledger retired held current identifier (current world) (identifier world) called called_world /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Callstate (Internal f_host_initialize) [] Kstop called) called_world) body
      (gateway_live (Returnstate returned Kstop changed) changed_world) /\ returned <> Vnullptr /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Returnstate returned (initialization_body_cont parameters) changed) changed_world) suffix
      (gateway_live (Returnstate value Kstop after) next).
Proof.
  intros LOADER READONLY STORAGE SIDE HISTORY RUN NONNULL.
  destruct (gateway_initialization_regions_loaded native stable base before world LOADER READONLY STORAGE SIDE) as [symbols REGIONS].
  destruct (gateway_actual_initialization_body backend io native stable base thread_errno heap_allocation python objects current identifier
    threads reference_threads interpreter symbols before decimal_float ledger retired held (current world) (identifier world) before world events value after next
    (conj REGIONS (conj HISTORY (conj eq_refl eq_refl))) RUN NONNULL) as [MAIN RECEIPT].
  split; [exact MAIN |]. exists symbols; exact RECEIPT.
Qed.
