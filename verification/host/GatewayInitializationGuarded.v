(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: The public wrapper proves its active guard before entering the private body. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayInterpreterSource GatewayInterpreterRuntime
  GatewayInitializationContext GatewayInitializationRegions GatewayInitializationStores GatewayInitializationEntrySource
  GatewayInitializationSource GatewayReferenceThreads GatewayThreadRuntime GatewaySourcePaths GatewaySourceSegments GatewayFramedRuntime
  GatewayBootstrapCapacities GatewayBindings.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_initialization_word_access {World} native memory (world : World) object :
  gateway_bootstrap_capacity native memory world object Ptrofs.zero 4 Writable ->
  Mem.valid_access memory Mint32 object 0 Writable.
Proof.
  intros [PRIVATE [POSITIVE [COUNT [WIDTH [LIVE RANGE]]]]]; split.
  - change (Mem.range_perm memory object 0 4 Cur Writable).
    change (Mem.range_perm memory object 0 4 Cur Writable) in RANGE; exact RANGE.
  - change (4 | 0); apply Z.divide_0_r.
Qed.

Theorem gateway_actual_initialization_guarded_path {World Event} (backend : gateway_backend World Event)
    io native stable base thread_errno heap_allocation python objects current identifier
    (threads : gateway_thread_runtime backend io native stable base thread_errno)
    (reference_threads : gateway_reference_thread_contract backend native stable base heap_allocation python objects)
    (interpreter : gateway_interpreter_runtime backend io native stable base python objects current identifier)
    symbols snapshot decimal_float ledger retired held pointer number parameters memory :
  exists called_parameters,
    gateway_source_path backend (Clight.globalenv prog) (Internal f_host_initialize) [] (initialization_body_cont called_parameters)
      (gateway_initialization_context native stable base symbols snapshot Int.zero Int.zero
        python objects decimal_float ledger retired held current identifier pointer number)
      (Returnstate (Vlong Int64.zero) (gateway_interpreter_id_cont true parameters) memory)
      (gateway_initialization_context native stable base symbols snapshot Int.one Int.zero
        python objects decimal_float ledger retired held current identifier pointer number).
Proof.
  set (before_property := gateway_initialization_context native stable base symbols snapshot Int.zero Int.zero
    python objects decimal_float ledger retired held current identifier pointer number).
  set (after_property := gateway_initialization_context native stable base symbols snapshot Int.one Int.zero
    python objects decimal_float ledger retired held current identifier pointer number).
  assert (BEFORE_CLOSED : gateway_ambient_closed backend before_property).
  { eapply gateway_initialization_context_ambient; eassumption. }
  assert (AFTER_CLOSED : gateway_ambient_closed backend after_property).
  { eapply gateway_initialization_context_ambient; eassumption. }
  destruct (gateway_initialization_to_enter backend (Clight.globalenv prog) before_property parameters memory
    (initialization_active symbols) (initialization_complete symbols) BEFORE_CLOSED
    (initialization_active_symbol symbols) (initialization_complete_symbol symbols)
    ltac:(intros candidate owner [REGIONS REST]; exact (initialization_region_active_value _ _ _ _ _ _ _ _ _ REGIONS))
    ltac:(intros candidate owner [REGIONS REST]; exact (initialization_region_complete_value _ _ _ _ _ _ _ _ _ REGIONS)))
    as [called_parameters PREFIX].
  assert (BINDING : gateway_function_binding (Clight.globalenv prog) _host_initialize (Internal f_host_initialize))
    by (apply gateway_actual_function_binding; vm_compute; reflexivity).
  destruct BINDING as [symbol [SYMBOL FUNCTION]].
  exists called_parameters; eapply gateway_segment_then_call; [exact PREFIX |].
  eapply gateway_source_next with (target := State f_PyInit__host Sskip (Kseq initialization_after_enter Kstop)
    empty_env called_parameters memory) (middle := after_property).
  - exact BEFORE_CLOSED.
  - cbn; tauto.
  - intros before world READY.
    pose proof (initialization_region_active_capacity _ _ _ _ _ _ _ _ _ (proj1 READY)) as CAPACITY.
    destruct (Mem.valid_access_store before Mint32 (initialization_active symbols) 0 (Vint Int.one)
      (gateway_initialization_word_access native before world _ CAPACITY)) as [after STORE].
    exists after; split.
    + apply initialization_global_store with (object := initialization_active symbols);
        [exact (initialization_active_symbol symbols) |exact STORE].
    + exact (gateway_initialization_context_store backend io native stable base thread_errno threads symbols snapshot Int.zero Int.zero
        python objects decimal_float ledger retired held current identifier pointer number false Int.one before world after READY STORE).
  - apply gateway_initialization_after_enter_path with (symbol := symbol); assumption.
Qed.
