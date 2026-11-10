(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Real module ownership justifies the success branch and both source flag stores. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers Floats AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayInitializationSource
  GatewayInitializationRegions GatewayInitializationStores GatewayInitializationContext GatewayInitializationGuarded
  GatewayInitializationEntrySource GatewayInitializationCompletionSource GatewayBootstrapReferenceScope GatewayBootstrapRegions
  GatewayReferenceAccounting GatewayReferenceHistory GatewayReferenceHistoryThreads GatewayReferenceThreads GatewayReferenceLedger GatewayReferenceAbandon
  GatewayPython GatewayObjects GatewayObjectThreads GatewayInterpreterRuntime GatewayThreadRuntime GatewaySourceSegments GatewayFramedRuntime GatewayReturnScope.
Import ListNotations.
Open Scope Z_scope.

Section Completion.
Context {World Event} (backend : gateway_backend World Event) io native stable base thread_errno heap_allocation
  python objects current identifier
  (threads : gateway_thread_runtime backend io native stable base thread_errno)
  (reference_threads : gateway_reference_thread_contract backend native stable base heap_allocation python objects)
  (interpreter : gateway_interpreter_runtime backend io native stable base python objects current identifier)
  (profile : gateway_bootstrap_python_profile native base python objects)
  (symbols : gateway_initialization_symbols) (snapshot : mem)
  (decimal_float : list Z -> Floats.float -> Prop) (ledger : gateway_reference_ledger)
  (retired : list gateway_abandoned_reference) (held : list gateway_held_value)
  (pointer : Values.val) (number : int64) (owner : gateway_reference_place) (ticket : nat)
  (object : block) (offset : ptrofs).
Let context active complete := gateway_initialization_context native stable base symbols snapshot active complete
  python objects decimal_float ledger retired held current identifier pointer number.

Local Lemma completion_closed active complete : gateway_ambient_closed backend (context active complete).
Proof. eapply gateway_initialization_context_ambient; eassumption. Qed.

Theorem gateway_initialization_owned_module_live memory world active complete :
  gateway_reference_owns ledger owner ticket (Vptr object offset) -> context active complete memory world ->
  Mem.weak_valid_pointer memory object (Ptrofs.unsigned offset) = true.
Proof.
  intros OWNED [REGIONS [HISTORY REST]].
  pose proof (proj1 (initialization_region_buffers _ _ _ _ _ _ _ _ _ REGIONS)) as SIDE.
  pose proof (gateway_bootstrap_profile_ready _ _ _ _ profile memory world SIDE) as READY.
  assert (ROOT : gateway_rooted (python world) (objects world) (Vptr object offset)).
  { eapply gateway_reference_owned_rooted; [exact (proj1 (proj2 HISTORY)) |exact OWNED]. }
  destruct READY as [[_ [_ [_ [_ ADDRESSES]]]] _].
  destruct (ADDRESSES _ ROOT) as (actual & position & SAME & LIVE); inversion SAME; subst; exact LIVE.
Qed.

Theorem gateway_initialization_completion_script parameters memory :
  gateway_reference_owns ledger owner ticket (Vptr object offset) ->
  gateway_source_segment backend (Clight.globalenv prog) (context Int.one Int.zero)
      (Returnstate (Vptr object offset) (initialization_body_cont parameters) memory)
      (Returnstate (Vptr object offset) Kstop memory) (context Int.zero Int.one).
Proof.
  intros OWNED.
  destruct (gateway_initialization_success_frontier backend (Clight.globalenv prog) (context Int.one Int.zero)
    parameters object offset memory (completion_closed _ _)
    ltac:(intros changed world READY; eapply gateway_initialization_owned_module_live; [exact OWNED |exact READY]))
    as (changed_parameters & FRONTIER & RESULT).
  eapply initialization_completion_segment_compose; [exact FRONTIER |].
  eapply gateway_segment_next with
    (next := State f_PyInit__host Sskip (Kseq initialization_after_success Kstop) empty_env changed_parameters memory)
    (middle := context Int.one Int.one).
  - apply completion_closed.
  - cbn; tauto.
  - intros before world READY.
    pose proof (initialization_region_complete_capacity _ _ _ _ _ _ _ _ _ (proj1 READY)) as CAPACITY.
    destruct (Mem.valid_access_store before Mint32 (initialization_complete symbols) 0 (Vint Int.one)
      (gateway_initialization_word_access native before world _ CAPACITY)) as [after STORE].
    exists after; split.
    + apply initialization_global_store with (object := initialization_complete symbols);
        [exact (initialization_complete_symbol symbols) |exact STORE].
    + exact (gateway_initialization_context_store backend io native stable base thread_errno threads symbols snapshot Int.one Int.zero
        python objects decimal_float ledger retired held current identifier pointer number true Int.one before world after READY STORE).
  - eapply initialization_completion_segment_compose;
      [apply gateway_initialization_success_to_clear; apply completion_closed |].
    eapply gateway_segment_next with
      (next := State f_PyInit__host Sskip (Kseq initialization_return Kstop) empty_env changed_parameters memory)
      (middle := context Int.zero Int.one).
    + apply completion_closed.
    + cbn; tauto.
    + intros before world READY.
      pose proof (initialization_region_active_capacity _ _ _ _ _ _ _ _ _ (proj1 READY)) as CAPACITY.
      destruct (Mem.valid_access_store before Mint32 (initialization_active symbols) 0 (Vint Int.zero)
        (gateway_initialization_word_access native before world _ CAPACITY)) as [after STORE].
      exists after; split.
      * apply initialization_global_store with (object := initialization_active symbols);
          [exact (initialization_active_symbol symbols) |exact STORE].
      * exact (gateway_initialization_context_store backend io native stable base thread_errno threads symbols snapshot Int.one Int.one
          python objects decimal_float ledger retired held current identifier pointer number false Int.zero before world after READY STORE).
    + apply gateway_initialization_success_return; [apply completion_closed |exact RESULT].
Qed.

Theorem gateway_actual_initialization_completed parameters before world events value after next :
  gateway_reference_owns ledger owner ticket (Vptr object offset) -> context Int.one Int.zero before world ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (Returnstate (Vptr object offset) (initialization_body_cont parameters) before) world) events
    (gateway_live (Returnstate value Kstop after) next) ->
  value = Vptr object offset /\ context Int.zero Int.one after next.
Proof.
  intros OWNED INPUT RUN.
  pose proof (gateway_initialization_completion_script parameters before OWNED) as SCRIPT.
  destruct (gateway_source_segment_cut backend (Clight.globalenv prog) _ _ _ _ SCRIPT before world events value after next INPUT RUN)
    as (prefix & suffix & memory & owner_world & EVENTS & QUIET & PREFIX & READY & SUFFIX).
  exact (gateway_terminal_return_scope backend (Clight.globalenv prog) (context Int.zero Int.one) (Vptr object offset)
    (completion_closed _ _) memory owner_world suffix value after next READY SUFFIX).
Qed.
End Completion.
