(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Actual source queries establish this same thread's main-interpreter check. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayInterpreterSource GatewayInterpreterRuntime
  GatewayInterpreterRuns GatewayInitializationContext GatewayInitializationRegions GatewayReferenceThreads GatewayReferenceHistoryThreads
  GatewayThreadRuntime GatewaySourcePaths GatewayFramedRuntime GatewayBindings.
Import ListNotations.

Theorem gateway_actual_initialization_interpreter {World Event} (backend : gateway_backend World Event)
    io native stable base thread_errno heap_allocation python objects current identifier
    (threads : gateway_thread_runtime backend io native stable base thread_errno)
    (reference_threads : gateway_reference_thread_contract backend native stable base heap_allocation python objects)
    (interpreter : gateway_interpreter_runtime backend io native stable base python objects current identifier)
    symbols snapshot active complete decimal_float ledger retired held pointer number guarded parameters
    before world events value after next :
  gateway_initialization_context native stable base symbols snapshot active complete
    python objects decimal_float ledger retired held current identifier pointer number before world ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (State (gateway_interpreter_owner guarded) (fn_body (gateway_interpreter_owner guarded))
      Kstop empty_env parameters before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value <> Vnullptr ->
  number = Int64.zero /\
  exists prefix suffix memory owner,
    events = prefix ++ suffix /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (State (gateway_interpreter_owner guarded) (fn_body (gateway_interpreter_owner guarded))
        Kstop empty_env parameters before) world) prefix
      (gateway_live (Returnstate (Vlong Int64.zero)
        (gateway_interpreter_id_cont guarded (PTree.set _t'1 pointer parameters)) memory) owner) /\
    gateway_initialization_context native stable base symbols snapshot active complete
      python objects decimal_float ledger retired held current identifier pointer number memory owner /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Returnstate (Vlong Int64.zero)
        (gateway_interpreter_id_cont guarded (PTree.set _t'1 pointer parameters)) memory) owner) suffix
      (gateway_live (Returnstate value Kstop after) next).
Proof.
  intros INPUT RUN NONNULL.
  set (property := gateway_initialization_context native stable base symbols snapshot active complete
    python objects decimal_float ledger retired held current identifier pointer number).
  assert (CLOSED : gateway_ambient_closed backend property).
  { eapply gateway_initialization_context_ambient; eassumption. }
  assert (EFFECT : forall memory owner changed following observed, property memory owner ->
    gateway_interpreter_query_post io native stable base python objects current identifier memory owner changed following observed ->
    property changed following).
  { intros; eapply gateway_initialization_context_query; eassumption. }
  destruct gateway_actual_interpreter_bindings as [[get_symbol [GET_SYMBOL GET_FUNCTION]] [id_symbol [ID_SYMBOL ID_FUNCTION]]].
  pose proof (gateway_interpreter_get_source_path backend (Clight.globalenv prog) guarded property parameters before get_symbol
    CLOSED GET_SYMBOL GET_FUNCTION) as GET_PATH.
  destruct (gateway_source_path_cut backend (Clight.globalenv prog) _ _ _ _ _ _ GET_PATH before world events value after next INPUT RUN)
    as (p0 & rest0 & get_before & get_world & EVENTS0 & QUIET0 & PREFIX0 & GET_READY & FROM_GET).
  destruct (gateway_return_cut backend (Clight.globalenv prog) gateway_interpreter_get_definition []
    (gateway_interpreter_get_cont guarded parameters) get_before get_world rest0 (Returnstate value Kstop after) next
    ltac:(destruct guarded; cbn; exact I) ltac:(destruct guarded; cbn; lia) FROM_GET)
    as (getting & rest1 & get_result & get_after & get_next & EVENTS1 & GET_RUN & AFTER_GET_RUN).
  destruct (gateway_interpreter_run_retained backend (Clight.globalenv prog) io native stable base python objects current identifier interpreter
    property true [] get_before get_world getting get_result get_after get_next CLOSED
    ltac:(intros memory owner [REGIONS REST]; split; [exact (proj1 (initialization_region_buffers _ _ _ _ _ _ _ _ _ REGIONS)) |reflexivity])
    EFFECT GET_READY GET_RUN) as [AFTER_GET GET_RECEIPT].
  destruct GET_RECEIPT as (get_pending & get_trailing & get_called & get_called_world & get_changed & get_changed_world & get_observed &
    GET_EVENTS & GET_AT & GET_OPERATION & GET_VALUE & GET_POST).
  cbn [gateway_interpreter_result] in GET_VALUE; destruct GET_VALUE as [GET_SAME [object [offset POINTER]]].
  assert (GET_POINTER : get_result = pointer).
  { destruct GET_AT as [_ [_ [SAME REST]]]; exact (eq_trans GET_SAME SAME). }
  rewrite POINTER in GET_RUN, AFTER_GET_RUN, GET_POINTER.
  subst pointer.
  set (id_parameters := PTree.set _t'1 (Vptr object offset) parameters).
  pose proof (gateway_interpreter_id_source_path backend (Clight.globalenv prog) guarded property parameters get_after object offset id_symbol
    CLOSED ID_SYMBOL ID_FUNCTION) as ID_PATH.
  destruct (gateway_source_path_cut backend (Clight.globalenv prog) _ _ _ _ _ _ ID_PATH get_after get_next rest1 value after next AFTER_GET AFTER_GET_RUN)
    as (p1 & rest2 & id_before & id_world & EVENTS2 & QUIET1 & PREFIX1 & ID_READY & FROM_ID).
  destruct (gateway_return_cut backend (Clight.globalenv prog) gateway_interpreter_id_definition [Vptr object offset]
    (gateway_interpreter_id_cont guarded id_parameters) id_before id_world rest2 (Returnstate value Kstop after) next
    ltac:(destruct guarded; cbn; exact I) ltac:(destruct guarded; cbn; lia) FROM_ID)
    as (identifying & suffix & id_result & id_after & id_next & EVENTS3 & ID_RUN & REST).
  destruct (gateway_interpreter_run_retained backend (Clight.globalenv prog) io native stable base python objects current identifier interpreter
    property false [Vptr object offset] id_before id_world identifying id_result id_after id_next CLOSED
    ltac:(intros memory owner [REGIONS [HISTORY [SAME OTHER]]]; split;
      [exact (proj1 (initialization_region_buffers _ _ _ _ _ _ _ _ _ REGIONS)) |cbn; rewrite SAME; reflexivity])
    EFFECT ID_READY ID_RUN) as [AFTER_ID ID_RECEIPT].
  destruct ID_RECEIPT as (id_pending & id_trailing & id_called & id_called_world & id_changed & id_changed_world & id_observed &
    ID_EVENTS & ID_AT & ID_OPERATION & ID_VALUE & ID_POST).
  cbn [gateway_interpreter_result] in ID_VALUE.
  assert (ID_NUMBER : id_result = Vlong number).
  { destruct ID_AT as [_ [_ [SAME NUMBER]]]; rewrite ID_VALUE, NUMBER; reflexivity. }
  rewrite ID_NUMBER in ID_RUN, REST.
  pose proof (gateway_actual_interpreter_zero backend (Clight.globalenv prog) guarded id_parameters id_after id_next suffix
    number value after next REST NONNULL) as ZERO.
  split; [exact ZERO |]. exists (p0 ++ getting ++ p1 ++ identifying), suffix, id_after, id_next.
  split.
  - rewrite EVENTS0, EVENTS1, EVENTS2, EVENTS3; repeat rewrite app_assoc; reflexivity.
  - split.
    + rewrite <- ZERO; eapply gateway_steps_append; [exact PREFIX0 |].
      eapply gateway_steps_append; [exact (gateway_plug_steps backend (Clight.globalenv prog) _ _ _
        (gateway_interpreter_get_cont guarded parameters) ltac:(destruct guarded; cbn; exact I) GET_RUN) |].
      eapply gateway_steps_append; [exact PREFIX1 |].
      exact (gateway_plug_steps backend (Clight.globalenv prog) _ _ _ (gateway_interpreter_id_cont guarded id_parameters)
        ltac:(destruct guarded; cbn; exact I) ID_RUN).
    + split; [exact AFTER_ID |rewrite <- ZERO; exact REST].
Qed.
