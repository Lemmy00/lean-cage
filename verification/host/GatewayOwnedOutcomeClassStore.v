(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Same-run class publication archives overwritten
  owners. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import ClightSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayModuleSource
  GatewayFramedRuntime GatewayCalls GatewayInstructions GatewayInitializerGlobalStores GatewayInitializerOwnedStores
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceHistory GatewayReferenceAbandon
  GatewayReferenceGlobalStore GatewayHistorySourceCuts.
Import ListNotations.

Theorem gateway_actual_owned_outcome_class_store {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (python:World->python_world)(objects:World->gateway_object_heap)(property:mem->World->Prop)
    before world parameters continuation object offset symbol events value after next position ledger retired ticket:
  gateway_ambient_closed backend property ->property before world ->
  (forall memory current,property memory current->gateway_objects_ready(python current)(objects current)memory /\
    gateway_native_private(python current)symbol /\gateway_history_counts_fit ledger retired(python current)) ->
  Genv.find_symbol ge _host_outcome_class=Some symbol ->
  gateway_history_well_formed position ledger retired ->
  gateway_reference_owns ledger(gateway_reference_result(S(gateway_reference_depth continuation)))ticket(Vptr object offset) ->
  gateway_reference_take(gateway_reference_temporary(gateway_reference_depth continuation)_t'11)
    (gateway_reference_entries ledger)=None ->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vptr object offset)(module_outcome_cont parameters continuation)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->
  exists prefix suffix memory current changed final archived,
    events=prefix++suffix /\
    gateway_history_execution backend ge gateway_history_global_store_select position
      (gateway_live(Returnstate(Vptr object offset)(module_outcome_cont parameters continuation)before)world)
      {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|}prefix
      (gateway_live(State f_host_initialize Sskip(Kseq module_outcome_rest continuation)empty_env
        (PTree.set _t'11(Vptr object offset)parameters)changed)current)
      {|gateway_history_active:=gateway_reference_valid final;gateway_history_abandoned:=archived|} /\
    gateway_history_well_formed(position+length prefix)final archived /\
    gateway_history_counts_fit final archived(python current) /\
    gateway_reference_owns final(gateway_reference_global _host_outcome_class)ticket(Vptr object offset) /\
    Mem.store Mptr memory symbol 0(Vptr object offset)=Some changed /\Mem.load Mptr changed symbol 0=Some(Vptr object offset) /\
    gateway_objects_ready(python current)(objects current)changed /\
    gateway_reference_place_value ge
      (State f_host_initialize Sskip(Kseq module_outcome_rest continuation)empty_env
        (PTree.set _t'11(Vptr object offset)parameters)changed)
      (gateway_reference_global _host_outcome_class)(Vptr object offset) /\
    (forall pointer,gateway_history_total_count final archived pointer=gateway_history_total_count ledger retired pointer) /\
    gateway_steps backend ge
      (gateway_live(State f_host_initialize Sskip(Kseq module_outcome_rest continuation)empty_env
        (PTree.set _t'11(Vptr object offset)parameters)changed)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros CLOSED INITIAL PROPERTY SYMBOL WELL OWNED VACANT RUN.
  destruct(gateway_actual_history_return_capture backend ge property f_host_initialize _t'11 empty_env parameters
    (Kseq module_outcome_store(Kseq module_outcome_rest continuation))object offset before world events value after next
    position ledger retired ticket CLOSED INITIAL WELL OWNED VACANT RUN)
    as(temporary &captured &rest &first &first_world &EVENTS &FIRST &CAPTURED &TEMPORARY_WELL &TEMPORARY_OWNER &TEMPORARY_COUNTS &REST).
  destruct(gateway_actual_history_skip_sequence backend ge property f_host_initialize module_outcome_store
    (Kseq module_outcome_rest continuation)empty_env(PTree.set _t'11(Vptr object offset)parameters)
    first first_world rest value after next(position+length captured)temporary retired CLOSED FIRST TEMPORARY_WELL REST)
    as(skipped &later &second &second_world &REST_EVENTS &SECOND &SKIPPED &BEFORE_WAIT &LATER).
  destruct(gateway_source_instruction_occurrence backend ge f_host_initialize module_outcome_store
    (Kseq module_outcome_rest continuation)empty_env(PTree.set _t'11(Vptr object offset)parameters)
    second second_world later value after next ltac:(cbn;tauto)LATER)
    as(waiting &suffix &memory &current &trace &target &LATER_EVENTS &AMBIENT &WAITING &STEP &SUFFIX).
  assert(GOOD:property memory current).
  { eapply(gateway_ambient_run_ready backend ge property CLOSED
      (State f_host_initialize module_outcome_store(Kseq module_outcome_rest continuation)empty_env
        (PTree.set _t'11(Vptr object offset)parameters)second)
      second second_world waiting memory current);[exact SECOND|exact AMBIENT|exact WAITING]. }
  destruct(PROPERTY memory current GOOD)as(READY &PRIVATE &FIT).
  destruct(gateway_initializer_pointer_store ge _host_outcome_class _t'11 symbol(Vptr object offset)
    (PTree.set _t'11(Vptr object offset)parameters)memory(Kseq module_outcome_rest continuation)trace target
    SYMBOL(PTree.gss _ _ _)STEP)as(changed &TRACE &TARGET &STORE);subst trace target.
  assert(WAIT_WELL:gateway_history_well_formed(position+length captured+length skipped+length waiting)temporary retired).
  { eapply(gateway_history_well_formed_advance(position+length captured+length skipped)
      (position+length captured+length skipped+length waiting)temporary retired);[lia|exact BEFORE_WAIT]. }
  assert(SOURCE:gateway_step backend ge
    (gateway_live(State f_host_initialize module_outcome_store(Kseq module_outcome_rest continuation)empty_env
      (PTree.set _t'11(Vptr object offset)parameters)memory)current)(gateway_source E0)
    (gateway_live(State f_host_initialize Sskip(Kseq module_outcome_rest continuation)empty_env
      (PTree.set _t'11(Vptr object offset)parameters)changed)current)).
  { apply gateway_internal;[exact I|exact STEP]. }
  destruct(gateway_history_actual_owned_global_store backend ge f_host_initialize _host_outcome_class _t'11
    (tptr(Tstruct __object noattr))(Kseq module_outcome_rest continuation)empty_env
    (PTree.set _t'11(Vptr object offset)parameters)object offset memory changed current
    (position+length captured+length skipped+length waiting)temporary retired ticket
    (PTree.gss _ _ _)WAIT_WELL TEMPORARY_OWNER SOURCE)
    as(final &archived &STORED &FINAL_WELL &FINAL_OWNER &FINAL_COUNTS).
  set(prefix:=captured++skipped++waiting++[gateway_source E0]).
  exists prefix,suffix,memory,current,changed,final,archived.
  split;[unfold prefix;rewrite EVENTS,REST_EVENTS,LATER_EVENTS;repeat rewrite<-app_assoc;reflexivity|]. split.
  - unfold prefix;eapply gateway_history_execution_append;[exact CAPTURED|].
    eapply gateway_history_execution_append;[exact SKIPPED|].
    replace(position+length(captured++skipped))%nat with(position+length captured+length skipped)%nat
      by(rewrite length_app;lia).
    eapply gateway_history_execution_append with(prefix:=waiting);
      [eapply gateway_history_ambient_execution;[exact WAITING|exact AMBIENT]|exact STORED].
  - split.
    + unfold prefix;repeat rewrite length_app;cbn;replace(position+(length captured+(length skipped+(length waiting+1))))%nat
        with(S(position+length captured+length skipped+length waiting))by lia;exact FINAL_WELL.
    + split.
      * intro pointer;rewrite FINAL_COUNTS,TEMPORARY_COUNTS;exact(FIT pointer).
      * split;[exact FINAL_OWNER|]. split;[exact STORE|].
        assert(LOAD:Mem.load Mptr changed symbol 0=Some(Vptr object offset))by(exact(Mem.load_store_same _ _ _ _ _ _ STORE)).
        split;[exact LOAD|]. split;[eapply gateway_owned_native_store_ready;eassumption|]. split.
        -- eapply gateway_reference_global_binding;eassumption.
        -- split;[intro pointer;rewrite FINAL_COUNTS,TEMPORARY_COUNTS;reflexivity|exact SUFFIX].
Qed.
