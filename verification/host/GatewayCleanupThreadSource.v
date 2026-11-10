(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Source cleanup saves its thread before reaping the same stored
   child. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayMemoryPrefixes GatewayFramedRuntime
  GatewayRuntimeABI GatewayExchangeTransport GatewayCleanupSource.
Import ListNotations.
Open Scope Z_scope.

Definition cleanup_save_body:=exchange_cleanup_statement 2.
Definition cleanup_save_call:=match cleanup_save_body with Ssequence first _=>first|_=>Sskip end.
Definition cleanup_save_bind:=match cleanup_save_body with Ssequence _ rest=>rest|_=>Sskip end.
Definition cleanup_save_after:=Kseq cleanup_save_bind(Kseq(exchange_cleanup_after 3)Kstop).
Definition cleanup_save_cont environment temporaries:=Kcall(Some _t'53)f_host_exchange environment temporaries cleanup_save_after.
Definition cleanup_reap_body:=exchange_cleanup_statement 3.
Definition cleanup_reap_load:=match cleanup_reap_body with Ssequence first _=>first|_=>Sskip end.
Definition cleanup_reap_call:=match cleanup_reap_body with Ssequence _ rest=>rest|_=>Sskip end.
Definition cleanup_reap_after:=Kseq(exchange_cleanup_after 4)Kstop.
Definition cleanup_reap_cont environment temporaries:=Kcall None f_host_exchange environment temporaries cleanup_reap_after.
Definition cleanup_save_temps(saved:val)(temporaries:temp_env):=PTree.set _t'53 saved temporaries.
Definition cleanup_saved_temps(saved:val)(temporaries:temp_env):=PTree.set _saved saved(cleanup_save_temps saved temporaries).
Definition cleanup_reap_temps child saved temporaries:=PTree.set _t'55(Vint child)(cleanup_saved_temps saved temporaries).

Theorem actual_cleanup_save_call ge environment temporaries memory:
  environment!_PyEval_SaveThread=None->gateway_function_binding ge _PyEval_SaveThread gateway_save_thread_definition->
  store_edge ge(State f_host_exchange cleanup_save_call cleanup_save_after environment temporaries memory)
    (Callstate gateway_save_thread_definition[](cleanup_save_cont environment temporaries)memory).
Proof.
  intros LOCAL[symbol[SYMBOL FUNCTION]];eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero);
    [reflexivity|apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity]|
      apply no_argument_values|cbn;exact FUNCTION|reflexivity].
Qed.

Theorem actual_cleanup_save_prefix {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries memory:
  environment!_PyEval_SaveThread=None->gateway_function_binding ge _PyEval_SaveThread gateway_save_thread_definition->
  gateway_memory_prefix backend ge
    (Callstate gateway_save_thread_definition[](cleanup_save_cont environment temporaries)memory)property property
    (State f_host_exchange(exchange_cleanup_after 2)Kstop environment temporaries memory).
Proof.
  intros LOCAL FUNCTION.
  eapply gateway_memory_same with(following:=State f_host_exchange cleanup_save_body
    (Kseq(exchange_cleanup_after 3)Kstop)environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange cleanup_save_call cleanup_save_after environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=Callstate gateway_save_thread_definition[](cleanup_save_cont environment temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply actual_cleanup_save_call;assumption|apply gateway_memory_identity].
Qed.

Theorem actual_cleanup_reap_call ge environment temporaries memory child object offset:
  environment!_host_engine_reap=None->gateway_function_binding ge _host_engine_reap(Internal f_host_engine_reap)->
  temporaries!_t'55=Some(Vint child)->temporaries!_result=Some(Vptr object offset)->
  Mem.weak_valid_pointer memory object(Ptrofs.unsigned offset)=true->
  store_edge ge(State f_host_exchange cleanup_reap_call cleanup_reap_after environment temporaries memory)
    (Callstate(Internal f_host_engine_reap)[Vint child;Vint Int.one](cleanup_reap_cont environment temporaries)memory).
Proof.
  intros LOCAL[symbol[SYMBOL FUNCTION]]CHILD RESULT POINTER.
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vint child).
    + apply old_expression_value,value_temp;exact CHILD.
    + reflexivity.
    + eapply cons_argument_values with(v:=Vint Int.one).
      * apply binary_expression_value with(v:=Vptr object offset)(w:=Vnullptr).
        -- apply old_expression_value,value_temp;exact RESULT.
        -- apply cast_expression_value with(v:=Vint Int.zero);[apply old_expression_value;constructor|reflexivity].
        -- unfold Cop.sem_binary_operation,Cop.sem_cmp,Cop.classify_cmp,Cop.cmp_ptr.
           cbn[typeof Vnullptr Archi.ptr64 Val.cmplu_bool].
           fold(Mem.weak_valid_pointer memory object(Ptrofs.unsigned offset));rewrite POINTER;reflexivity.
      * reflexivity.
      * apply no_argument_values.
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_cleanup_saved_reap_prefix {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries memory child_cell child saved_block saved_offset object offset:
  environment!_child=Some(child_cell,tint)->environment!_host_engine_reap=None->
  gateway_function_binding ge _host_engine_reap(Internal f_host_engine_reap)->
  temporaries!_result=Some(Vptr object offset)->
  (forall before world,property before world->Mem.load Mint32 before child_cell 0=Some(Vint child))->
  (forall before world,property before world->Mem.weak_valid_pointer before object(Ptrofs.unsigned offset)=true)->
  gateway_memory_prefix backend ge
    (Callstate(Internal f_host_engine_reap)[Vint child;Vint Int.one]
      (cleanup_reap_cont environment(cleanup_reap_temps child(Vptr saved_block saved_offset)temporaries))memory)property property
    (State f_host_exchange Sskip cleanup_save_after environment(cleanup_save_temps(Vptr saved_block saved_offset)temporaries)memory).
Proof.
  intros CHILD LOCAL FUNCTION RESULT CELL POINTER.
  set(saved:=Vptr saved_block saved_offset).
  eapply gateway_memory_same with(following:=State f_host_exchange cleanup_save_bind
    (Kseq(exchange_cleanup_after 3)Kstop)environment(cleanup_save_temps saved temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange Sskip
    (Kseq(exchange_cleanup_after 3)Kstop)environment(cleanup_saved_temps saved temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply certified_set_edge,old_expression_value,value_temp;apply PTree.gss|].
  eapply gateway_memory_same with(following:=State f_host_exchange(exchange_cleanup_after 3)Kstop
    environment(cleanup_saved_temps saved temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange cleanup_reap_body cleanup_reap_after
    environment(cleanup_saved_temps saved temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange cleanup_reap_load(Kseq cleanup_reap_call cleanup_reap_after)
    environment(cleanup_saved_temps saved temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange Sskip(Kseq cleanup_reap_call cleanup_reap_after)
    environment(cleanup_reap_temps child saved temporaries)memory);
    [exact CLOSED|cbn;tauto| |].
  - intros before world READY;apply certified_set_edge;eapply location_read_value with(b:=child_cell)(ofs:=Ptrofs.zero);
      [apply local_location_value;exact CHILD|eapply deref_loc_value;[reflexivity|exact(CELL before world READY)]].
  - eapply gateway_memory_same with(following:=State f_host_exchange cleanup_reap_call cleanup_reap_after
      environment(cleanup_reap_temps child saved temporaries)memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
    eapply gateway_memory_same with(following:=Callstate(Internal f_host_engine_reap)[Vint child;Vint Int.one]
      (cleanup_reap_cont environment(cleanup_reap_temps child saved temporaries))memory);
      [exact CLOSED|cbn;tauto| |apply gateway_memory_identity].
    intros before world READY;apply actual_cleanup_reap_call with(object:=object)(offset:=offset);
      [exact LOCAL|exact FUNCTION|apply PTree.gss| |exact(POINTER before world READY)].
    unfold cleanup_reap_temps,cleanup_saved_temps,cleanup_save_temps.
    do 3(rewrite PTree.gso by discriminate);exact RESULT.
Qed.
