(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The same cleanup restores the token saved before its real reap call. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayRuntimeABI GatewaySourcePaths
  GatewayMemoryPrefixes GatewayFramedRuntime GatewayCleanupSource GatewayCleanupThreadSource.
Import ListNotations.

Definition cleanup_restore_call:=exchange_cleanup_statement 4.
Definition cleanup_restore_after:=Kseq(exchange_cleanup_after 5)Kstop.
Definition cleanup_restore_cont environment temporaries:=Kcall None f_host_exchange environment temporaries cleanup_restore_after.

Theorem actual_cleanup_restore_call ge environment temporaries memory saved_block saved_offset:
  environment!_PyEval_RestoreThread=None->gateway_function_binding ge _PyEval_RestoreThread gateway_restore_thread_definition->
  temporaries!_saved=Some(Vptr saved_block saved_offset)->
  store_edge ge(State f_host_exchange cleanup_restore_call cleanup_restore_after environment temporaries memory)
    (Callstate gateway_restore_thread_definition[Vptr saved_block saved_offset](cleanup_restore_cont environment temporaries)memory).
Proof.
  intros LOCAL[symbol[SYMBOL FUNCTION]]SAVED.
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vptr saved_block saved_offset);
      [apply old_expression_value,value_temp;exact SAVED|reflexivity|apply no_argument_values].
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_cleanup_reap_restore_path {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries memory returned saved_block saved_offset:
  environment!_PyEval_RestoreThread=None->gateway_function_binding ge _PyEval_RestoreThread gateway_restore_thread_definition->
  temporaries!_saved=Some(Vptr saved_block saved_offset)->
  gateway_source_path backend ge gateway_restore_thread_definition[Vptr saved_block saved_offset]
    (cleanup_restore_cont environment temporaries)property
    (Returnstate returned(cleanup_reap_cont environment temporaries)memory)property.
Proof.
  intros LOCAL FUNCTION SAVED.
  eapply gateway_source_same with(target:=State f_host_exchange Sskip cleanup_reap_after environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_source_same with(target:=State f_host_exchange(exchange_cleanup_after 4)Kstop environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_source_same with(target:=State f_host_exchange cleanup_restore_call cleanup_restore_after environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_source_same with(target:=Callstate gateway_restore_thread_definition[Vptr saved_block saved_offset]
    (cleanup_restore_cont environment temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply actual_cleanup_restore_call;assumption|
      apply gateway_source_reached;intros;assumption].
Qed.

Theorem actual_cleanup_restored_final_path {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries memory:
  gateway_memory_prefix backend ge
    (State f_host_exchange(exchange_cleanup_after 5)Kstop environment temporaries memory)property property
    (State f_host_exchange Sskip cleanup_restore_after environment temporaries memory).
Proof.
  eapply gateway_memory_same with(following:=State f_host_exchange(exchange_cleanup_after 5)Kstop environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|apply gateway_memory_identity].
Qed.
