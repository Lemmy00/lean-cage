(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Real reap source arguments retain the selected child and
   completion flag. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayReapABI GatewayMemoryPrefixes
  GatewayFramedRuntime GatewayPrefix GatewayReapAllocation GatewayExchangeABI.
Import ListNotations.
Open Scope Z_scope.

Definition reap_initial_test:=match fn_body f_host_engine_reap with Ssequence first _=>first|_=>Sskip end.
Definition reap_after_initial:=match fn_body f_host_engine_reap with Ssequence _ rest=>rest|_=>Sskip end.
Definition reap_initial_kill:=match reap_initial_test with Sifthenelse _ first _=>first|_=>Sskip end.
Definition reap_began_sequence:=match reap_after_initial with Ssequence first _=>first|_=>Sskip end.
Definition reap_after_began:=match reap_after_initial with Ssequence _ rest=>rest|_=>Sskip end.
Definition reap_began_call:=match reap_began_sequence with Ssequence first _=>first|_=>Sskip end.
Definition reap_began_bind:=match reap_began_sequence with Ssequence _ rest=>rest|_=>Sskip end.
Definition reap_clock_after:=Kseq reap_began_bind(Kseq reap_after_began Kstop).
Definition reap_clock_cont environment temporaries:=Kcall(Some _t'1)f_host_engine_reap environment temporaries reap_clock_after.
Definition reap_initial_kill_cont environment temporaries:=Kcall None f_host_engine_reap environment temporaries(Kseq reap_after_initial Kstop).
Definition reap_main_loop:=match reap_after_began with Ssequence first _=>first|_=>Sskip end.
Definition reap_after_main_loop:=match reap_after_began with Ssequence _ rest=>rest|_=>Sskip end.
Definition reap_loop_first:=match reap_main_loop with Sloop first _=>first|_=>Sskip end.
Definition reap_loop_tail:=match reap_loop_first with Ssequence _ rest=>rest|_=>Sskip end.
Definition reap_wait_sequence:=match reap_loop_tail with Ssequence first _=>first|_=>Sskip end.
Definition reap_after_wait:=match reap_loop_tail with Ssequence _ rest=>rest|_=>Sskip end.
Definition reap_wait_call:=match reap_wait_sequence with Ssequence first _=>first|_=>Sskip end.
Definition reap_observed_bind:=match reap_wait_sequence with Ssequence _ rest=>rest|_=>Sskip end.
Definition reap_loop_cont:=Kseq reap_after_main_loop Kstop.
Definition reap_iteration_cont:=Kloop1 reap_loop_first Sskip reap_loop_cont.
Definition reap_wait_after:=Kseq reap_observed_bind(Kseq reap_after_wait reap_iteration_cont).
Definition reap_wait_cont environment temporaries:=Kcall(Some _t'2)f_host_engine_reap environment temporaries reap_wait_after.

Theorem actual_reap_clock_call ge environment temporaries memory:
  environment!_host_now=None->gateway_function_binding ge _host_now(Internal f_host_now)->
  store_edge ge(State f_host_engine_reap reap_began_call reap_clock_after environment temporaries memory)
    (Callstate(Internal f_host_now)[](reap_clock_cont environment temporaries)memory).
Proof.
  intros LOCAL[symbol[SYMBOL FUNCTION]];eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero);
    [reflexivity|apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity]|
      apply no_argument_values|cbn;exact FUNCTION|reflexivity].
Qed.

Theorem actual_reap_wait_call ge environment temporaries memory status child:
  environment!_status=Some(status,tint)->environment!_waitpid=None->
  gateway_function_binding ge _waitpid gateway_waitpid_definition->temporaries!_child=Some(Vint child)->
  store_edge ge(State f_host_engine_reap reap_wait_call reap_wait_after environment temporaries memory)
    (Callstate gateway_waitpid_definition[Vint child;Vptr status Ptrofs.zero;Vint Int.one]
      (reap_wait_cont environment temporaries)memory).
Proof.
  intros STATUS LOCAL[symbol[SYMBOL FUNCTION]]CHILD.
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vint child).
    + apply old_expression_value,value_temp;exact CHILD.
    + reflexivity.
    + eapply cons_argument_values with(v:=Vptr status Ptrofs.zero).
      * apply local_address_expression;exact STATUS.
      * reflexivity.
      * eapply cons_argument_values with(v:=Vint Int.one);
          [apply old_expression_value;constructor|reflexivity|apply no_argument_values].
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_reap_loop_wait_prefix {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries memory status child:
  environment!_status=Some(status,tint)->environment!_waitpid=None->
  gateway_function_binding ge _waitpid gateway_waitpid_definition->temporaries!_child=Some(Vint child)->
  gateway_memory_prefix backend ge
    (Callstate gateway_waitpid_definition[Vint child;Vptr status Ptrofs.zero;Vint Int.one]
      (reap_wait_cont environment temporaries)memory)property property
    (State f_host_engine_reap reap_main_loop reap_loop_cont environment temporaries memory).
Proof.
  intros STATUS LOCAL FUNCTION CHILD.
  eapply gateway_memory_same with(following:=State f_host_engine_reap reap_loop_first reap_iteration_cont environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_loop|].
  eapply gateway_memory_same with(following:=State f_host_engine_reap Sskip(Kseq reap_loop_tail reap_iteration_cont)environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_engine_reap reap_loop_tail reap_iteration_cont environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_memory_same with(following:=State f_host_engine_reap reap_wait_sequence(Kseq reap_after_wait reap_iteration_cont)environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_engine_reap reap_wait_call reap_wait_after environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=Callstate gateway_waitpid_definition[Vint child;Vptr status Ptrofs.zero;Vint Int.one]
    (reap_wait_cont environment temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply actual_reap_wait_call;assumption|apply gateway_memory_identity].
Qed.

Theorem actual_reap_initial_kill_call ge environment temporaries memory child:
  environment!_kill=None->gateway_function_binding ge _kill gateway_kill_definition->temporaries!_child=Some(Vint child)->
  store_edge ge(State f_host_engine_reap reap_initial_kill(Kseq reap_after_initial Kstop)environment temporaries memory)
    (Callstate gateway_kill_definition[Vint(Int.neg child);Vint(Int.repr 9)](reap_initial_kill_cont environment temporaries)memory).
Proof.
  intros LOCAL[symbol[SYMBOL FUNCTION]]CHILD;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vint(Int.neg child)).
    + apply old_expression_value;eapply value_unary;[apply value_temp;exact CHILD|reflexivity].
    + reflexivity.
    + eapply cons_argument_values with(v:=Vint(Int.repr 9));
        [apply old_expression_value;constructor|reflexivity|apply no_argument_values].
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_reap_completed_initial_prefix {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries memory:
  temporaries!_complete=Some(Vint Int.one)->environment!_host_now=None->gateway_function_binding ge _host_now(Internal f_host_now)->
  gateway_memory_prefix backend ge(Callstate(Internal f_host_now)[](reap_clock_cont environment temporaries)memory)property property
    (State f_host_engine_reap(fn_body f_host_engine_reap)Kstop environment temporaries memory).
Proof.
  intros COMPLETE LOCAL FUNCTION.
  eapply gateway_memory_same with(following:=State f_host_engine_reap reap_initial_test(Kseq reap_after_initial Kstop)environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_engine_reap Sskip(Kseq reap_after_initial Kstop)environment temporaries memory);
    [exact CLOSED|cbn;tauto| |].
  - intros before world READY;apply certified_if_edge with(v:=Vint Int.zero)(b:=false).
    + apply old_expression_value;eapply value_unary;[apply value_temp;exact COMPLETE|reflexivity].
    + reflexivity.
  - eapply gateway_memory_same with(following:=State f_host_engine_reap reap_after_initial Kstop environment temporaries memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
    eapply gateway_memory_same with(following:=State f_host_engine_reap reap_began_sequence(Kseq reap_after_began Kstop)environment temporaries memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
    eapply gateway_memory_same with(following:=State f_host_engine_reap reap_began_call reap_clock_after environment temporaries memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
    eapply gateway_memory_same with(following:=Callstate(Internal f_host_now)[](reap_clock_cont environment temporaries)memory);
      [exact CLOSED|cbn;tauto|intros;apply actual_reap_clock_call;assumption|apply gateway_memory_identity].
Qed.

Theorem actual_reap_incomplete_initial_prefix {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries memory child:
  temporaries!_complete=Some(Vint Int.zero)->temporaries!_child=Some(Vint child)->
  environment!_kill=None->gateway_function_binding ge _kill gateway_kill_definition->
  gateway_memory_prefix backend ge
    (Callstate gateway_kill_definition[Vint(Int.neg child);Vint(Int.repr 9)](reap_initial_kill_cont environment temporaries)memory)property property
    (State f_host_engine_reap(fn_body f_host_engine_reap)Kstop environment temporaries memory).
Proof.
  intros COMPLETE CHILD LOCAL FUNCTION.
  eapply gateway_memory_same with(following:=State f_host_engine_reap reap_initial_test(Kseq reap_after_initial Kstop)environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_engine_reap reap_initial_kill(Kseq reap_after_initial Kstop)environment temporaries memory);
    [exact CLOSED|cbn;tauto| |].
  - intros before world READY;apply certified_if_edge with(v:=Vint Int.one)(b:=true).
    + apply old_expression_value;eapply value_unary;[apply value_temp;exact COMPLETE|reflexivity].
    + reflexivity.
  - eapply gateway_memory_same with(following:=Callstate gateway_kill_definition[Vint(Int.neg child);Vint(Int.repr 9)]
      (reap_initial_kill_cont environment temporaries)memory);
      [exact CLOSED|cbn;tauto|intros;apply actual_reap_initial_kill_call;assumption|apply gateway_memory_identity].
Qed.
