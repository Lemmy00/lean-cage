(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Actual receive counts select EOF, retry or the real error path. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayMemoryPrefixes GatewayFramedRuntime
  GatewayRuntimeCuts GatewayReadonly GatewayExchangeTransport GatewayEOFSource GatewayEOFReceiveSource.
Import ListNotations.
Open Scope Z_scope.

Definition exchange_eof_retry_sequence:=match exchange_eof_after_receive with Ssequence first _=>first|_=>Sskip end.
Definition exchange_eof_after_retry:=match exchange_eof_after_receive with Ssequence _ rest=>rest|_=>Sskip end.
Definition exchange_eof_retry_compute:=match exchange_eof_retry_sequence with Ssequence first _=>first|_=>Sskip end.
Definition exchange_eof_retry_test:=match exchange_eof_retry_sequence with Ssequence _ rest=>rest|_=>Sskip end.
Definition exchange_eof_count_test:=match exchange_eof_after_retry with Ssequence first _=>first|_=>Sskip end.
Definition exchange_eof_count_error:=match exchange_eof_count_test with Sifthenelse _ first _=>first|_=>Sskip end.
Definition exchange_eof_retry_cont:=Kseq exchange_eof_retry_test(Kseq exchange_eof_after_retry exchange_eof_iteration_cont).
Definition exchange_eof_count_temps count(temporaries:temp_env):=
  PTree.set _count(Vlong count)(PTree.set _t'47(Vlong count)temporaries).

Theorem actual_eof_count_binding_path {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries memory count:
  gateway_memory_prefix backend ge
    (State f_host_exchange exchange_eof_retry_compute exchange_eof_retry_cont environment
      (exchange_eof_count_temps count temporaries)memory)property property
    (State f_host_exchange Sskip exchange_eof_receive_after environment(PTree.set _t'47(Vlong count)temporaries)memory).
Proof.
  eapply gateway_memory_same with(following:=State f_host_exchange exchange_eof_receive_bind
    (Kseq exchange_eof_after_receive exchange_eof_iteration_cont)environment(PTree.set _t'47(Vlong count)temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange Sskip
    (Kseq exchange_eof_after_receive exchange_eof_iteration_cont)environment(exchange_eof_count_temps count temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply certified_set_edge,old_expression_value,value_temp;apply PTree.gss|].
  eapply gateway_memory_same with(following:=State f_host_exchange exchange_eof_after_receive exchange_eof_iteration_cont
    environment(exchange_eof_count_temps count temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange exchange_eof_retry_sequence
    (Kseq exchange_eof_after_retry exchange_eof_iteration_cont)environment(exchange_eof_count_temps count temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange exchange_eof_retry_compute exchange_eof_retry_cont
    environment(exchange_eof_count_temps count temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|apply gateway_memory_identity].
Qed.

Theorem actual_eof_count_bound_prefix {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries count before world events value after next:
  property before world->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vlong count)(exchange_eof_receive_cont environment temporaries)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vlong count)(exchange_eof_receive_cont environment temporaries)before)world)prefix
      (gateway_live(State f_host_exchange exchange_eof_retry_compute exchange_eof_retry_cont environment
        (exchange_eof_count_temps count temporaries)memory)current) /\property memory current /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange exchange_eof_retry_compute exchange_eof_retry_cont environment
        (exchange_eof_count_temps count temporaries)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros READY RUN.
  destruct(gateway_uniform_edge_side_cut backend ge property CLOSED
    (Returnstate(Vlong count)(exchange_eof_receive_cont environment temporaries)before)
    (State f_host_exchange Sskip exchange_eof_receive_after environment(PTree.set _t'47(Vlong count)temporaries)before)
    before world events value after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_returnstate)READY RUN)
    as(p1&r1&m1&w1&E1&Q1&P1&R1&S1).
  cbn[gateway_replace_memory]in P1,S1.
  destruct(gateway_memory_prefix_cut backend ge _ _ _ _ m1 w1 r1(Returnstate value Kstop after)next
    (actual_eof_count_binding_path backend ge property CLOSED environment temporaries m1 count)I R1 S1)
    as(p2&suffix&memory&current&E2&Q2&P2&FINAL&SUFFIX).
  cbn[gateway_replace_memory]in P2,SUFFIX.
  exists(p1++gateway_source E0::p2),suffix,memory,current.
  split;[rewrite E1,E2;rewrite<-app_assoc;reflexivity|]. split.
  - apply Forall_app;split.
    + eapply Forall_impl;[|exact Q1];intros event SAME;right;exact SAME.
    + constructor;[left;reflexivity|exact Q2].
  - split.
    + eapply gateway_steps_append;[exact P1|].
      econstructor;[apply gateway_internal;[cbn;tauto|constructor;reflexivity]|exact P2].
    + split;assumption.
Qed.

Theorem actual_eof_retry_continue_path {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries memory:
  gateway_memory_prefix backend ge
    (State f_host_exchange exchange_eof_loop exchange_eof_cont environment temporaries memory)property property
    (State f_host_exchange Scontinue(Kseq exchange_eof_after_retry exchange_eof_iteration_cont)environment temporaries memory).
Proof.
  eapply gateway_memory_same with(following:=State f_host_exchange Scontinue exchange_eof_iteration_cont environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_continue_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange Sskip
    (Kloop2 exchange_eof_loop_first Sskip exchange_eof_cont)environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_continue_loop1|].
  eapply gateway_memory_same with(following:=State f_host_exchange exchange_eof_loop exchange_eof_cont environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_loop2|apply gateway_memory_identity].
Qed.

Theorem actual_eof_zero_break_path {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries memory:
  temporaries!_count=Some(Vlong Int64.zero)->
  gateway_memory_prefix backend ge
    (State f_host_exchange exchange_cleanup_phase Kstop environment temporaries memory)property property
    (State f_host_exchange exchange_eof_after_retry exchange_eof_iteration_cont environment temporaries memory).
Proof.
  intro COUNT.
  eapply gateway_memory_same with(following:=State f_host_exchange exchange_eof_count_test
    (Kseq Sbreak exchange_eof_iteration_cont)environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange Sskip
    (Kseq Sbreak exchange_eof_iteration_cont)environment temporaries memory);
    [exact CLOSED|cbn;tauto| |].
  - intros before world READY;apply certified_if_edge with(v:=Vint Int.zero)(b:=false).
    + apply old_expression_value;eapply value_binary with(v:=Vlong Int64.zero)(w:=Vint Int.zero);
        [apply value_temp;exact COUNT|constructor|reflexivity].
    + reflexivity.
  - eapply gateway_memory_same with(following:=State f_host_exchange Sbreak exchange_eof_iteration_cont environment temporaries memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
    eapply gateway_memory_same with(following:=State f_host_exchange Sskip exchange_eof_cont environment temporaries memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_break_loop1|].
    eapply gateway_memory_same with(following:=State f_host_exchange exchange_cleanup_phase Kstop environment temporaries memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|apply gateway_memory_identity].
Qed.
