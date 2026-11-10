(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual parser reference is bound to the original result temporary. *)
From Stdlib Require Import List.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayMemoryPrefixes GatewayFramedRuntime
  GatewayExchangeTransport GatewayResponseParserSource.
Import ListNotations.

Definition gateway_parser_bound_temps(parsed:val)(temporaries:temp_env):=
  PTree.set _result parsed(PTree.set _t'43 parsed(PTree.set _t'44 parsed temporaries)).

Theorem actual_parser_binding_path {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries memory object offset:
  gateway_memory_prefix backend ge
    (State f_host_exchange(exchange_transport_after 6)Kstop environment
      (gateway_parser_bound_temps(Vptr object offset)temporaries)memory)property property
    (State f_host_exchange Sskip response_parser_after_call environment
      (PTree.set _t'44(Vptr object offset)temporaries)memory).
Proof.
  set(parsed:=Vptr object offset).
  eapply gateway_memory_same with(following:=State f_host_exchange response_parser_bind
    (Kseq exchange_result_bind(Kseq(exchange_transport_after 6)Kstop))environment(PTree.set _t'44 parsed temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange Sskip
    (Kseq exchange_result_bind(Kseq(exchange_transport_after 6)Kstop))environment
    (PTree.set _t'43 parsed(PTree.set _t'44 parsed temporaries))memory);
    [exact CLOSED|cbn;tauto| |].
  - intros before world READY;apply certified_set_edge,old_expression_value.
    eapply value_cast with(v:=parsed);[apply value_temp;apply PTree.gss|reflexivity].
  - eapply gateway_memory_same with(following:=State f_host_exchange exchange_result_bind
      (Kseq(exchange_transport_after 6)Kstop)environment(PTree.set _t'43 parsed(PTree.set _t'44 parsed temporaries))memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
    eapply gateway_memory_same with(following:=State f_host_exchange Sskip(Kseq(exchange_transport_after 6)Kstop)environment
      (gateway_parser_bound_temps parsed temporaries)memory);
      [exact CLOSED|cbn;tauto|intros;apply certified_set_edge,old_expression_value,value_temp;apply PTree.gss|].
    eapply gateway_memory_same with(following:=State f_host_exchange(exchange_transport_after 6)Kstop environment
      (gateway_parser_bound_temps parsed temporaries)memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|apply gateway_memory_identity].
Qed.

From HostGateway Require Import GatewayRuntimeCuts GatewayReadonly.

Theorem actual_parser_bound_prefix {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries object offset before world events value after next:
  property before world->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vptr object offset)(response_parser_cont environment temporaries)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vptr object offset)(response_parser_cont environment temporaries)before)world)prefix
      (gateway_live(State f_host_exchange(exchange_transport_after 6)Kstop environment
        (gateway_parser_bound_temps(Vptr object offset)temporaries)memory)current) /\
    property memory current /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange(exchange_transport_after 6)Kstop environment
        (gateway_parser_bound_temps(Vptr object offset)temporaries)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros READY RUN.
  destruct(gateway_uniform_edge_side_cut backend ge property CLOSED
    (Returnstate(Vptr object offset)(response_parser_cont environment temporaries)before)
    (State f_host_exchange Sskip response_parser_after_call environment(PTree.set _t'44(Vptr object offset)temporaries)before)
    before world events value after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_returnstate)READY RUN)
    as(p1&r1&m1&w1&E1&Q1&P1&R1&S1).
  cbn[gateway_replace_memory]in P1,S1.
  destruct(gateway_memory_prefix_cut backend ge _ _ _ _ m1 w1 r1(Returnstate value Kstop after)next
    (actual_parser_binding_path backend ge property CLOSED environment temporaries m1 object offset)I R1 S1)
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
