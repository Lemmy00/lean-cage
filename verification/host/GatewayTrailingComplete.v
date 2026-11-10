(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: The real successful caller consumes its complete declared payload. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayMemoryPrefixes GatewayFramedRuntime GatewayFailurePaths
  GatewayReadonly GatewayExchangeTransport GatewayStreamInterface GatewayStreamLayout GatewayTrailingSource GatewayTrailingError.
Import ListNotations.
Open Scope Z_scope.

Lemma actual_trailing_zero_guard {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries memory:
  temporaries!_t'45=Some(Vint Int.zero)->
  gateway_memory_prefix backend ge
    (State f_host_exchange(exchange_transport_after 7)Kstop environment temporaries memory)property property
    (State f_host_exchange exchange_trailing_test(Kseq(exchange_transport_after 7)Kstop)environment temporaries memory).
Proof.
  intro ZERO.
  eapply gateway_memory_same with(following:=State f_host_exchange Sskip(Kseq(exchange_transport_after 7)Kstop)environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
      [apply old_expression_value,value_temp;exact ZERO|reflexivity]|].
  eapply gateway_memory_same with(following:=State f_host_exchange(exchange_transport_after 7)Kstop environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|apply gateway_memory_identity].
Qed.

Theorem actual_successful_trailing_guard {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries stream initial object offset before world events value after next:
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->stream_member_layout ge _remaining 24->
  temporaries!_result=Some(Vptr object offset)->
  (forall memory current,property memory current->gateway_stream_memory memory stream Ptrofs.zero initial)->
  (forall memory current,property memory current->Mem.weak_valid_pointer memory object(Ptrofs.unsigned offset)=true)->
  property before world->value<>Vnullptr->
  gateway_steps backend ge
    (gateway_live(State f_host_exchange(exchange_transport_after 6)Kstop environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  stream_remaining initial=Int64.zero /\
  exists prefix suffix memory current,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange(exchange_transport_after 6)Kstop environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange(exchange_transport_after 7)Kstop environment
        (gateway_trailing_temps(stream_remaining initial)temporaries)memory)current) /\
    property memory current /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange(exchange_transport_after 7)Kstop environment
        (gateway_trailing_temps(stream_remaining initial)temporaries)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros STREAM LAYOUT RESULT CELLS POINTER READY NONNULL RUN.
  destruct(gateway_memory_prefix_cut backend ge _ _ _ _ before world events(Returnstate value Kstop after)next
    (actual_trailing_select_path backend ge property CLOSED environment temporaries before stream initial object offset
      STREAM LAYOUT RESULT CELLS POINTER)I READY RUN)
    as(p1&r1&m1&w1&E1&Q1&P1&R1&S1).
  cbn[gateway_replace_memory]in P1,S1.
  assert(ZERO:Int64.eq(stream_remaining initial)Int64.zero=true).
  { destruct(Int64.eq(stream_remaining initial)Int64.zero)eqn:CHOICE;[reflexivity|].
    exfalso;apply NONNULL.
    assert(FAILURE:gateway_failure_result backend ge(State f_host_exchange exchange_trailing_test
      (Kseq(exchange_transport_after 7)Kstop)environment(gateway_trailing_temps(stream_remaining initial)temporaries)m1)).
    { eapply gateway_failure_edge with(target:=State f_host_exchange exchange_trailing_error
        (Kseq(exchange_transport_after 7)Kstop)environment(gateway_trailing_temps(stream_remaining initial)temporaries)m1).
      - cbn;tauto.
      - intros;apply certified_if_edge with(v:=Vint Int.one)(b:=true).
        + apply old_expression_value,value_temp;unfold gateway_trailing_temps,gateway_trailing_flag;rewrite CHOICE;apply PTree.gss.
        + reflexivity.
      - apply actual_trailing_error_failure. }
    exact(FAILURE m1 w1 r1 value after next S1). }
  split;[apply Int64.same_if_eq;exact ZERO|].
  destruct(gateway_memory_prefix_cut backend ge _ _ _ _ m1 w1 r1(Returnstate value Kstop after)next
    (actual_trailing_zero_guard backend ge property CLOSED environment(gateway_trailing_temps(stream_remaining initial)temporaries)m1
      ltac:(unfold gateway_trailing_temps,gateway_trailing_flag;rewrite ZERO;apply PTree.gss))I R1 S1)
    as(p2&suffix&memory&current&E2&Q2&P2&FINAL&SUFFIX).
  cbn[gateway_replace_memory]in P2,SUFFIX.
  exists(p1++p2),suffix,memory,current.
  split;[rewrite E1,E2,app_assoc;reflexivity|]. split;[apply Forall_app;split;assumption|].
  split;[eapply gateway_steps_append;[exact P1|exact P2]|]. split;assumption.
Qed.
