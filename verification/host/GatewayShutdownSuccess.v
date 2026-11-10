(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual successful half-close reaches the same reply-selection source. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOperations GatewayContexts GatewayReadonly GatewayRuntimeCuts
  GatewayMemoryPrefixes GatewayFramedRuntime GatewayReadContext GatewayThreadRuntime GatewayStreamInterface GatewayStreamLayout
  GatewayExchangeSetup GatewayExchangeABI GatewayExchangeRuntime GatewayExchangeTransport GatewayShutdownSource GatewayShutdownReturn
  GatewayShutdownRuntime GatewayTransferMath GatewayPrimitiveCalls GatewaySendRuntime.
Import ListNotations.

Definition shutdown_zero_temps temporaries:=PTree.set _t'33(Vint Int.zero)(PTree.set _t'34(Vint Int.zero)temporaries).

Lemma actual_shutdown_zero_prefix {World Event}(backend:gateway_backend World Event)ge
    property(CLOSED:gateway_ambient_closed backend property)environment temporaries memory:
  gateway_memory_prefix backend ge
    (State f_host_exchange(exchange_transport_after 2)Kstop environment(shutdown_zero_temps temporaries)memory)property property
    (State f_host_exchange Sskip shutdown_after_call environment(PTree.set _t'34(Vint Int.zero)temporaries)memory).
Proof.
  eapply gateway_memory_same with(following:=State f_host_exchange shutdown_cast
    (Kseq exchange_shutdown_test(Kseq(exchange_transport_after 2)Kstop))environment(PTree.set _t'34(Vint Int.zero)temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange Sskip
    (Kseq exchange_shutdown_test(Kseq(exchange_transport_after 2)Kstop))environment(shutdown_zero_temps temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply certified_set_edge,old_expression_value;WriteAll.expression|].
  eapply gateway_memory_same with(following:=State f_host_exchange exchange_shutdown_test
    (Kseq(exchange_transport_after 2)Kstop)environment(shutdown_zero_temps temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange Sskip(Kseq(exchange_transport_after 2)Kstop)
    environment(shutdown_zero_temps temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
      [apply old_expression_value;unfold shutdown_zero_temps;WriteAll.expression|reflexivity]|].
  eapply gateway_memory_same with(following:=State f_host_exchange(exchange_transport_after 2)Kstop
    environment(shutdown_zero_temps temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|apply gateway_memory_identity].
Qed.

Theorem actual_exchange_shutdown {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    (exchange:gateway_exchange_runtime backend io native stable discipline)
    allocation_before allocated environment temporaries stream response initial readonly before world events value after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->temporaries!_failed=Some(Vint Int.zero)->
  gateway_read_context native stable discipline None stream Ptrofs.zero initial response Ptrofs.zero 24 readonly before world->
  value<>Vnullptr->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(exchange_transport_after 1)Kstop environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_transport_after 1)Kstop environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange(exchange_transport_after 2)Kstop environment
        (shutdown_zero_temps(shutdown_temps(stream_descriptor initial)temporaries))memory)current) /\
    gateway_received_bytes io(stream_descriptor initial)prefix=[] /\gateway_sent_bytes io(stream_descriptor initial)prefix=[] /\
    gateway_read_context native stable discipline None stream Ptrofs.zero initial response Ptrofs.zero 24 readonly memory current /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_transport_after 2)Kstop environment
        (shutdown_zero_temps(shutdown_temps(stream_descriptor initial)temporaries))memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros ALLOC STREAM FAILED READY NONNULL RUN.
  set(context:=gateway_read_context native stable discipline None stream Ptrofs.zero initial response Ptrofs.zero 24 readonly).
  assert(CLOSED:gateway_ambient_closed backend context).
  { exact(gateway_read_context_ambient backend io native stable discipline thread_errno runtime None stream Ptrofs.zero initial
      response Ptrofs.zero 24 readonly). }
  assert(LOCAL:environment!_shutdown=None).
  { eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate]. }
  assert(CELLS:forall memory current,context memory current->gateway_stream_memory memory stream Ptrofs.zero initial).
  { intros memory current GOOD;exact(gateway_read_stream_cells _ _ _ _ _ _ _ _(proj2(proj2(proj2(proj2 GOOD))))). }
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ before world events(Returnstate value Kstop after)next
    (actual_shutdown_prefix backend(Clight.globalenv prog)context CLOSED environment temporaries before stream initial
      FAILED STREAM(proj1 actual_stream_layout)LOCAL actual_gateway_shutdown_binding CELLS)I READY RUN)
    as(p1&r1&m1&w1&E1&Q1&P1&C1&R1).
  cbn[gateway_replace_memory]in P1,R1.
  set(selected:=shutdown_temps(stream_descriptor initial)temporaries).
  destruct(gateway_return_cut backend(Clight.globalenv prog)gateway_shutdown_definition[Vint(stream_descriptor initial);Vint Int.one]
    (shutdown_cont environment selected)m1 w1 r1(Returnstate value Kstop after)next I ltac:(cbn;lia)R1)
    as(p2&r2&returned&m2&w2&E2&P2&R2).
  destruct(actual_shutdown_receive_context backend io native stable discipline thread_errno runtime exchange stream response initial readonly
    (stream_descriptor initial)m1 w1 p2 returned m2 w2 C1 P2)as[TYPE[C2[IN2 OUT2]]].
  pose proof(actual_successful_shutdown_return backend(Clight.globalenv prog)environment selected m2 w2 r2 returned value after next
    TYPE NONNULL R2)as ZERO;subst returned.
  destruct(gateway_uniform_edge_side_cut backend(Clight.globalenv prog)context CLOSED
    (Returnstate(Vint Int.zero)(shutdown_cont environment selected)m2)
    (State f_host_exchange Sskip shutdown_after_call environment(PTree.set _t'34(Vint Int.zero)selected)m2)
    m2 w2 r2 value after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_returnstate)C2 R2)
    as(p3&r3&m3&w3&E3&A3&P3&C3&R3).
  cbn[gateway_replace_memory]in P3,R3.
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ m3 w3 r3(Returnstate value Kstop after)next
    (actual_shutdown_zero_prefix backend(Clight.globalenv prog)context CLOSED environment selected m3)I C3 R3)
    as(p4&suffix&memory&current&E4&Q4&P4&FINAL&SUFFIX).
  cbn[gateway_replace_memory]in P4,SUFFIX.
  exists(p1++p2++p3++gateway_source E0::p4),suffix,memory,current.
  split;[rewrite E1,E2,E3,E4;repeat rewrite<-app_assoc;reflexivity|]. split.
  - eapply gateway_steps_append;[exact P1|]. eapply gateway_steps_append;[exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _(shutdown_cont environment selected)I P2)|].
    eapply gateway_steps_append;[exact P3|].
    econstructor;[apply gateway_internal;[cbn;tauto|apply step_returnstate]|exact P4].
  - assert(Q3:Forall gateway_quiet_event p3).
    { eapply Forall_impl;[|exact A3];intros event SAME;right;exact SAME. }
    split.
    + rewrite !gateway_received_bytes_append,(gateway_quiet_received_empty io(stream_descriptor initial)p1 Q1),IN2,
        (gateway_quiet_received_empty io(stream_descriptor initial)p3 Q3).
      cbn[gateway_received_bytes gateway_received_event];exact(gateway_quiet_received_empty io(stream_descriptor initial)p4 Q4).
    + split.
      * rewrite !gateway_sent_bytes_append,(gateway_quiet_sent_empty io(stream_descriptor initial)p1 Q1),OUT2,
          (gateway_quiet_sent_empty io(stream_descriptor initial)p3 Q3).
        cbn[gateway_sent_bytes gateway_sent_event];exact(gateway_quiet_sent_empty io(stream_descriptor initial)p4 Q4).
      * split;assumption.
Qed.
