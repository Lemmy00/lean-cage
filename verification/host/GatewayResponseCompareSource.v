(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual decoded-length store precedes the actual magic comparison. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewaySourcePaths GatewayFramedRuntime GatewayStreamLayout
  GatewayExchangeTransport GatewayResponseLengthSource GatewayResponseWord GatewayResponseBudget GatewayThreadRuntime GatewayReadContext
  GatewayBootstrapABI.
Import ListNotations.
Open Scope Z_scope.

Definition response_bounds_test:=match response_after_length with Ssequence _ rest=>rest|_=>Sskip end.
Definition response_bounds_select:=match response_after_length with Ssequence first _=>first|_=>Sskip end.
Definition response_size_test:=match response_bounds_select with Ssequence _ rest=>rest|_=>Sskip end.
Definition response_reserved_select:=match response_bounds_select with Ssequence first _=>first|_=>Sskip end.
Definition response_reserved_test:=match response_reserved_select with Ssequence _ rest=>rest|_=>Sskip end.
Definition response_magic_select:=match response_reserved_select with Ssequence first _=>first|_=>Sskip end.
Definition response_status_test:=match response_magic_select with Ssequence _ rest=>rest|_=>Sskip end.
Definition response_magic_call:=match response_magic_select with Ssequence first _=>first|_=>Sskip end.
Definition response_compare_after_call:=Kseq response_status_test(Kseq response_reserved_test
  (Kseq response_size_test(Kseq response_bounds_test(Kseq(exchange_transport_after 5)Kstop)))).
Definition response_compare_cont environment temporaries:=Kcall(Some _t'38)f_host_exchange environment temporaries response_compare_after_call.
Definition response_compare_arguments response magic:=[Vptr response Ptrofs.zero;Vptr magic Ptrofs.zero;Vlong(Int64.repr 8)].

Lemma actual_response_remaining_store ge environment temporaries before stream remaining after continuation:
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->stream_member_layout ge _remaining 24->
  temporaries!_t'37=Some(Vlong remaining)->Mem.store Mint64 before stream 24(Vlong remaining)=Some after->
  store_edge ge(State f_host_exchange response_length_store continuation environment temporaries before)
    (State f_host_exchange Sskip continuation environment temporaries after).
Proof.
  intros STREAM[composite[LAYOUT MEMBER]]VALUE STORE.
  eapply assignment_source_edge with(b:=stream)(ofs:=Ptrofs.add Ptrofs.zero(Ptrofs.repr 24))
    (v:=Vlong remaining)(w:=Vlong remaining).
  - eapply struct_location_value with(id:=_host_stream)(co:=composite)(att:=noattr)(delta:=24).
    + eapply location_read_value;[apply local_location_value;exact STREAM|apply deref_loc_copy;reflexivity].
    + reflexivity.
    + exact LAYOUT.
    + exact MEMBER.
  - apply old_expression_value,value_temp;exact VALUE.
  - reflexivity.
  - eapply assign_loc_value;[reflexivity|exact STORE].
Qed.

Lemma actual_response_compare_call(ge:Clight.genv)environment temporaries memory response magic:
  environment!_response=Some(response,tarray tuchar 24)->environment!___stringlit_25=None->
  Genv.find_symbol ge ___stringlit_25=Some magic->environment!_memcmp=None->
  gateway_function_binding ge _memcmp(gateway_bootstrap_signature gateway_memory_compare_api)->
  store_edge ge(State f_host_exchange response_magic_call response_compare_after_call environment temporaries memory)
    (Callstate(gateway_bootstrap_signature gateway_memory_compare_api)(response_compare_arguments response magic)
      (response_compare_cont environment temporaries)memory).
Proof.
  intros RESPONSE MAGIC_LOCAL MAGIC LOCAL[symbol[SYMBOL FUNCTION]].
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vptr response Ptrofs.zero).
    + eapply location_read_value;[apply local_location_value;exact RESPONSE|apply deref_loc_reference;reflexivity].
    + reflexivity.
    + eapply cons_argument_values with(v:=Vptr magic Ptrofs.zero).
      * eapply location_read_value;[apply global_location_value;[exact MAGIC_LOCAL|exact MAGIC]|apply deref_loc_reference;reflexivity].
      * reflexivity.
      * eapply cons_argument_values with(v:=Vint(Int.repr 8));
          [apply old_expression_value;constructor|reflexivity|apply no_argument_values].
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_response_compare_path {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    environment temporaries memory stream response magic initial readonly bytes remaining:
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->environment!_response=Some(response,tarray tuchar 24)->
  environment!___stringlit_25=None->Genv.find_symbol(Clight.globalenv prog)___stringlit_25=Some magic->environment!_memcmp=None->
  gateway_source_path backend(Clight.globalenv prog)(gateway_bootstrap_signature gateway_memory_compare_api)(response_compare_arguments response magic)
    (response_compare_cont environment(PTree.set _t'37(Vlong remaining)temporaries))
    (gateway_response_context native stable discipline stream response readonly initial bytes)
    (Returnstate(Vlong remaining)(response_length_cont environment temporaries)memory)
    (gateway_response_context native stable discipline stream response readonly(gateway_response_budget initial remaining)bytes).
Proof.
  intros STREAM RESPONSE MAGIC_LOCAL MAGIC LOCAL.
  set(before_context:=gateway_response_context native stable discipline stream response readonly initial bytes).
  set(after_context:=gateway_response_context native stable discipline stream response readonly(gateway_response_budget initial remaining)bytes).
  assert(BEFORE_CLOSED:gateway_ambient_closed backend before_context).
  { apply gateway_response_context_ambient with(io:=io)(thread_errno:=thread_errno);exact runtime. }
  assert(AFTER_CLOSED:gateway_ambient_closed backend after_context).
  { apply gateway_response_context_ambient with(io:=io)(thread_errno:=thread_errno);exact runtime. }
  set(values:=PTree.set _t'37(Vlong remaining)temporaries).
  eapply gateway_source_same with(target:=State f_host_exchange Sskip response_length_after_call environment values memory);
    [exact BEFORE_CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_source_same with(target:=State f_host_exchange response_length_store
    (Kseq response_after_length(Kseq(exchange_transport_after 5)Kstop))environment values memory);
    [exact BEFORE_CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_source_next with(target:=State f_host_exchange Sskip
    (Kseq response_after_length(Kseq(exchange_transport_after 5)Kstop))environment values memory)(middle:=after_context).
  - exact BEFORE_CLOSED.
  - cbn;tauto.
  - intros before world READY.
    destruct(gateway_response_budget_allocates before stream response readonly initial remaining
      (proj2(proj2(proj2(proj2(proj1 READY))))))as[after STORE].
    exists after;split.
    + eapply actual_response_remaining_store;[exact STREAM|exact(proj1(proj2(proj2(proj2(proj2(proj2 actual_stream_layout))))))|
        unfold values;apply PTree.gss|exact STORE].
    + eapply gateway_response_budget_store;[exact runtime|exact READY|exact STORE].
  - eapply gateway_source_same with(target:=State f_host_exchange response_after_length(Kseq(exchange_transport_after 5)Kstop)
      environment values memory);[exact AFTER_CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
    eapply gateway_source_same with(target:=State f_host_exchange response_bounds_select(Kseq response_bounds_test(Kseq(exchange_transport_after 5)Kstop))
      environment values memory);[exact AFTER_CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
    eapply gateway_source_same with(target:=State f_host_exchange response_reserved_select
      (Kseq response_size_test(Kseq response_bounds_test(Kseq(exchange_transport_after 5)Kstop)))environment values memory);
      [exact AFTER_CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
    eapply gateway_source_same with(target:=State f_host_exchange response_magic_select
      (Kseq response_reserved_test(Kseq response_size_test(Kseq response_bounds_test(Kseq(exchange_transport_after 5)Kstop))))environment values memory);
      [exact AFTER_CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
    eapply gateway_source_same with(target:=State f_host_exchange response_magic_call response_compare_after_call environment values memory);
      [exact AFTER_CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
    eapply gateway_source_same with(target:=Callstate(gateway_bootstrap_signature gateway_memory_compare_api)(response_compare_arguments response magic)
      (response_compare_cont environment values)memory);
      [exact AFTER_CLOSED|cbn;tauto|intros;eapply actual_response_compare_call;[exact RESPONSE|exact MAGIC_LOCAL|exact MAGIC|exact LOCAL|
        exact(actual_bootstrap_bindings gateway_memory_compare_api)]|apply gateway_source_reached;intros;assumption].
Qed.
