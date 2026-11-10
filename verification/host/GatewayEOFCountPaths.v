(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: The source tests nonnegative receives before breaking its EOF
   loop. *)
From Stdlib Require Import List.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayMemoryPrefixes GatewayFramedRuntime
  GatewayExchangeTransport GatewayEOFSource GatewayEOFReceiveSource GatewayEOFCountSource
  GatewayFailurePaths GatewayResponseReturn GatewayEOFCountError.
Import ListNotations.

Definition exchange_eof_nonnegative_temps(temporaries:temp_env):=PTree.set _t'48(Vint Int.zero)temporaries.

Theorem actual_eof_nonnegative_path {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries memory count:
  temporaries!_count=Some(Vlong count)->Int64.lt count Int64.zero=false->
  gateway_memory_prefix backend ge
    (State f_host_exchange exchange_eof_after_retry exchange_eof_iteration_cont environment
      (exchange_eof_nonnegative_temps temporaries)memory)property property
    (State f_host_exchange exchange_eof_retry_compute exchange_eof_retry_cont environment temporaries memory).
Proof.
  intros COUNT NONNEGATIVE.
  eapply gateway_memory_same with(following:=State f_host_exchange(Sset _t'48(Econst_int Int.zero tint))
    exchange_eof_retry_cont environment temporaries memory);
    [exact CLOSED|cbn;tauto| |].
  - intros before world READY;apply certified_if_edge with(v:=Vint Int.zero)(b:=false).
    + apply old_expression_value;eapply value_binary;[apply value_temp;exact COUNT|constructor|].
      change(Some(Val.of_bool(Int64.lt count Int64.zero))=Some(Vint Int.zero));rewrite NONNEGATIVE;reflexivity.
    + reflexivity.
  - eapply gateway_memory_same with(following:=State f_host_exchange Sskip exchange_eof_retry_cont
      environment(exchange_eof_nonnegative_temps temporaries)memory);
      [exact CLOSED|cbn;tauto|intros;apply certified_set_edge,old_expression_value;constructor|].
    eapply gateway_memory_same with(following:=State f_host_exchange exchange_eof_retry_test
      (Kseq exchange_eof_after_retry exchange_eof_iteration_cont)environment(exchange_eof_nonnegative_temps temporaries)memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
    eapply gateway_memory_same with(following:=State f_host_exchange Sskip
      (Kseq exchange_eof_after_retry exchange_eof_iteration_cont)environment(exchange_eof_nonnegative_temps temporaries)memory);
      [exact CLOSED|cbn;tauto|intros;apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
        [apply old_expression_value,value_temp;apply PTree.gss|reflexivity]|].
    eapply gateway_memory_same with(following:=State f_host_exchange exchange_eof_after_retry exchange_eof_iteration_cont
      environment(exchange_eof_nonnegative_temps temporaries)memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|apply gateway_memory_identity].
Qed.

Theorem actual_eof_zero_source_path {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries memory:
  temporaries!_count=Some(Vlong Int64.zero)->
  gateway_memory_prefix backend ge
    (State f_host_exchange exchange_cleanup_phase Kstop environment(exchange_eof_nonnegative_temps temporaries)memory)
      property property
    (State f_host_exchange exchange_eof_retry_compute exchange_eof_retry_cont environment temporaries memory).
Proof.
  intro COUNT;eapply gateway_memory_prefix_compose.
  - apply actual_eof_nonnegative_path with(count:=Int64.zero);[exact CLOSED|exact COUNT|reflexivity].
  - apply actual_eof_zero_break_path;[exact CLOSED|].
    unfold exchange_eof_nonnegative_temps;rewrite PTree.gso by discriminate;exact COUNT.
Qed.

Theorem actual_eof_positive_one_failure {World Event}(backend:gateway_backend World Event)ge
    environment temporaries memory:
  temporaries!_count=Some(Vlong Int64.one)->
  gateway_failure_result backend ge(State f_host_exchange exchange_eof_retry_compute exchange_eof_retry_cont
    environment temporaries memory).
Proof.
  intro COUNT.
  eapply gateway_failure_edge with(target:=State f_host_exchange(Sset _t'48(Econst_int Int.zero tint))
    exchange_eof_retry_cont environment temporaries memory);
    [cbn;tauto| |].
  - intros;apply certified_if_edge with(v:=Vint Int.zero)(b:=false).
    + apply old_expression_value;eapply value_binary;[apply value_temp;exact COUNT|constructor|reflexivity].
    + reflexivity.
  - response_denied_set_as(Vint Int.zero).
    unfold exchange_eof_retry_cont.
    response_denied_route.
    response_denied_branch false(Vint Int.zero).
    apply actual_eof_nonzero_skipped_failure with(count:=Int64.one);
      [unfold exchange_eof_nonnegative_temps;WriteAll.lookup|reflexivity].
Qed.
