(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: EOF cannot become a successful positive-length native transfer. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayControlPaths GatewayCalls GatewayOperations
  GatewayTransferSource GatewayTransferErrno GatewayTransferProgress.
Import ListNotations.

Definition transfer_count_error:=match transfer_count_test with Sifthenelse _ error _=>error|_=>Sskip end.
Definition transfer_zero_count_values temporaries:=PTree.set _t'11(Vint Int.one)(transfer_positive_retry_values temporaries).

Local Ltac failure_prefix target:=
  eapply gateway_prefix_next with(next:=target);[cbn;tauto|intro another|].

Lemma actual_zero_count_error_prefix ge temporaries memory :
  temporaries!_count=Some(Vlong Int64.zero) ->
  gateway_retained_prefix ge
    (State f_host_transfer transfer_count_error(Kseq transfer_advance_sequence transfer_iteration_cont)empty_env
      (transfer_zero_count_values temporaries)memory)
    (State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env temporaries memory).
Proof.
  intro COUNT.
  failure_prefix(State f_host_transfer transfer_retry_sequence(Kseq transfer_after_retry transfer_iteration_cont)
    empty_env temporaries memory).
  { apply unchanged_store_edge,edge_seq. }
  failure_prefix(State f_host_transfer transfer_retry_prefix
    (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env temporaries memory).
  { apply unchanged_store_edge,edge_seq. }
  failure_prefix(State f_host_transfer(Sset _t'9(Econst_int Int.zero tint))
    (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env temporaries memory).
  { apply certified_if_edge with(v:=Vint Int.zero)(b:=false).
    - apply old_expression_value;eapply value_binary;[apply value_temp;exact COUNT|constructor|reflexivity].
    - reflexivity. }
  failure_prefix(State f_host_transfer Sskip
    (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))
    empty_env(transfer_positive_retry_values temporaries)memory).
  { apply certified_set_edge;apply old_expression_value;constructor. }
  failure_prefix(State f_host_transfer transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)
    empty_env(transfer_positive_retry_values temporaries)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  failure_prefix(State f_host_transfer Sskip(Kseq transfer_after_retry transfer_iteration_cont)
    empty_env(transfer_positive_retry_values temporaries)memory).
  { apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
      [apply old_expression_value,value_temp;unfold transfer_positive_retry_values;apply PTree.gss|reflexivity]. }
  failure_prefix(State f_host_transfer transfer_after_retry transfer_iteration_cont
    empty_env(transfer_positive_retry_values temporaries)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  failure_prefix(State f_host_transfer transfer_count_sequence(Kseq transfer_advance_sequence transfer_iteration_cont)
    empty_env(transfer_positive_retry_values temporaries)memory).
  { apply unchanged_store_edge,edge_seq. }
  failure_prefix(State f_host_transfer transfer_count_choice
    (Kseq transfer_count_test(Kseq transfer_advance_sequence transfer_iteration_cont))
    empty_env(transfer_positive_retry_values temporaries)memory).
  { apply unchanged_store_edge,edge_seq. }
  failure_prefix(State f_host_transfer(Sset _t'11(Econst_int Int.one tint))
    (Kseq transfer_count_test(Kseq transfer_advance_sequence transfer_iteration_cont))
    empty_env(transfer_positive_retry_values temporaries)memory).
  { apply certified_if_edge with(v:=Vint Int.one)(b:=true).
    - apply old_expression_value;eapply value_binary.
      + apply value_temp;unfold transfer_positive_retry_values;rewrite PTree.gso by discriminate;exact COUNT.
      + constructor.
      + reflexivity.
    - reflexivity. }
  failure_prefix(State f_host_transfer Sskip
    (Kseq transfer_count_test(Kseq transfer_advance_sequence transfer_iteration_cont))
    empty_env(transfer_zero_count_values temporaries)memory).
  { apply certified_set_edge;apply old_expression_value;constructor. }
  failure_prefix(State f_host_transfer transfer_count_test(Kseq transfer_advance_sequence transfer_iteration_cont)
    empty_env(transfer_zero_count_values temporaries)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  failure_prefix(State f_host_transfer transfer_count_error(Kseq transfer_advance_sequence transfer_iteration_cont)
    empty_env(transfer_zero_count_values temporaries)memory).
  { apply certified_if_edge with(v:=Vint Int.one)(b:=true);
      [apply old_expression_value,value_temp;unfold transfer_zero_count_values;apply PTree.gss|reflexivity]. }
  change(gateway_retained_prefix ge
    (State f_host_transfer transfer_count_error(Kseq transfer_advance_sequence transfer_iteration_cont)empty_env
      (transfer_zero_count_values temporaries)memory)
    (gateway_replace_memory(State f_host_transfer transfer_count_error(Kseq transfer_advance_sequence transfer_iteration_cont)empty_env
      (transfer_zero_count_values temporaries)memory)memory)).
  constructor.
Qed.

Theorem actual_zero_count_returns_failure {World Event}(backend:gateway_backend World Event)ge
    temporaries before world events returned after next :
  temporaries!_count=Some(Vlong Int64.zero) ->
  gateway_steps backend ge
    (gateway_live(State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env temporaries before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->returned=Vint(Int.neg Int.one).
Proof.
  intros COUNT RUN.
  destruct(gateway_prefix_side_cut backend ge(fun _ _=>True)
    ltac:(unfold gateway_runtime_discipline;intros;exact I)
    (State f_host_transfer transfer_count_error(Kseq transfer_advance_sequence transfer_iteration_cont)empty_env
      (transfer_zero_count_values temporaries)before)
    (State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env temporaries before)
    (actual_zero_count_error_prefix ge temporaries before COUNT)before world events returned after next I RUN)
    as[prefix[suffix[memory[current[EVENTS[QUIET[PREFIX[READY REST]]]]]]]].
  cbn[GatewayMachine.gateway_replace_memory]in REST.
  eapply gateway_error_sequence_returns_failure with(function:=f_host_transfer)
    (continuation:=Kseq transfer_advance_sequence transfer_iteration_cont);[reflexivity|reflexivity|exact REST].
Qed.
