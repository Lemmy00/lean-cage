(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Actual interrupted receives retry with the same cursor and size. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPure GatewayControlPaths GatewayCallPath
  GatewayTransferSource GatewayTransferErrno GatewayTransferProgress GatewayTransferLoop GatewayTransferFailure.
Import ListNotations.
Open Scope Z_scope.

Definition transfer_errno_sequence:=match transfer_retry_prefix with Sifthenelse _ retry _=>retry|_=>Sskip end.
Definition transfer_errno_first:=match transfer_errno_sequence with Ssequence first _=>first|_=>Sskip end.
Definition transfer_errno_second:=match transfer_errno_sequence with Ssequence _ second=>second|_=>Sskip end.
Definition transfer_retry_errno_values temporaries:=PTree.set _t'10(Vint Int.one)temporaries.
Definition transfer_retry_values temporaries:=PTree.set _t'9(Vint Int.one)(transfer_retry_errno_values temporaries).

Local Ltac retry_prefix target:=
  eapply gateway_prefix_next with(next:=target);[cbn;tauto|intro another|].

Lemma actual_negative_count_comparison ge environment temporaries memory :
  temporaries!_count=Some(Vlong(Int64.repr(-1))) ->
  expression_value ge environment temporaries memory
    (Ebinop Olt(Etempvar _count tlong)(Econst_int Int.zero tint)tint)(Vint Int.one).
Proof.
  intro COUNT;apply old_expression_value;eapply value_binary;
    [apply value_temp;exact COUNT|constructor|reflexivity].
Qed.

Lemma actual_retry_errno_first_prefix ge temporaries number memory :
  temporaries!_number=Some(Vint number) ->
  (number=Int.repr 4 \/number=Int.repr 11) ->
  gateway_retained_prefix ge
    (State f_host_transfer transfer_errno_second
      (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env
      (transfer_retry_errno_values temporaries)memory)
    (State f_host_transfer transfer_errno_first
      (Kseq transfer_errno_second(Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)))
      empty_env temporaries memory).
Proof.
  intros NUMBER[FOUR|ELEVEN];subst number.
  - retry_prefix(State f_host_transfer(Sset _t'10(Econst_int Int.one tint))
      (Kseq transfer_errno_second(Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)))
      empty_env temporaries memory).
    { apply certified_if_edge with(v:=Vint Int.one)(b:=true);
        [apply old_expression_value;eapply value_binary;[apply value_temp;exact NUMBER|constructor|reflexivity]|reflexivity]. }
    retry_prefix(State f_host_transfer Sskip
      (Kseq transfer_errno_second(Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)))
      empty_env(transfer_retry_errno_values temporaries)memory).
    { apply certified_set_edge;apply old_expression_value;constructor. }
    retry_prefix(State f_host_transfer transfer_errno_second
      (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env
      (transfer_retry_errno_values temporaries)memory).
    { apply unchanged_store_edge,edge_skip_seq. }
    change(gateway_retained_prefix ge
      (State f_host_transfer transfer_errno_second
        (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env
        (transfer_retry_errno_values temporaries)memory)
      (gateway_replace_memory(State f_host_transfer transfer_errno_second
        (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env
        (transfer_retry_errno_values temporaries)memory)memory));constructor.
  - retry_prefix(State f_host_transfer
      (Sset _t'10(Ecast(Ebinop Oeq(Etempvar _number tint)(Econst_int(Int.repr 11)tint)tint)tbool))
      (Kseq transfer_errno_second(Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)))
      empty_env temporaries memory).
    { apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
        [apply old_expression_value;eapply value_binary;[apply value_temp;exact NUMBER|constructor|reflexivity]|reflexivity]. }
    retry_prefix(State f_host_transfer Sskip
      (Kseq transfer_errno_second(Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)))
      empty_env(transfer_retry_errno_values temporaries)memory).
    { apply certified_set_edge;apply cast_expression_value with(v:=Vint Int.one);[|reflexivity].
      apply old_expression_value;eapply value_binary;[apply value_temp;exact NUMBER|constructor|reflexivity]. }
    retry_prefix(State f_host_transfer transfer_errno_second
      (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env
      (transfer_retry_errno_values temporaries)memory).
    { apply unchanged_store_edge,edge_skip_seq. }
    change(gateway_retained_prefix ge
      (State f_host_transfer transfer_errno_second
        (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env
        (transfer_retry_errno_values temporaries)memory)
      (gateway_replace_memory(State f_host_transfer transfer_errno_second
        (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env
        (transfer_retry_errno_values temporaries)memory)memory));constructor.
Qed.

Lemma actual_retry_errno_tail_prefix ge temporaries memory :
  gateway_retained_prefix ge
    (State f_host_transfer transfer_loop transfer_loop_cont empty_env(transfer_retry_values temporaries)memory)
    (State f_host_transfer transfer_errno_second
      (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env
      (transfer_retry_errno_values temporaries)memory).
Proof.
  retry_prefix(State f_host_transfer(Sset _t'9(Ecast(Econst_int Int.one tint)tbool))
    (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env
    (transfer_retry_errno_values temporaries)memory).
  { apply certified_if_edge with(v:=Vint Int.one)(b:=true);
      [apply old_expression_value,value_temp;apply PTree.gss|reflexivity]. }
  retry_prefix(State f_host_transfer Sskip
    (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env
    (transfer_retry_values temporaries)memory).
  { apply certified_set_edge;apply cast_expression_value with(v:=Vint Int.one);
      [apply old_expression_value;constructor|reflexivity]. }
  retry_prefix(State f_host_transfer transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)
    empty_env(transfer_retry_values temporaries)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  retry_prefix(State f_host_transfer Scontinue(Kseq transfer_after_retry transfer_iteration_cont)
    empty_env(transfer_retry_values temporaries)memory).
  { apply certified_if_edge with(v:=Vint Int.one)(b:=true);
      [apply old_expression_value,value_temp;apply PTree.gss|reflexivity]. }
  retry_prefix(State f_host_transfer Scontinue transfer_iteration_cont empty_env(transfer_retry_values temporaries)memory).
  { apply unchanged_store_edge,edge_continue_seq. }
  retry_prefix(State f_host_transfer Sskip(Kloop2 transfer_loop_first Sskip transfer_loop_cont)empty_env
    (transfer_retry_values temporaries)memory).
  { apply unchanged_store_edge,edge_continue_loop1. }
  retry_prefix(State f_host_transfer transfer_loop transfer_loop_cont empty_env(transfer_retry_values temporaries)memory).
  { apply unchanged_store_edge,edge_skip_loop2. }
  change(gateway_retained_prefix ge
    (State f_host_transfer transfer_loop transfer_loop_cont empty_env(transfer_retry_values temporaries)memory)
    (gateway_replace_memory(State f_host_transfer transfer_loop transfer_loop_cont empty_env
      (transfer_retry_values temporaries)memory)memory));constructor.
Qed.

Lemma gateway_retained_prefix_relocate ge target source :
  gateway_retained_prefix ge target source ->forall memory,
  gateway_retained_prefix ge target(gateway_replace_memory source memory).
Proof.
  intro PREFIX;induction PREFIX;intro changed.
  - rewrite gateway_memory_replace_twice;constructor.
  - eapply gateway_prefix_next with(next:=gateway_replace_memory next changed).
    + destruct source;exact H.
    + intro another;rewrite !gateway_memory_replace_twice;apply H0.
    + apply IHPREFIX.
Qed.

Lemma gateway_retained_prefix_transitive ge target middle source :
  gateway_retained_prefix ge middle source ->gateway_retained_prefix ge target middle ->
  gateway_retained_prefix ge target source.
Proof.
  intros PREFIX REST;induction PREFIX.
  - apply gateway_retained_prefix_relocate;exact REST.
  - eapply gateway_prefix_next;[exact H|exact H0|exact IHPREFIX].
Qed.

Theorem actual_negative_retry_loop_prefix ge temporaries number memory :
  temporaries!_count=Some(Vlong(Int64.repr(-1))) ->temporaries!_number=Some(Vint number) ->
  (number=Int.repr 4 \/number=Int.repr 11) ->
  gateway_retained_prefix ge
    (State f_host_transfer transfer_loop transfer_loop_cont empty_env(transfer_retry_values temporaries)memory)
    (State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env temporaries memory).
Proof.
  intros COUNT NUMBER RETRY.
  retry_prefix(State f_host_transfer transfer_retry_sequence(Kseq transfer_after_retry transfer_iteration_cont)
    empty_env temporaries memory).
  { apply unchanged_store_edge,edge_seq. }
  retry_prefix(State f_host_transfer transfer_retry_prefix
    (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env temporaries memory).
  { apply unchanged_store_edge,edge_seq. }
  retry_prefix(State f_host_transfer transfer_errno_sequence
    (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env temporaries memory).
  { apply certified_if_edge with(v:=Vint Int.one)(b:=true);
      [apply actual_negative_count_comparison;exact COUNT|reflexivity]. }
  retry_prefix(State f_host_transfer transfer_errno_first
    (Kseq transfer_errno_second(Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)))
    empty_env temporaries memory).
  { apply unchanged_store_edge,edge_seq. }
  eapply gateway_retained_prefix_transitive.
  - exact(actual_retry_errno_first_prefix ge temporaries number memory NUMBER RETRY).
  - exact(actual_retry_errno_tail_prefix ge temporaries memory).
Qed.

Theorem actual_negative_retry_next_ready (ge:Clight.genv)temporaries number size memory
    stream_block stream_offset symbol :
  temporaries!_count=Some(Vlong(Int64.repr(-1))) ->temporaries!_number=Some(Vint number) ->
  (number=Int.repr 4 \/number=Int.repr 11) ->0<size<=Int64.max_unsigned ->
  temporaries!_size=Some(Vlong(Int64.repr size)) ->
  temporaries!_stream=Some(Vptr stream_block stream_offset) ->temporaries!_sending=Some(Vint Int.zero) ->
  Genv.find_symbol ge _host_ready=Some symbol ->Genv.find_funct_ptr ge symbol=Some(Internal f_host_ready) ->
  gateway_retained_call_path ge(Internal f_host_ready)[Vptr stream_block stream_offset;Vint Int.one]
    (transfer_ready_cont(transfer_retry_values temporaries))
    (State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env temporaries memory).
Proof.
  intros COUNT NUMBER RETRY SIZE LOOK STREAM RECEIVE SYMBOL FUNCTION.
  eapply gateway_prefix_before_call.
  - exact(actual_negative_retry_loop_prefix ge temporaries number memory COUNT NUMBER RETRY).
  - apply actual_positive_transfer_loop_ready_path with(amount:=size)(symbol:=symbol);[exact SIZE| | | |exact SYMBOL|exact FUNCTION];
      unfold transfer_retry_values,transfer_retry_errno_values;rewrite !PTree.gso by discriminate;assumption.
Qed.
