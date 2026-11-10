(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Accepted counts advance the real cursor and return to the source loop. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPure GatewayCallPath GatewayControlPaths GatewayTransferSource
  GatewayTransferErrno GatewayTransferMath GatewayTransferProgressMath GatewayTransferLoop.
Import ListNotations.
Open Scope Z_scope.

Definition transfer_retry_sequence:=match transfer_after_restore with Ssequence retry _=>retry|_=>Sskip end.
Definition transfer_after_retry:=match transfer_after_restore with Ssequence _ rest=>rest|_=>Sskip end.
Definition transfer_retry_prefix:=match transfer_retry_sequence with Ssequence prefix _=>prefix|_=>Sskip end.
Definition transfer_retry_test:=match transfer_retry_sequence with Ssequence _ test=>test|_=>Sskip end.
Definition transfer_count_sequence:=match transfer_after_retry with Ssequence count _=>count|_=>Sskip end.
Definition transfer_advance_sequence:=match transfer_after_retry with Ssequence _ advance=>advance|_=>Sskip end.
Definition transfer_count_choice:=match transfer_count_sequence with Ssequence choice _=>choice|_=>Sskip end.
Definition transfer_count_test:=match transfer_count_sequence with Ssequence _ test=>test|_=>Sskip end.
Definition transfer_count_cast:=match transfer_count_choice with Sifthenelse _ _ cast=>cast|_=>Sskip end.
Definition transfer_cursor_assignment:=match transfer_advance_sequence with Ssequence cursor _=>cursor|_=>Sskip end.
Definition transfer_size_assignment:=match transfer_advance_sequence with Ssequence _ size=>size|_=>Sskip end.
Definition transfer_positive_retry_values temporaries:=PTree.set _t'9(Vint Int.zero)temporaries.
Definition transfer_positive_count_values temporaries:=PTree.set _t'11(Vint Int.zero)(transfer_positive_retry_values temporaries).
Definition transfer_advanced_cursor_values temporaries count block offset:=
  PTree.set _cursor(Vptr block(Ptrofs.add offset(Ptrofs.repr count)))(transfer_positive_count_values temporaries).
Definition transfer_advanced_values temporaries size count block offset:=
  PTree.set _size(Vlong(Int64.repr(size-count)))(transfer_advanced_cursor_values temporaries count block offset).

Local Ltac progress_prefix target:=
  eapply gateway_prefix_next with(next:=target);[cbn;tauto|intro another|].

Theorem actual_positive_count_loop_prefix ge temporaries size count block offset memory :
  0<size<=Int64.max_unsigned ->0<count<=transfer_chunk size ->
  temporaries!_count=Some(Vlong(Int64.repr count)) ->
  temporaries!_amount=Some(Vlong(Int64.repr(transfer_chunk size))) ->
  temporaries!_cursor=Some(Vptr block offset) ->temporaries!_size=Some(Vlong(Int64.repr size)) ->
  gateway_retained_prefix ge
    (State f_host_transfer transfer_loop transfer_loop_cont empty_env
      (transfer_advanced_values temporaries size count block offset)memory)
    (State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env temporaries memory).
Proof.
  intros SIZE COUNT COUNT_LOOK AMOUNT_LOOK CURSOR_LOOK SIZE_LOOK.
  pose proof(transfer_chunk_bounds size ltac:(lia))as[CHUNK BELOW].
  assert(SMALL:0<count<=65536)by lia.
  progress_prefix(State f_host_transfer transfer_retry_sequence(Kseq transfer_after_retry transfer_iteration_cont)
    empty_env temporaries memory).
  { apply unchanged_store_edge,edge_seq. }
  progress_prefix(State f_host_transfer transfer_retry_prefix
    (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env temporaries memory).
  { apply unchanged_store_edge,edge_seq. }
  progress_prefix(State f_host_transfer(Sset _t'9(Econst_int Int.zero tint))
    (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env temporaries memory).
  { apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
      [apply actual_positive_count_not_negative with(count:=count);[exact SMALL|exact COUNT_LOOK]|reflexivity]. }
  progress_prefix(State f_host_transfer Sskip
    (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))
    empty_env(transfer_positive_retry_values temporaries)memory).
  { apply certified_set_edge;apply old_expression_value;constructor. }
  progress_prefix(State f_host_transfer transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)
    empty_env(transfer_positive_retry_values temporaries)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  progress_prefix(State f_host_transfer Sskip(Kseq transfer_after_retry transfer_iteration_cont)
    empty_env(transfer_positive_retry_values temporaries)memory).
  { apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
      [apply old_expression_value,value_temp;apply PTree.gss|reflexivity]. }
  progress_prefix(State f_host_transfer transfer_after_retry transfer_iteration_cont
    empty_env(transfer_positive_retry_values temporaries)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  progress_prefix(State f_host_transfer transfer_count_sequence(Kseq transfer_advance_sequence transfer_iteration_cont)
    empty_env(transfer_positive_retry_values temporaries)memory).
  { apply unchanged_store_edge,edge_seq. }
  progress_prefix(State f_host_transfer transfer_count_choice
    (Kseq transfer_count_test(Kseq transfer_advance_sequence transfer_iteration_cont))
    empty_env(transfer_positive_retry_values temporaries)memory).
  { apply unchanged_store_edge,edge_seq. }
  progress_prefix(State f_host_transfer transfer_count_cast
    (Kseq transfer_count_test(Kseq transfer_advance_sequence transfer_iteration_cont))
    empty_env(transfer_positive_retry_values temporaries)memory).
  { apply certified_if_edge with(v:=Vint Int.zero)(b:=false).
    - apply actual_positive_count_not_zero with(count:=count);[exact SMALL|].
      unfold transfer_positive_retry_values;rewrite PTree.gso by discriminate;exact COUNT_LOOK.
    - reflexivity. }
  progress_prefix(State f_host_transfer Sskip
    (Kseq transfer_count_test(Kseq transfer_advance_sequence transfer_iteration_cont))
    empty_env(transfer_positive_count_values temporaries)memory).
  { apply certified_set_edge;apply actual_count_inside_chunk with(count:=count)(amount:=transfer_chunk size);[exact COUNT|lia| |];
      unfold transfer_positive_retry_values;rewrite PTree.gso by discriminate;assumption. }
  progress_prefix(State f_host_transfer transfer_count_test(Kseq transfer_advance_sequence transfer_iteration_cont)
    empty_env(transfer_positive_count_values temporaries)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  progress_prefix(State f_host_transfer Sskip(Kseq transfer_advance_sequence transfer_iteration_cont)
    empty_env(transfer_positive_count_values temporaries)memory).
  { apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
      [apply old_expression_value,value_temp;unfold transfer_positive_count_values;apply PTree.gss|reflexivity]. }
  progress_prefix(State f_host_transfer transfer_advance_sequence transfer_iteration_cont
    empty_env(transfer_positive_count_values temporaries)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  progress_prefix(State f_host_transfer transfer_cursor_assignment(Kseq transfer_size_assignment transfer_iteration_cont)
    empty_env(transfer_positive_count_values temporaries)memory).
  { apply unchanged_store_edge,edge_seq. }
  progress_prefix(State f_host_transfer Sskip(Kseq transfer_size_assignment transfer_iteration_cont)
    empty_env(transfer_advanced_cursor_values temporaries count block offset)memory).
  { apply certified_set_edge;apply actual_cursor_advance with(count:=count)(block:=block)(offset:=offset);[exact SMALL| |];
      unfold transfer_positive_count_values,transfer_positive_retry_values;
      rewrite !PTree.gso by discriminate;assumption. }
  progress_prefix(State f_host_transfer transfer_size_assignment transfer_iteration_cont
    empty_env(transfer_advanced_cursor_values temporaries count block offset)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  progress_prefix(State f_host_transfer Sskip transfer_iteration_cont empty_env
    (transfer_advanced_values temporaries size count block offset)memory).
  { apply certified_set_edge;apply actual_size_decrement with(size:=size)(count:=count);[lia|lia| |];
      unfold transfer_advanced_cursor_values,transfer_positive_count_values,transfer_positive_retry_values;
      rewrite !PTree.gso by discriminate;assumption. }
  progress_prefix(State f_host_transfer Sskip(Kloop2 transfer_loop_first Sskip transfer_loop_cont)empty_env
    (transfer_advanced_values temporaries size count block offset)memory).
  { apply unchanged_store_edge,edge_skip_loop1. }
  progress_prefix(State f_host_transfer transfer_loop transfer_loop_cont empty_env
    (transfer_advanced_values temporaries size count block offset)memory).
  { apply unchanged_store_edge,edge_skip_loop2. }
  change(gateway_retained_prefix ge
    (State f_host_transfer transfer_loop transfer_loop_cont empty_env
      (transfer_advanced_values temporaries size count block offset)memory)
    (gateway_replace_memory(State f_host_transfer transfer_loop transfer_loop_cont empty_env
      (transfer_advanced_values temporaries size count block offset)memory)memory)).
  constructor.
Qed.

Theorem actual_positive_count_last_path ge temporaries size count block offset memory :
  0<size<=Int64.max_unsigned ->0<count<=transfer_chunk size ->size-count=0 ->
  temporaries!_count=Some(Vlong(Int64.repr count)) ->
  temporaries!_amount=Some(Vlong(Int64.repr(transfer_chunk size))) ->
  temporaries!_cursor=Some(Vptr block offset) ->temporaries!_size=Some(Vlong(Int64.repr size)) ->
  gateway_pure_path ge(State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env temporaries memory)
    (Vint Int.zero).
Proof.
  intros SIZE COUNT FINISHED COUNT_LOOK AMOUNT_LOOK CURSOR_LOOK SIZE_LOOK.
  eapply gateway_prefix_before_return.
  - exact(actual_positive_count_loop_prefix ge temporaries size count block offset memory
      SIZE COUNT COUNT_LOOK AMOUNT_LOOK CURSOR_LOOK SIZE_LOOK).
  - apply actual_zero_transfer_loop_path.
    unfold transfer_advanced_values;rewrite PTree.gss,FINISHED;reflexivity.
Qed.

Theorem actual_positive_count_next_ready (ge:Clight.genv)temporaries size count block offset memory
    stream_block stream_offset symbol :
  0<size<=Int64.max_unsigned ->0<count<=transfer_chunk size ->count<size ->
  temporaries!_count=Some(Vlong(Int64.repr count)) ->
  temporaries!_amount=Some(Vlong(Int64.repr(transfer_chunk size))) ->
  temporaries!_cursor=Some(Vptr block offset) ->temporaries!_size=Some(Vlong(Int64.repr size)) ->
  temporaries!_stream=Some(Vptr stream_block stream_offset) ->temporaries!_sending=Some(Vint Int.zero) ->
  Genv.find_symbol ge _host_ready=Some symbol ->Genv.find_funct_ptr ge symbol=Some(Internal f_host_ready) ->
  gateway_retained_call_path ge(Internal f_host_ready)[Vptr stream_block stream_offset;Vint Int.one]
    (transfer_ready_cont(transfer_advanced_values temporaries size count block offset))
    (State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env temporaries memory).
Proof.
  intros SIZE COUNT MORE COUNT_LOOK AMOUNT_LOOK CURSOR_LOOK SIZE_LOOK STREAM RECEIVE SYMBOL FUNCTION.
  eapply gateway_prefix_before_call.
  - exact(actual_positive_count_loop_prefix ge temporaries size count block offset memory
      SIZE COUNT COUNT_LOOK AMOUNT_LOOK CURSOR_LOOK SIZE_LOOK).
  - apply actual_positive_transfer_loop_ready_path with(amount:=size-count)(symbol:=symbol).
    + lia.
    + unfold transfer_advanced_values;apply PTree.gss.
    + unfold transfer_advanced_values,transfer_advanced_cursor_values,
        transfer_positive_count_values,transfer_positive_retry_values.
      rewrite !PTree.gso by discriminate;exact STREAM.
    + unfold transfer_advanced_values,transfer_advanced_cursor_values,
        transfer_positive_count_values,transfer_positive_retry_values.
      rewrite !PTree.gso by discriminate;exact RECEIVE.
    + exact SYMBOL.
    + exact FUNCTION.
Qed.
