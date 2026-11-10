(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Exact source pointers and bounded chunk supply the actual receive
   call. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayGuardedCuts GatewayTransferSource
  GatewayTransferChunk GatewayTransferMath GatewayRuntimeABI GatewayStreamInterface GatewayStreamLayout GatewayStreamAccess.
Import ListNotations.
Open Scope Z_scope.

Definition transfer_io_sequence:=match transfer_after_save with Ssequence io _=>io|_=>Sskip end.
Definition transfer_after_io:=match transfer_after_save with Ssequence _ rest=>rest|_=>Sskip end.
Definition transfer_io_choice:=match transfer_io_sequence with Ssequence choice _=>choice|_=>Sskip end.
Definition transfer_count_assignment:=match transfer_io_sequence with Ssequence _ assign=>assign|_=>Sskip end.
Definition transfer_receive_sequence:=match transfer_io_choice with Sifthenelse _ _ receive=>receive|_=>Sskip end.
Definition transfer_receive_prefix:=match transfer_receive_sequence with Ssequence prefix _=>prefix|_=>Sskip end.
Definition transfer_receive_cast:=match transfer_receive_sequence with Ssequence _ cast=>cast|_=>Sskip end.
Definition transfer_receive_descriptor:=match transfer_receive_prefix with Ssequence descriptor _=>descriptor|_=>Sskip end.
Definition transfer_receive_call:=match transfer_receive_prefix with Ssequence _ call=>call|_=>Sskip end.
Definition transfer_saved_values temporaries amount saved:=
  PTree.set _saved saved(PTree.set _t'4 saved(transfer_amount_values temporaries amount)).
Definition transfer_receive_values temporaries amount saved descriptor:=
  PTree.set _t'13(Vint descriptor)(transfer_saved_values temporaries amount saved).
Definition transfer_receive_cont temporaries amount saved descriptor:=
  Kcall(Some _t'7)f_host_transfer empty_env(transfer_receive_values temporaries amount saved descriptor)
    (Kseq transfer_receive_cast(Kseq transfer_count_assignment(Kseq transfer_after_io transfer_iteration_cont))).

Lemma actual_transfer_receive_call (ge:Clight.genv)temporaries amount saved descriptor data_block data_offset memory symbol :
  temporaries!_cursor=Some(Vptr data_block data_offset) ->
  Genv.find_symbol ge _recv=Some symbol ->Genv.find_funct_ptr ge symbol=Some gateway_receive_definition ->
  store_edge ge(State f_host_transfer transfer_receive_call
    (Kseq transfer_receive_cast(Kseq transfer_count_assignment(Kseq transfer_after_io transfer_iteration_cont)))empty_env
    (transfer_receive_values temporaries amount saved descriptor)memory)
    (Callstate gateway_receive_definition
      [Vint descriptor;Vptr data_block data_offset;Vlong(Int64.repr(transfer_chunk amount));Vint Int.zero]
      (transfer_receive_cont temporaries amount saved descriptor)memory).
Proof.
  intros CURSOR SYMBOL FUNCTION;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vint descriptor).
    + apply old_expression_value,value_temp;unfold transfer_receive_values;apply PTree.gss.
    + reflexivity.
    + eapply cons_argument_values with(v:=Vptr data_block data_offset).
      * apply old_expression_value,value_temp.
        unfold transfer_receive_values,transfer_saved_values,transfer_amount_values,
          transfer_chunk_temp_values,transfer_ready_zero_values.
        rewrite !PTree.gso by discriminate;exact CURSOR.
      * reflexivity.
      * eapply cons_argument_values with(v:=Vlong(Int64.repr(transfer_chunk amount))).
        -- apply old_expression_value,value_temp.
           unfold transfer_receive_values,transfer_saved_values,transfer_amount_values.
           rewrite !PTree.gso by discriminate;apply PTree.gss.
        -- reflexivity.
        -- eapply cons_argument_values with(v:=Vint Int.zero).
           ++ apply old_expression_value;constructor.
           ++ reflexivity.
           ++ apply no_argument_values.
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Local Ltac receive_retain target:=
  eapply gateway_guarded_next with(next:=target);[cbn;tauto|intros another CELLS|].

Lemma actual_saved_thread_receive_path (ge:Clight.genv)temporaries amount saved initial
    stream_block stream_offset data_block data_offset memory symbol :
  temporaries!_stream=Some(Vptr stream_block stream_offset) ->temporaries!_sending=Some(Vint Int.zero) ->
  temporaries!_cursor=Some(Vptr data_block data_offset) ->stream_member_layout ge _descriptor 0 ->
  Genv.find_symbol ge _recv=Some symbol ->Genv.find_funct_ptr ge symbol=Some gateway_receive_definition ->
  gateway_guarded_retained_path ge(fun memory=>gateway_stream_memory memory stream_block stream_offset initial)
    gateway_receive_definition
    [Vint(stream_descriptor initial);Vptr data_block data_offset;Vlong(Int64.repr(transfer_chunk amount));Vint Int.zero]
    (transfer_receive_cont temporaries amount saved(stream_descriptor initial))
    (Returnstate saved(transfer_save_cont temporaries amount)memory).
Proof.
  intros STREAM RECEIVE CURSOR LAYOUT SYMBOL FUNCTION.
  receive_retain(State f_host_transfer Sskip(Kseq transfer_save_bind(Kseq transfer_after_save transfer_iteration_cont))
    empty_env(PTree.set _t'4 saved(transfer_amount_values temporaries amount))memory).
  { apply unchanged_store_edge,edge_returnstate. }
  receive_retain(State f_host_transfer transfer_save_bind(Kseq transfer_after_save transfer_iteration_cont)
    empty_env(PTree.set _t'4 saved(transfer_amount_values temporaries amount))memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  receive_retain(State f_host_transfer Sskip(Kseq transfer_after_save transfer_iteration_cont)
    empty_env(transfer_saved_values temporaries amount saved)memory).
  { apply certified_set_edge;apply old_expression_value,value_temp;apply PTree.gss. }
  receive_retain(State f_host_transfer transfer_after_save transfer_iteration_cont
    empty_env(transfer_saved_values temporaries amount saved)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  receive_retain(State f_host_transfer transfer_io_sequence(Kseq transfer_after_io transfer_iteration_cont)
    empty_env(transfer_saved_values temporaries amount saved)memory).
  { apply unchanged_store_edge,edge_seq. }
  receive_retain(State f_host_transfer transfer_io_choice(Kseq transfer_count_assignment(Kseq transfer_after_io transfer_iteration_cont))
    empty_env(transfer_saved_values temporaries amount saved)memory).
  { apply unchanged_store_edge,edge_seq. }
  receive_retain(State f_host_transfer transfer_receive_sequence(Kseq transfer_count_assignment(Kseq transfer_after_io transfer_iteration_cont))
    empty_env(transfer_saved_values temporaries amount saved)memory).
  { apply certified_if_edge with(v:=Vint Int.zero)(b:=false).
    - apply old_expression_value,value_temp.
      unfold transfer_saved_values,transfer_amount_values,transfer_chunk_temp_values,transfer_ready_zero_values.
      rewrite !PTree.gso by discriminate;exact RECEIVE.
    - reflexivity. }
  receive_retain(State f_host_transfer transfer_receive_prefix
    (Kseq transfer_receive_cast(Kseq transfer_count_assignment(Kseq transfer_after_io transfer_iteration_cont)))
    empty_env(transfer_saved_values temporaries amount saved)memory).
  { apply unchanged_store_edge,edge_seq. }
  receive_retain(State f_host_transfer transfer_receive_descriptor
    (Kseq transfer_receive_call(Kseq transfer_receive_cast(Kseq transfer_count_assignment(Kseq transfer_after_io transfer_iteration_cont))))
    empty_env(transfer_saved_values temporaries amount saved)memory).
  { apply unchanged_store_edge,edge_seq. }
  receive_retain(State f_host_transfer Sskip
    (Kseq transfer_receive_call(Kseq transfer_receive_cast(Kseq transfer_count_assignment(Kseq transfer_after_io transfer_iteration_cont))))
    empty_env(transfer_receive_values temporaries amount saved(stream_descriptor initial))memory).
  { apply certified_set_edge.
    eapply actual_stream_member_read with(block:=stream_block)(offset:=stream_offset)(delta:=0)(chunk:=Mint32).
    - unfold transfer_saved_values,transfer_amount_values,transfer_chunk_temp_values,transfer_ready_zero_values.
      rewrite !PTree.gso by discriminate;exact STREAM.
    - exact LAYOUT.
    - reflexivity.
    - exact(proj1 CELLS). }
  receive_retain(State f_host_transfer transfer_receive_call
    (Kseq transfer_receive_cast(Kseq transfer_count_assignment(Kseq transfer_after_io transfer_iteration_cont)))
    empty_env(transfer_receive_values temporaries amount saved(stream_descriptor initial))memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  receive_retain(Callstate gateway_receive_definition
    [Vint(stream_descriptor initial);Vptr data_block data_offset;Vlong(Int64.repr(transfer_chunk amount));Vint Int.zero]
    (transfer_receive_cont temporaries amount saved(stream_descriptor initial))memory).
  { apply actual_transfer_receive_call with(symbol:=symbol);assumption. }
  constructor.
Qed.
