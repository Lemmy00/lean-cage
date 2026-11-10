(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: The actual sending branch uses the retained data span. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayGuardedCuts GatewayTransferSource
  GatewayTransferChunk GatewayTransferReceive GatewaySendSource GatewaySendChunk GatewayTransferMath
  GatewayRuntimeABI GatewayStreamInterface GatewayStreamLayout GatewayStreamAccess.
Import ListNotations.
Open Scope Z_scope.

Definition send_transfer_sequence:=match transfer_io_choice with Sifthenelse _ sending _=>sending|_=>Sskip end.
Definition send_transfer_prefix:=match send_transfer_sequence with Ssequence prefix _=>prefix|_=>Sskip end.
Definition send_transfer_cast:=match send_transfer_sequence with Ssequence _ cast=>cast|_=>Sskip end.
Definition send_transfer_descriptor:=match send_transfer_prefix with Ssequence descriptor _=>descriptor|_=>Sskip end.
Definition send_transfer_call:=match send_transfer_prefix with Ssequence _ call=>call|_=>Sskip end.
Definition send_saved_values temporaries amount saved:=
  PTree.set _saved saved(PTree.set _t'4 saved(send_amount_values temporaries amount)).
Definition send_transfer_values temporaries amount saved descriptor:=
  PTree.set _t'14(Vint descriptor)(send_saved_values temporaries amount saved).
Definition send_transfer_cont temporaries amount saved descriptor:=
  Kcall(Some _t'6)f_host_transfer empty_env(send_transfer_values temporaries amount saved descriptor)
    (Kseq send_transfer_cast(Kseq transfer_count_assignment(Kseq transfer_after_io transfer_iteration_cont))).

Lemma actual_send_transfer_call (ge:Clight.genv)temporaries amount saved descriptor data_block data_offset memory symbol :
  temporaries!_cursor=Some(Vptr data_block data_offset) ->
  Genv.find_symbol ge _send=Some symbol ->Genv.find_funct_ptr ge symbol=Some gateway_send_definition ->
  store_edge ge(State f_host_transfer send_transfer_call
    (Kseq send_transfer_cast(Kseq transfer_count_assignment(Kseq transfer_after_io transfer_iteration_cont)))empty_env
    (send_transfer_values temporaries amount saved descriptor)memory)
    (Callstate gateway_send_definition
      [Vint descriptor;Vptr data_block data_offset;Vlong(Int64.repr(transfer_chunk amount));Vint(Int.repr 16384)]
      (send_transfer_cont temporaries amount saved descriptor)memory).
Proof.
  intros CURSOR SYMBOL FUNCTION;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vint descriptor).
    + apply old_expression_value,value_temp;unfold send_transfer_values;apply PTree.gss.
    + reflexivity.
    + eapply cons_argument_values with(v:=Vptr data_block data_offset).
      * apply old_expression_value,value_temp.
        unfold send_transfer_values,send_saved_values,send_amount_values,
          send_chunk_temp_values,send_ready_zero_values.
        rewrite !PTree.gso by discriminate;exact CURSOR.
      * reflexivity.
      * eapply cons_argument_values with(v:=Vlong(Int64.repr(transfer_chunk amount))).
        -- apply old_expression_value,value_temp.
           unfold send_transfer_values,send_saved_values,send_amount_values.
           rewrite !PTree.gso by discriminate;apply PTree.gss.
        -- reflexivity.
        -- eapply cons_argument_values with(v:=Vint(Int.repr 16384)).
           ++ apply old_expression_value;constructor.
           ++ reflexivity.
           ++ apply no_argument_values.
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Local Ltac send_retain target:=
  eapply gateway_guarded_next with(next:=target);[cbn;tauto|intros another CELLS|].

Lemma actual_saved_thread_send_path (ge:Clight.genv)temporaries amount saved initial
    stream_block stream_offset data_block data_offset memory symbol :
  temporaries!_stream=Some(Vptr stream_block stream_offset) ->temporaries!_sending=Some(Vint Int.one) ->
  temporaries!_cursor=Some(Vptr data_block data_offset) ->stream_member_layout ge _descriptor 0 ->
  Genv.find_symbol ge _send=Some symbol ->Genv.find_funct_ptr ge symbol=Some gateway_send_definition ->
  gateway_guarded_retained_path ge(fun memory=>gateway_stream_memory memory stream_block stream_offset initial)
    gateway_send_definition
    [Vint(stream_descriptor initial);Vptr data_block data_offset;Vlong(Int64.repr(transfer_chunk amount));Vint(Int.repr 16384)]
    (send_transfer_cont temporaries amount saved(stream_descriptor initial))
    (Returnstate saved(send_save_cont temporaries amount)memory).
Proof.
  intros STREAM SENDING CURSOR LAYOUT SYMBOL FUNCTION.
  send_retain(State f_host_transfer Sskip(Kseq transfer_save_bind(Kseq transfer_after_save transfer_iteration_cont))
    empty_env(PTree.set _t'4 saved(send_amount_values temporaries amount))memory).
  { apply unchanged_store_edge,edge_returnstate. }
  send_retain(State f_host_transfer transfer_save_bind(Kseq transfer_after_save transfer_iteration_cont)
    empty_env(PTree.set _t'4 saved(send_amount_values temporaries amount))memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  send_retain(State f_host_transfer Sskip(Kseq transfer_after_save transfer_iteration_cont)
    empty_env(send_saved_values temporaries amount saved)memory).
  { apply certified_set_edge;apply old_expression_value,value_temp;apply PTree.gss. }
  send_retain(State f_host_transfer transfer_after_save transfer_iteration_cont
    empty_env(send_saved_values temporaries amount saved)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  send_retain(State f_host_transfer transfer_io_sequence(Kseq transfer_after_io transfer_iteration_cont)
    empty_env(send_saved_values temporaries amount saved)memory).
  { apply unchanged_store_edge,edge_seq. }
  send_retain(State f_host_transfer transfer_io_choice(Kseq transfer_count_assignment(Kseq transfer_after_io transfer_iteration_cont))
    empty_env(send_saved_values temporaries amount saved)memory).
  { apply unchanged_store_edge,edge_seq. }
  send_retain(State f_host_transfer send_transfer_sequence(Kseq transfer_count_assignment(Kseq transfer_after_io transfer_iteration_cont))
    empty_env(send_saved_values temporaries amount saved)memory).
  { apply certified_if_edge with(v:=Vint Int.one)(b:=true).
    - apply old_expression_value,value_temp.
      unfold send_saved_values,send_amount_values,send_chunk_temp_values,send_ready_zero_values.
      rewrite !PTree.gso by discriminate;exact SENDING.
    - reflexivity. }
  send_retain(State f_host_transfer send_transfer_prefix
    (Kseq send_transfer_cast(Kseq transfer_count_assignment(Kseq transfer_after_io transfer_iteration_cont)))
    empty_env(send_saved_values temporaries amount saved)memory).
  { apply unchanged_store_edge,edge_seq. }
  send_retain(State f_host_transfer send_transfer_descriptor
    (Kseq send_transfer_call(Kseq send_transfer_cast(Kseq transfer_count_assignment(Kseq transfer_after_io transfer_iteration_cont))))
    empty_env(send_saved_values temporaries amount saved)memory).
  { apply unchanged_store_edge,edge_seq. }
  send_retain(State f_host_transfer Sskip
    (Kseq send_transfer_call(Kseq send_transfer_cast(Kseq transfer_count_assignment(Kseq transfer_after_io transfer_iteration_cont))))
    empty_env(send_transfer_values temporaries amount saved(stream_descriptor initial))memory).
  { apply certified_set_edge.
    eapply actual_stream_member_read with(block:=stream_block)(offset:=stream_offset)(delta:=0)(chunk:=Mint32).
    - unfold send_saved_values,send_amount_values,send_chunk_temp_values,send_ready_zero_values.
      rewrite !PTree.gso by discriminate;exact STREAM.
    - exact LAYOUT.
    - reflexivity.
    - exact(proj1 CELLS). }
  send_retain(State f_host_transfer send_transfer_call
    (Kseq send_transfer_cast(Kseq transfer_count_assignment(Kseq transfer_after_io transfer_iteration_cont)))
    empty_env(send_transfer_values temporaries amount saved(stream_descriptor initial))memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  send_retain(Callstate gateway_send_definition
    [Vint(stream_descriptor initial);Vptr data_block data_offset;Vlong(Int64.repr(transfer_chunk amount));Vint(Int.repr 16384)]
    (send_transfer_cont temporaries amount saved(stream_descriptor initial))memory).
  { apply actual_send_transfer_call with(symbol:=symbol);assumption. }
  constructor.
Qed.
