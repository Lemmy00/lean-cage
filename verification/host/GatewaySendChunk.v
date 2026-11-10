(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: The real sending branch bounds the chunk before GIL release. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayCallPath GatewayTransferMath
  GatewayTransferSource GatewayTransferChunk GatewaySendSource GatewayRuntimeABI.
Import ListNotations.
Open Scope Z_scope.

Definition send_ready_zero_values temporaries:=
  PTree.set _t'2(Vint Int.zero)(PTree.set _t'1(Vint(Int.repr 4))temporaries).
Definition send_chunk_temp_values temporaries amount:=
  PTree.set _t'3(Vlong(Int64.repr(transfer_chunk amount)))(send_ready_zero_values temporaries).
Definition send_amount_values temporaries amount:=
  PTree.set _amount(Vlong(Int64.repr(transfer_chunk amount)))(send_chunk_temp_values temporaries amount).
Definition send_save_cont temporaries amount:=
  Kcall(Some _t'4)f_host_transfer empty_env(send_amount_values temporaries amount)
    (Kseq transfer_save_bind(Kseq transfer_after_save transfer_iteration_cont)).

Lemma actual_send_save_thread_call (ge:Clight.genv) temporaries amount memory symbol :
  Genv.find_symbol ge _PyEval_SaveThread=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some gateway_save_thread_definition ->
  store_edge ge(State f_host_transfer transfer_save_call
    (Kseq transfer_save_bind(Kseq transfer_after_save transfer_iteration_cont))empty_env
    (send_amount_values temporaries amount)memory)
    (Callstate gateway_save_thread_definition[](send_save_cont temporaries amount)memory).
Proof.
  intros SYMBOL FUNCTION;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
  - apply no_argument_values.
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Local Ltac send_retain target:=
  eapply gateway_retained_next with(next:=target);[cbn;tauto|intro another|].

Lemma actual_send_ready_zero_save_thread_path (ge:Clight.genv) temporaries amount memory symbol :
  0<=amount<=Int64.max_unsigned ->temporaries!_size=Some(Vlong(Int64.repr amount)) ->
  Genv.find_symbol ge _PyEval_SaveThread=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some gateway_save_thread_definition ->
  gateway_retained_call_path ge gateway_save_thread_definition[](send_save_cont temporaries amount)
    (Returnstate(Vint Int.zero)(transfer_send_ready_cont temporaries)memory).
Proof.
  intros AMOUNT SIZE SYMBOL FUNCTION.
  send_retain(State f_host_transfer Sskip
    (Kseq transfer_ready_test(Kseq transfer_after_ready transfer_iteration_cont))empty_env
    (send_ready_zero_values temporaries)memory).
  { apply unchanged_store_edge,edge_returnstate. }
  send_retain(State f_host_transfer transfer_ready_test(Kseq transfer_after_ready transfer_iteration_cont)
    empty_env(send_ready_zero_values temporaries)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  send_retain(State f_host_transfer Sskip(Kseq transfer_after_ready transfer_iteration_cont)
    empty_env(send_ready_zero_values temporaries)memory).
  { apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
      [apply old_expression_value,value_temp;unfold send_ready_zero_values;apply PTree.gss|reflexivity]. }
  send_retain(State f_host_transfer transfer_after_ready transfer_iteration_cont
    empty_env(send_ready_zero_values temporaries)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  send_retain(State f_host_transfer transfer_chunk_sequence(Kseq transfer_after_chunk transfer_iteration_cont)
    empty_env(send_ready_zero_values temporaries)memory).
  { apply unchanged_store_edge,edge_seq. }
  send_retain(State f_host_transfer transfer_chunk_choice
    (Kseq transfer_chunk_assignment(Kseq transfer_after_chunk transfer_iteration_cont))
    empty_env(send_ready_zero_values temporaries)memory).
  { apply unchanged_store_edge,edge_seq. }
  send_retain(State f_host_transfer(transfer_chunk_set amount)
    (Kseq transfer_chunk_assignment(Kseq transfer_after_chunk transfer_iteration_cont))
    empty_env(send_ready_zero_values temporaries)memory).
  { apply actual_transfer_chunk_choice_edge;[exact AMOUNT|].
    unfold send_ready_zero_values;rewrite !PTree.gso by discriminate;exact SIZE. }
  send_retain(State f_host_transfer Sskip
    (Kseq transfer_chunk_assignment(Kseq transfer_after_chunk transfer_iteration_cont))
    empty_env(send_chunk_temp_values temporaries amount)memory).
  { apply certified_set_edge;apply actual_transfer_chunk_expression;[exact AMOUNT|].
    unfold send_ready_zero_values;rewrite !PTree.gso by discriminate;exact SIZE. }
  send_retain(State f_host_transfer transfer_chunk_assignment(Kseq transfer_after_chunk transfer_iteration_cont)
    empty_env(send_chunk_temp_values temporaries amount)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  send_retain(State f_host_transfer Sskip(Kseq transfer_after_chunk transfer_iteration_cont)
    empty_env(send_amount_values temporaries amount)memory).
  { apply certified_set_edge;apply old_expression_value,value_temp;
      unfold send_chunk_temp_values;apply PTree.gss. }
  send_retain(State f_host_transfer transfer_after_chunk transfer_iteration_cont
    empty_env(send_amount_values temporaries amount)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  send_retain(State f_host_transfer transfer_save_sequence(Kseq transfer_after_save transfer_iteration_cont)
    empty_env(send_amount_values temporaries amount)memory).
  { apply unchanged_store_edge,edge_seq. }
  send_retain(State f_host_transfer transfer_save_call
    (Kseq transfer_save_bind(Kseq transfer_after_save transfer_iteration_cont))
    empty_env(send_amount_values temporaries amount)memory).
  { apply unchanged_store_edge,edge_seq. }
  send_retain(Callstate gateway_save_thread_definition[](send_save_cont temporaries amount)memory).
  { apply actual_send_save_thread_call with(symbol:=symbol);assumption. }
  constructor.
Qed.
