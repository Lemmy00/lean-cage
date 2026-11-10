(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: The actual source bounds each chunk before releasing the GIL. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayCallPath GatewayTransferMath
  GatewayTransferSource GatewayRuntimeABI.
Import ListNotations.
Open Scope Z_scope.

Definition transfer_chunk_sequence:=match transfer_after_ready with Ssequence chunk _=>chunk|_=>Sskip end.
Definition transfer_after_chunk:=match transfer_after_ready with Ssequence _ rest=>rest|_=>Sskip end.
Definition transfer_chunk_choice:=match transfer_chunk_sequence with Ssequence choice _=>choice|_=>Sskip end.
Definition transfer_chunk_assignment:=match transfer_chunk_sequence with Ssequence _ assign=>assign|_=>Sskip end.
Definition transfer_save_sequence:=match transfer_after_chunk with Ssequence save _=>save|_=>Sskip end.
Definition transfer_after_save:=match transfer_after_chunk with Ssequence _ rest=>rest|_=>Sskip end.
Definition transfer_save_call:=match transfer_save_sequence with Ssequence call _=>call|_=>Sskip end.
Definition transfer_save_bind:=match transfer_save_sequence with Ssequence _ bind=>bind|_=>Sskip end.
Definition transfer_ready_zero_values temporaries:=
  PTree.set _t'2(Vint Int.zero)(PTree.set _t'1(Vint Int.one)temporaries).
Definition transfer_chunk_temp_values temporaries amount:=
  PTree.set _t'3(Vlong(Int64.repr(transfer_chunk amount)))(transfer_ready_zero_values temporaries).
Definition transfer_amount_values temporaries amount:=
  PTree.set _amount(Vlong(Int64.repr(transfer_chunk amount)))(transfer_chunk_temp_values temporaries amount).
Definition transfer_save_cont temporaries amount:=
  Kcall(Some _t'4)f_host_transfer empty_env(transfer_amount_values temporaries amount)
    (Kseq transfer_save_bind(Kseq transfer_after_save transfer_iteration_cont)).

Definition transfer_chunk_expression amount:=if zlt 65536 amount then
  Ecast(Econst_int(Int.repr 65536)tint)tulong else
  Ecast(Ecast(Etempvar _size tulong)tulong)tulong.
Definition transfer_chunk_set amount:=Sset _t'3(transfer_chunk_expression amount).

Lemma actual_transfer_chunk_expression ge temporaries memory amount :
  0<=amount<=Int64.max_unsigned ->temporaries!_size=Some(Vlong(Int64.repr amount)) ->
  expression_value ge empty_env temporaries memory(transfer_chunk_expression amount)
    (Vlong(Int64.repr(transfer_chunk amount))).
Proof.
  intros AMOUNT SIZE;unfold transfer_chunk_expression;rewrite transfer_chunk_cases.
  destruct(zlt 65536 amount).
  - apply cast_expression_value with(v:=Vint(Int.repr 65536));[apply old_expression_value;constructor|reflexivity].
  - apply cast_expression_value with(v:=Vlong(Int64.repr amount));[|reflexivity].
    apply cast_expression_value with(v:=Vlong(Int64.repr amount));[apply old_expression_value,value_temp;exact SIZE|reflexivity].
Qed.

Lemma actual_transfer_chunk_choice_edge ge temporaries memory amount continuation :
  0<=amount<=Int64.max_unsigned ->temporaries!_size=Some(Vlong(Int64.repr amount)) ->
  store_edge ge(State f_host_transfer transfer_chunk_choice continuation empty_env temporaries memory)
    (State f_host_transfer(transfer_chunk_set amount)continuation empty_env temporaries memory).
Proof.
  intros AMOUNT SIZE;unfold transfer_chunk_set,transfer_chunk_expression.
  destruct(zlt 65536 amount)as[LARGE|SMALL].
  - apply certified_if_edge with(v:=Vint Int.one)(b:=true).
    + pose proof(actual_transfer_chunk_comparison ge empty_env temporaries memory amount AMOUNT SIZE)as VALUE.
      destruct(zlt 65536 amount);[exact VALUE|lia].
    + reflexivity.
  - apply certified_if_edge with(v:=Vint Int.zero)(b:=false).
    + pose proof(actual_transfer_chunk_comparison ge empty_env temporaries memory amount AMOUNT SIZE)as VALUE.
      destruct(zlt 65536 amount);[lia|exact VALUE].
    + reflexivity.
Qed.

Lemma actual_transfer_save_thread_call (ge:Clight.genv) temporaries amount memory symbol :
  Genv.find_symbol ge _PyEval_SaveThread=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some gateway_save_thread_definition ->
  store_edge ge(State f_host_transfer transfer_save_call
    (Kseq transfer_save_bind(Kseq transfer_after_save transfer_iteration_cont))empty_env
    (transfer_amount_values temporaries amount)memory)
    (Callstate gateway_save_thread_definition[](transfer_save_cont temporaries amount)memory).
Proof.
  intros SYMBOL FUNCTION;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
  - apply no_argument_values.
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Local Ltac transfer_retain target:=
  eapply gateway_retained_next with(next:=target);[cbn;tauto|intro another|].

Lemma actual_ready_zero_save_thread_path (ge:Clight.genv) temporaries amount memory symbol :
  0<=amount<=Int64.max_unsigned ->temporaries!_size=Some(Vlong(Int64.repr amount)) ->
  Genv.find_symbol ge _PyEval_SaveThread=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some gateway_save_thread_definition ->
  gateway_retained_call_path ge gateway_save_thread_definition[](transfer_save_cont temporaries amount)
    (Returnstate(Vint Int.zero)(transfer_ready_cont temporaries)memory).
Proof.
  intros AMOUNT SIZE SYMBOL FUNCTION.
  transfer_retain(State f_host_transfer Sskip
    (Kseq transfer_ready_test(Kseq transfer_after_ready transfer_iteration_cont))empty_env
    (transfer_ready_zero_values temporaries)memory).
  { apply unchanged_store_edge,edge_returnstate. }
  transfer_retain(State f_host_transfer transfer_ready_test(Kseq transfer_after_ready transfer_iteration_cont)
    empty_env(transfer_ready_zero_values temporaries)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  transfer_retain(State f_host_transfer Sskip(Kseq transfer_after_ready transfer_iteration_cont)
    empty_env(transfer_ready_zero_values temporaries)memory).
  { apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
      [apply old_expression_value,value_temp;unfold transfer_ready_zero_values;apply PTree.gss|reflexivity]. }
  transfer_retain(State f_host_transfer transfer_after_ready transfer_iteration_cont
    empty_env(transfer_ready_zero_values temporaries)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  transfer_retain(State f_host_transfer transfer_chunk_sequence(Kseq transfer_after_chunk transfer_iteration_cont)
    empty_env(transfer_ready_zero_values temporaries)memory).
  { apply unchanged_store_edge,edge_seq. }
  transfer_retain(State f_host_transfer transfer_chunk_choice
    (Kseq transfer_chunk_assignment(Kseq transfer_after_chunk transfer_iteration_cont))
    empty_env(transfer_ready_zero_values temporaries)memory).
  { apply unchanged_store_edge,edge_seq. }
  transfer_retain(State f_host_transfer(transfer_chunk_set amount)
    (Kseq transfer_chunk_assignment(Kseq transfer_after_chunk transfer_iteration_cont))
    empty_env(transfer_ready_zero_values temporaries)memory).
  { apply actual_transfer_chunk_choice_edge;[exact AMOUNT|].
    unfold transfer_ready_zero_values;rewrite !PTree.gso by discriminate;exact SIZE. }
  transfer_retain(State f_host_transfer Sskip
    (Kseq transfer_chunk_assignment(Kseq transfer_after_chunk transfer_iteration_cont))
    empty_env(transfer_chunk_temp_values temporaries amount)memory).
  { apply certified_set_edge;apply actual_transfer_chunk_expression;[exact AMOUNT|].
    unfold transfer_ready_zero_values;rewrite !PTree.gso by discriminate;exact SIZE. }
  transfer_retain(State f_host_transfer transfer_chunk_assignment(Kseq transfer_after_chunk transfer_iteration_cont)
    empty_env(transfer_chunk_temp_values temporaries amount)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  transfer_retain(State f_host_transfer Sskip(Kseq transfer_after_chunk transfer_iteration_cont)
    empty_env(transfer_amount_values temporaries amount)memory).
  { apply certified_set_edge;apply old_expression_value,value_temp;
      unfold transfer_chunk_temp_values;apply PTree.gss. }
  transfer_retain(State f_host_transfer transfer_after_chunk transfer_iteration_cont
    empty_env(transfer_amount_values temporaries amount)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  transfer_retain(State f_host_transfer transfer_save_sequence(Kseq transfer_after_save transfer_iteration_cont)
    empty_env(transfer_amount_values temporaries amount)memory).
  { apply unchanged_store_edge,edge_seq. }
  transfer_retain(State f_host_transfer transfer_save_call
    (Kseq transfer_save_bind(Kseq transfer_after_save transfer_iteration_cont))
    empty_env(transfer_amount_values temporaries amount)memory).
  { apply unchanged_store_edge,edge_seq. }
  transfer_retain(Callstate gateway_save_thread_definition[](transfer_save_cont temporaries amount)memory).
  { apply actual_transfer_save_thread_call with(symbol:=symbol);assumption. }
  constructor.
Qed.
