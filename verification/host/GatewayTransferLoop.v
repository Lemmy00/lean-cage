(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Source loop exit and repeated readiness preserve the actual
   cursor state. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPure GatewayCallPath GatewayControlPaths
  GatewayTransferSource.
Import ListNotations.
Open Scope Z_scope.

Local Ltac loop_prefix target:=
  eapply gateway_prefix_next with(next:=target);[cbn;tauto|intro another|].
Local Ltac loop_call target:=
  eapply gateway_retained_next with(next:=target);[cbn;tauto|intro another|].
Local Ltac loop_pure target:=
  eapply gateway_pure_next with(next:=target);[cbn;tauto|intro another|].

Lemma actual_receive_transfer_enters_loop ge stream data amount memory :
  gateway_retained_prefix ge
    (State f_host_transfer transfer_loop transfer_loop_cont empty_env(transfer_loop_values stream data amount)memory)
    (Callstate(Internal f_host_transfer)[stream;data;Vlong(Int64.repr amount);Vint Int.zero]Kstop memory).
Proof.
  loop_prefix(State f_host_transfer(fn_body f_host_transfer)Kstop empty_env
    (transfer_parameters stream data amount)memory).
  { apply function_entry_source_edge,actual_receive_transfer_entry. }
  loop_prefix(State f_host_transfer(Sset _cursor(Etempvar _data(tptr tvoid)))(Kseq transfer_tail Kstop)
    empty_env(transfer_parameters stream data amount)memory).
  { apply unchanged_store_edge,edge_seq. }
  loop_prefix(State f_host_transfer Sskip(Kseq transfer_tail Kstop)empty_env
    (transfer_loop_values stream data amount)memory).
  { apply certified_set_edge;apply old_expression_value,value_temp;reflexivity. }
  loop_prefix(State f_host_transfer transfer_tail Kstop empty_env(transfer_loop_values stream data amount)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  loop_prefix(State f_host_transfer transfer_loop transfer_loop_cont empty_env(transfer_loop_values stream data amount)memory).
  { apply unchanged_store_edge,edge_seq. }
  change(gateway_retained_prefix ge
    (State f_host_transfer transfer_loop transfer_loop_cont empty_env(transfer_loop_values stream data amount)memory)
    (gateway_replace_memory(State f_host_transfer transfer_loop transfer_loop_cont empty_env
      (transfer_loop_values stream data amount)memory)memory)).
  constructor.
Qed.

Lemma actual_zero_transfer_loop_path ge temporaries memory :
  temporaries!_size=Some(Vlong Int64.zero) ->
  gateway_pure_path ge(State f_host_transfer transfer_loop transfer_loop_cont empty_env temporaries memory)(Vint Int.zero).
Proof.
  intro SIZE.
  loop_pure(State f_host_transfer transfer_loop_first transfer_iteration_cont empty_env temporaries memory).
  { apply unchanged_store_edge,edge_loop. }
  loop_pure(State f_host_transfer(Sifthenelse(Etempvar _size tulong)Sskip Sbreak)
    (Kseq transfer_iteration transfer_iteration_cont)empty_env temporaries memory).
  { apply unchanged_store_edge,edge_seq. }
  loop_pure(State f_host_transfer Sbreak(Kseq transfer_iteration transfer_iteration_cont)empty_env temporaries memory).
  { apply certified_if_edge with(v:=Vlong Int64.zero)(b:=false);
      [apply old_expression_value,value_temp;exact SIZE|reflexivity]. }
  loop_pure(State f_host_transfer Sbreak transfer_iteration_cont empty_env temporaries memory).
  { apply unchanged_store_edge,edge_break_seq. }
  loop_pure(State f_host_transfer Sskip transfer_loop_cont empty_env temporaries memory).
  { apply unchanged_store_edge,edge_break_loop1. }
  loop_pure(State f_host_transfer transfer_return Kstop empty_env temporaries memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  loop_pure(Returnstate(Vint Int.zero)Kstop memory).
  { apply unchanged_store_edge;eapply edge_return with(v:=Vint Int.zero);[constructor|reflexivity]. }
  constructor.
Qed.

Theorem actual_zero_receive_transfer_path ge stream data memory :
  gateway_pure_path ge
    (Callstate(Internal f_host_transfer)[stream;data;Vlong Int64.zero;Vint Int.zero]Kstop memory)(Vint Int.zero).
Proof.
  eapply gateway_prefix_before_return.
  - exact(actual_receive_transfer_enters_loop ge stream data 0 memory).
  - apply actual_zero_transfer_loop_path;reflexivity.
Qed.

Lemma actual_positive_transfer_loop_ready_path (ge:Clight.genv)temporaries stream_block stream_offset
    amount memory symbol :
  0<amount<=Int64.max_unsigned ->temporaries!_size=Some(Vlong(Int64.repr amount)) ->
  temporaries!_stream=Some(Vptr stream_block stream_offset) ->temporaries!_sending=Some(Vint Int.zero) ->
  Genv.find_symbol ge _host_ready=Some symbol ->Genv.find_funct_ptr ge symbol=Some(Internal f_host_ready) ->
  gateway_retained_call_path ge(Internal f_host_ready)[Vptr stream_block stream_offset;Vint Int.one]
    (transfer_ready_cont temporaries)
    (State f_host_transfer transfer_loop transfer_loop_cont empty_env temporaries memory).
Proof.
  intros AMOUNT SIZE STREAM RECEIVE SYMBOL FUNCTION.
  loop_call(State f_host_transfer transfer_loop_first transfer_iteration_cont empty_env temporaries memory).
  { apply unchanged_store_edge,edge_loop. }
  loop_call(State f_host_transfer(Sifthenelse(Etempvar _size tulong)Sskip Sbreak)
    (Kseq transfer_iteration transfer_iteration_cont)empty_env temporaries memory).
  { apply unchanged_store_edge,edge_seq. }
  loop_call(State f_host_transfer Sskip(Kseq transfer_iteration transfer_iteration_cont)empty_env temporaries memory).
  { apply certified_if_edge with(v:=Vlong(Int64.repr amount))(b:=true).
    - apply old_expression_value,value_temp;exact SIZE.
    - change(Some(negb(Int64.eq(Int64.repr amount)Int64.zero))=Some true).
      rewrite Int64.eq_false;[reflexivity|]. intro ZERO;apply(f_equal Int64.unsigned)in ZERO.
      rewrite Int64.unsigned_repr in ZERO by lia;rewrite Int64.unsigned_zero in ZERO;lia. }
  loop_call(State f_host_transfer transfer_iteration transfer_iteration_cont empty_env temporaries memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  apply actual_transfer_iteration_receive_ready_path with(symbol:=symbol);assumption.
Qed.
