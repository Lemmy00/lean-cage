(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: The same real helper selects POLLOUT before a send attempt. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPure GatewayCallPath GatewayControlPaths
  GatewayTransferSource GatewayTransferLoop GatewayTransferZero.
Import ListNotations.
Open Scope Z_scope.

Definition transfer_send_ready_cont temporaries:=Kcall(Some _t'2)f_host_transfer empty_env
  (PTree.set _t'1(Vint(Int.repr 4))temporaries)
  (Kseq transfer_ready_test(Kseq transfer_after_ready transfer_iteration_cont)).

Lemma actual_transfer_direction_enters_loop ge stream data amount direction memory:
  gateway_retained_prefix ge
    (State f_host_transfer transfer_loop transfer_loop_cont empty_env
      (transfer_direction_loop_values stream data amount direction)memory)
    (Callstate(Internal f_host_transfer)[stream;data;Vlong(Int64.repr amount);Vint direction]Kstop memory).
Proof.
  eapply gateway_prefix_next with(next:=State f_host_transfer(fn_body f_host_transfer)Kstop empty_env
    (transfer_direction_parameters stream data amount direction)memory);
    [cbn;tauto|intros;apply function_entry_source_edge,actual_transfer_direction_entry|].
  eapply gateway_prefix_next with(next:=State f_host_transfer(Sset _cursor(Etempvar _data(tptr tvoid)))
    (Kseq transfer_tail Kstop)empty_env(transfer_direction_parameters stream data amount direction)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_prefix_next with(next:=State f_host_transfer Sskip(Kseq transfer_tail Kstop)empty_env
    (transfer_direction_loop_values stream data amount direction)memory);
    [cbn;tauto|intros;apply certified_set_edge,old_expression_value,value_temp;reflexivity|].
  eapply gateway_prefix_next with(next:=State f_host_transfer transfer_tail Kstop empty_env
    (transfer_direction_loop_values stream data amount direction)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_prefix_next with(next:=State f_host_transfer transfer_loop transfer_loop_cont empty_env
    (transfer_direction_loop_values stream data amount direction)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  change(gateway_retained_prefix ge
    (State f_host_transfer transfer_loop transfer_loop_cont empty_env
      (transfer_direction_loop_values stream data amount direction)memory)
    (gateway_replace_memory
    (State f_host_transfer transfer_loop transfer_loop_cont empty_env
      (transfer_direction_loop_values stream data amount direction)memory)memory)).
  constructor.
Qed.

Lemma actual_transfer_send_ready_call(ge:Clight.genv)temporaries stream_block stream_offset memory symbol:
  temporaries!_stream=Some(Vptr stream_block stream_offset)->
  Genv.find_symbol ge _host_ready=Some symbol->Genv.find_funct_ptr ge symbol=Some(Internal f_host_ready)->
  store_edge ge(State f_host_transfer transfer_ready_call
    (Kseq transfer_ready_test(Kseq transfer_after_ready transfer_iteration_cont))empty_env
    (PTree.set _t'1(Vint(Int.repr 4))temporaries)memory)
    (Callstate(Internal f_host_ready)[Vptr stream_block stream_offset;Vint(Int.repr 4)]
      (transfer_send_ready_cont temporaries)memory).
Proof.
  intros STREAM SYMBOL FUNCTION;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vptr stream_block stream_offset).
    + apply old_expression_value,value_temp;rewrite PTree.gso by discriminate;exact STREAM.
    + reflexivity.
    + eapply cons_argument_values with(v:=Vint(Int.repr 4));
        [apply old_expression_value,value_temp;apply PTree.gss|reflexivity|apply no_argument_values].
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Lemma actual_transfer_iteration_send_ready_path(ge:Clight.genv)temporaries stream_block stream_offset memory symbol:
  temporaries!_stream=Some(Vptr stream_block stream_offset)->temporaries!_sending=Some(Vint Int.one)->
  Genv.find_symbol ge _host_ready=Some symbol->Genv.find_funct_ptr ge symbol=Some(Internal f_host_ready)->
  gateway_retained_call_path ge(Internal f_host_ready)[Vptr stream_block stream_offset;Vint(Int.repr 4)]
    (transfer_send_ready_cont temporaries)
    (State f_host_transfer transfer_iteration transfer_iteration_cont empty_env temporaries memory).
Proof.
  intros STREAM SENDING SYMBOL FUNCTION.
  eapply gateway_retained_next with(next:=State f_host_transfer transfer_ready_sequence
    (Kseq transfer_after_ready transfer_iteration_cont)empty_env temporaries memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_retained_next with(next:=State f_host_transfer transfer_ready_prefix
    (Kseq transfer_ready_test(Kseq transfer_after_ready transfer_iteration_cont))empty_env temporaries memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_retained_next with(next:=State f_host_transfer transfer_ready_direction
    (Kseq transfer_ready_call(Kseq transfer_ready_test(Kseq transfer_after_ready transfer_iteration_cont)))empty_env temporaries memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_retained_next with(next:=State f_host_transfer(Sset _t'1(Ecast(Econst_int(Int.repr 4)tint)tint))
    (Kseq transfer_ready_call(Kseq transfer_ready_test(Kseq transfer_after_ready transfer_iteration_cont)))empty_env temporaries memory);
    [cbn;tauto| |].
  - intros;apply certified_if_edge with(v:=Vint Int.one)(b:=true);
      [apply old_expression_value,value_temp;exact SENDING|reflexivity].
  - eapply gateway_retained_next with(next:=State f_host_transfer Sskip
      (Kseq transfer_ready_call(Kseq transfer_ready_test(Kseq transfer_after_ready transfer_iteration_cont)))empty_env
      (PTree.set _t'1(Vint(Int.repr 4))temporaries)memory);
      [cbn;tauto|intros;apply certified_set_edge,old_expression_value;eapply value_cast;[constructor|reflexivity]|].
    eapply gateway_retained_next with(next:=State f_host_transfer transfer_ready_call
      (Kseq transfer_ready_test(Kseq transfer_after_ready transfer_iteration_cont))empty_env
      (PTree.set _t'1(Vint(Int.repr 4))temporaries)memory);
      [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
    eapply gateway_retained_next with(next:=Callstate(Internal f_host_ready)
      [Vptr stream_block stream_offset;Vint(Int.repr 4)](transfer_send_ready_cont temporaries)memory);
      [cbn;tauto|intros;eapply actual_transfer_send_ready_call;eassumption|constructor].
Qed.

Theorem actual_positive_send_loop_ready_path(ge:Clight.genv)temporaries stream_block stream_offset amount memory symbol:
  0<amount<=Int64.max_unsigned->temporaries!_size=Some(Vlong(Int64.repr amount))->
  temporaries!_stream=Some(Vptr stream_block stream_offset)->temporaries!_sending=Some(Vint Int.one)->
  Genv.find_symbol ge _host_ready=Some symbol->Genv.find_funct_ptr ge symbol=Some(Internal f_host_ready)->
  gateway_retained_call_path ge(Internal f_host_ready)[Vptr stream_block stream_offset;Vint(Int.repr 4)]
    (transfer_send_ready_cont temporaries)
    (State f_host_transfer transfer_loop transfer_loop_cont empty_env temporaries memory).
Proof.
  intros AMOUNT SIZE STREAM SENDING SYMBOL FUNCTION.
  eapply gateway_retained_next with(next:=State f_host_transfer transfer_loop_first transfer_iteration_cont empty_env temporaries memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_loop|].
  eapply gateway_retained_next with(next:=State f_host_transfer(Sifthenelse(Etempvar _size tulong)Sskip Sbreak)
    (Kseq transfer_iteration transfer_iteration_cont)empty_env temporaries memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_retained_next with(next:=State f_host_transfer Sskip(Kseq transfer_iteration transfer_iteration_cont)
    empty_env temporaries memory);[cbn;tauto| |].
  - intros;apply certified_if_edge with(v:=Vlong(Int64.repr amount))(b:=true).
    + apply old_expression_value,value_temp;exact SIZE.
    + change(Some(negb(Int64.eq(Int64.repr amount)Int64.zero))=Some true).
      rewrite Int64.eq_false;[reflexivity|]. intro ZERO;apply(f_equal Int64.unsigned)in ZERO.
      rewrite Int64.unsigned_repr in ZERO by lia;rewrite Int64.unsigned_zero in ZERO;lia.
  - eapply gateway_retained_next with(next:=State f_host_transfer transfer_iteration transfer_iteration_cont empty_env temporaries memory);
      [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
    eapply actual_transfer_iteration_send_ready_path;eassumption.
Qed.
