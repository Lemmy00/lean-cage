(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Receive results reach the actual errno lookup before thread
   restoration. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayCallPath GatewayTransferSource
  GatewayTransferChunk GatewayTransferReceive GatewayRuntimeABI.
Import ListNotations.

Definition transfer_errno_sequence:=match transfer_after_io with Ssequence number _=>number|_=>Sskip end.
Definition transfer_after_errno:=match transfer_after_io with Ssequence _ rest=>rest|_=>Sskip end.
Definition transfer_errno_call:=match transfer_errno_sequence with Ssequence call _=>call|_=>Sskip end.
Definition transfer_errno_bind:=match transfer_errno_sequence with Ssequence _ bind=>bind|_=>Sskip end.
Definition transfer_restore_call:=match transfer_after_errno with Ssequence call _=>call|_=>Sskip end.
Definition transfer_after_restore:=match transfer_after_errno with Ssequence _ rest=>rest|_=>Sskip end.
Definition transfer_received_values temporaries amount saved descriptor count:=
  PTree.set _t'7(Vlong count)(transfer_receive_values temporaries amount saved descriptor).
Definition transfer_cast_count_values temporaries amount saved descriptor count:=
  PTree.set _t'5(Vlong count)(transfer_received_values temporaries amount saved descriptor count).
Definition transfer_count_values temporaries amount saved descriptor count:=
  PTree.set _count(Vlong count)(transfer_cast_count_values temporaries amount saved descriptor count).
Definition transfer_errno_cont temporaries amount saved descriptor count:=
  Kcall(Some _t'8)f_host_transfer empty_env(transfer_count_values temporaries amount saved descriptor count)
    (Kseq transfer_errno_bind(Kseq transfer_after_errno transfer_iteration_cont)).

Lemma actual_transfer_errno_call (ge:Clight.genv)temporaries amount saved descriptor count memory symbol :
  Genv.find_symbol ge ___errno_location=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some gateway_errno_location_definition ->
  store_edge ge(State f_host_transfer transfer_errno_call
    (Kseq transfer_errno_bind(Kseq transfer_after_errno transfer_iteration_cont))empty_env
    (transfer_count_values temporaries amount saved descriptor count)memory)
    (Callstate gateway_errno_location_definition[]
      (transfer_errno_cont temporaries amount saved descriptor count)memory).
Proof.
  intros SYMBOL FUNCTION;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
  - apply no_argument_values.
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Local Ltac errno_retain target:=
  eapply gateway_retained_next with(next:=target);[cbn;tauto|intro another|].

Lemma actual_received_count_errno_path (ge:Clight.genv)temporaries amount saved descriptor count memory symbol :
  Genv.find_symbol ge ___errno_location=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some gateway_errno_location_definition ->
  gateway_retained_call_path ge gateway_errno_location_definition[]
    (transfer_errno_cont temporaries amount saved descriptor count)
    (Returnstate(Vlong count)(transfer_receive_cont temporaries amount saved descriptor)memory).
Proof.
  intros SYMBOL FUNCTION.
  errno_retain(State f_host_transfer Sskip
    (Kseq transfer_receive_cast(Kseq transfer_count_assignment(Kseq transfer_after_io transfer_iteration_cont)))
    empty_env(transfer_received_values temporaries amount saved descriptor count)memory).
  { apply unchanged_store_edge,edge_returnstate. }
  errno_retain(State f_host_transfer transfer_receive_cast
    (Kseq transfer_count_assignment(Kseq transfer_after_io transfer_iteration_cont))
    empty_env(transfer_received_values temporaries amount saved descriptor count)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  errno_retain(State f_host_transfer Sskip
    (Kseq transfer_count_assignment(Kseq transfer_after_io transfer_iteration_cont))
    empty_env(transfer_cast_count_values temporaries amount saved descriptor count)memory).
  { apply certified_set_edge;apply cast_expression_value with(v:=Vlong count);
      [apply old_expression_value,value_temp;unfold transfer_received_values;apply PTree.gss|reflexivity]. }
  errno_retain(State f_host_transfer transfer_count_assignment(Kseq transfer_after_io transfer_iteration_cont)
    empty_env(transfer_cast_count_values temporaries amount saved descriptor count)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  errno_retain(State f_host_transfer Sskip(Kseq transfer_after_io transfer_iteration_cont)
    empty_env(transfer_count_values temporaries amount saved descriptor count)memory).
  { apply certified_set_edge;apply old_expression_value,value_temp;
      unfold transfer_cast_count_values;apply PTree.gss. }
  errno_retain(State f_host_transfer transfer_after_io transfer_iteration_cont
    empty_env(transfer_count_values temporaries amount saved descriptor count)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  errno_retain(State f_host_transfer transfer_errno_sequence(Kseq transfer_after_errno transfer_iteration_cont)
    empty_env(transfer_count_values temporaries amount saved descriptor count)memory).
  { apply unchanged_store_edge,edge_seq. }
  errno_retain(State f_host_transfer transfer_errno_call
    (Kseq transfer_errno_bind(Kseq transfer_after_errno transfer_iteration_cont))
    empty_env(transfer_count_values temporaries amount saved descriptor count)memory).
  { apply unchanged_store_edge,edge_seq. }
  errno_retain(Callstate gateway_errno_location_definition[]
    (transfer_errno_cont temporaries amount saved descriptor count)memory).
  { apply actual_transfer_errno_call with(symbol:=symbol);assumption. }
  constructor.
Qed.
