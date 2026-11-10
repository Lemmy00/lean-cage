(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Outgoing progress preserves the real transfer parameters. *)
From Stdlib Require Import ZArith.
From compcert Require Import Coqlib Maps Integers AST Values Clight.
From HostGateway Require Import GatewaySource GatewayTransferSource GatewayTransferMath GatewayTransferChunk
  GatewayTransferReceive GatewayTransferErrno GatewayTransferRestore GatewayTransferProgress GatewayTransferRetry
  GatewaySendSource GatewaySendChunk GatewaySendOperation GatewaySendErrno GatewaySendRestore GatewayTransferZero.
Open Scope Z_scope.
Definition send_initial_values stream data amount:=transfer_direction_loop_values stream data amount Int.one.

Definition gateway_send_locals temporaries stream data size :Prop:=
  temporaries!_stream=Some stream /\temporaries!_sending=Some(Vint Int.one) /\
  temporaries!_cursor=Some data /\temporaries!_size=Some(Vlong(Int64.repr size)).

Local Ltac transfer_values:=
  unfold send_number_values,GatewaySendRestore.send_errno_values,send_count_values,
    send_cast_count_values,send_returned_values,send_transfer_values,send_saved_values,
    send_amount_values,send_chunk_temp_values,send_ready_zero_values;
  repeat first[rewrite PTree.gss|rewrite PTree.gso by discriminate].

Lemma gateway_send_number_locals temporaries size saved descriptor count pointer number stream data :
  gateway_send_locals temporaries stream data size ->
  gateway_send_locals(send_number_values temporaries size saved descriptor count pointer number)stream data size.
Proof.
  intros[STREAM[SENDING[CURSOR SIZE]]];unfold gateway_send_locals;repeat split;transfer_values;assumption.
Qed.

Lemma gateway_send_number_count temporaries size saved descriptor count pointer number :
  (send_number_values temporaries size saved descriptor count pointer number)!_count=Some(Vlong count).
Proof. transfer_values;reflexivity. Qed.

Lemma gateway_send_number_errno temporaries size saved descriptor count pointer number :
  (send_number_values temporaries size saved descriptor count pointer number)!_number=Some number.
Proof. unfold send_number_values;apply PTree.gss. Qed.

Lemma gateway_send_number_chunk temporaries size saved descriptor count pointer number :
  (send_number_values temporaries size saved descriptor count pointer number)!_amount=
    Some(Vlong(Int64.repr(transfer_chunk size))).
Proof. transfer_values;reflexivity. Qed.

Lemma gateway_send_advanced_locals temporaries size count block offset stream :
  gateway_send_locals temporaries stream(Vptr block offset)size ->
  gateway_send_locals(transfer_advanced_values temporaries size count block offset)stream
    (Vptr block(Ptrofs.add offset(Ptrofs.repr count)))(size-count).
Proof.
  intros[STREAM[SENDING[CURSOR SIZE]]];unfold gateway_send_locals;repeat split;
    unfold transfer_advanced_values,transfer_advanced_cursor_values,transfer_positive_count_values,transfer_positive_retry_values;
    repeat first[rewrite PTree.gss|rewrite PTree.gso by discriminate];auto.
Qed.

Lemma gateway_send_retried_locals temporaries stream data size :
  gateway_send_locals temporaries stream data size ->
  gateway_send_locals(transfer_retry_values temporaries)stream data size.
Proof.
  intros[STREAM[SENDING[CURSOR SIZE]]];unfold gateway_send_locals;repeat split;
    unfold transfer_retry_values,transfer_retry_errno_values;
    repeat rewrite PTree.gso by discriminate;assumption.
Qed.

Lemma gateway_send_initial_locals stream data size :
  gateway_send_locals(send_initial_values stream data size)stream data size.
Proof. repeat split;reflexivity. Qed.
