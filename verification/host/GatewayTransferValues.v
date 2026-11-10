(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Actual saved caller temporaries retain the transfer parameters. *)
From Stdlib Require Import ZArith.
From compcert Require Import Coqlib Maps Integers AST Values Clight.
From HostGateway Require Import GatewaySource GatewayTransferSource GatewayTransferMath GatewayTransferChunk
  GatewayTransferReceive GatewayTransferErrno GatewayTransferRestore GatewayTransferProgress GatewayTransferRetry.
Open Scope Z_scope.

Definition gateway_transfer_locals temporaries stream data size :Prop:=
  temporaries!_stream=Some stream /\temporaries!_sending=Some(Vint Int.zero) /\
  temporaries!_cursor=Some data /\temporaries!_size=Some(Vlong(Int64.repr size)).

Local Ltac transfer_values:=
  unfold transfer_number_values,GatewayTransferRestore.transfer_errno_values,transfer_count_values,
    transfer_cast_count_values,transfer_received_values,transfer_receive_values,transfer_saved_values,
    transfer_amount_values,transfer_chunk_temp_values,transfer_ready_zero_values;
  repeat first[rewrite PTree.gss|rewrite PTree.gso by discriminate].

Lemma gateway_transfer_number_locals temporaries size saved descriptor count pointer number stream data :
  gateway_transfer_locals temporaries stream data size ->
  gateway_transfer_locals(transfer_number_values temporaries size saved descriptor count pointer number)stream data size.
Proof.
  intros[STREAM[SENDING[CURSOR SIZE]]];unfold gateway_transfer_locals;repeat split;transfer_values;assumption.
Qed.

Lemma gateway_transfer_number_count temporaries size saved descriptor count pointer number :
  (transfer_number_values temporaries size saved descriptor count pointer number)!_count=Some(Vlong count).
Proof. transfer_values;reflexivity. Qed.

Lemma gateway_transfer_number_errno temporaries size saved descriptor count pointer number :
  (transfer_number_values temporaries size saved descriptor count pointer number)!_number=Some number.
Proof. unfold transfer_number_values;apply PTree.gss. Qed.

Lemma gateway_transfer_number_chunk temporaries size saved descriptor count pointer number :
  (transfer_number_values temporaries size saved descriptor count pointer number)!_amount=
    Some(Vlong(Int64.repr(transfer_chunk size))).
Proof. transfer_values;reflexivity. Qed.

Lemma gateway_transfer_advanced_locals temporaries size count block offset stream :
  gateway_transfer_locals temporaries stream(Vptr block offset)size ->
  gateway_transfer_locals(transfer_advanced_values temporaries size count block offset)stream
    (Vptr block(Ptrofs.add offset(Ptrofs.repr count)))(size-count).
Proof.
  intros[STREAM[SENDING[CURSOR SIZE]]];unfold gateway_transfer_locals;repeat split;
    unfold transfer_advanced_values,transfer_advanced_cursor_values,transfer_positive_count_values,transfer_positive_retry_values;
    repeat first[rewrite PTree.gss|rewrite PTree.gso by discriminate];auto.
Qed.

Lemma gateway_transfer_retried_locals temporaries stream data size :
  gateway_transfer_locals temporaries stream data size ->
  gateway_transfer_locals(transfer_retry_values temporaries)stream data size.
Proof.
  intros[STREAM[SENDING[CURSOR SIZE]]];unfold gateway_transfer_locals;repeat split;
    unfold transfer_retry_values,transfer_retry_errno_values;
    repeat rewrite PTree.gso by discriminate;assumption.
Qed.

Lemma gateway_transfer_initial_locals stream data size :
  gateway_transfer_locals(transfer_loop_values stream data size)stream data size.
Proof. repeat split;reflexivity. Qed.
