(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Native transfer arithmetic is bounded before pointer advancement. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import ClightSteps LocalAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayStreamInterface.
Import ListNotations.
Open Scope Z_scope.

Definition transfer_chunk(size:Z):Z:=Z.min size 65536.

Lemma transfer_chunk_bounds size :
  0<size ->0<transfer_chunk size<=65536 /\transfer_chunk size<=size.
Proof. unfold transfer_chunk;intros POSITIVE;split;[split|];apply Z.min_glb || apply Z.le_min_l || lia. Qed.

Lemma transfer_chunk_cases size :
  transfer_chunk size=if zlt 65536 size then 65536 else size.
Proof. unfold transfer_chunk;destruct(zlt 65536 size);[rewrite Z.min_r|rewrite Z.min_l];lia. Qed.

Lemma actual_transfer_chunk_comparison (ge:Clight.genv)environment temporaries memory size :
  0<=size<=Int64.max_unsigned ->temporaries!_size=Some(Vlong(Int64.repr size)) ->
  expression_value ge environment temporaries memory
    (Ebinop Ogt(Etempvar _size tulong)(Econst_int(Int.repr 65536)tint)tint)
    (Vint(if zlt 65536 size then Int.one else Int.zero)).
Proof.
  intros BOUND LOOK;apply old_expression_value;eapply value_binary.
  - apply value_temp;exact LOOK.
  - constructor.
  - change(Some(Val.of_bool(Int64.ltu(Int64.repr 65536)(Int64.repr size)))=
      Some(Vint(if zlt 65536 size then Int.one else Int.zero))).
    unfold Int64.ltu;rewrite !Int64.unsigned_repr by(change Int64.max_unsigned with 18446744073709551615 in *;lia).
    destruct(zlt 65536 size);reflexivity.
Qed.

Lemma transfer_count_progress size count :
  0<size<=Int64.max_unsigned ->0<count<=transfer_chunk size ->
  Int64.unsigned(Int64.sub(Int64.repr size)(Int64.repr count))=size-count /\
  0<=size-count<size /\0<count<=65536.
Proof.
  intros SIZE COUNT;pose proof(transfer_chunk_bounds size ltac:(lia))as[CHUNK SMALL].
  split.
  - unfold Int64.sub.
    rewrite(Int64.unsigned_repr size)by lia.
    rewrite(Int64.unsigned_repr count)by lia.
    apply Int64.unsigned_repr;lia.
  - lia.
Qed.

Lemma transfer_positive_signed_count count :
  0<count<=65536 ->Int64.signed(Int64.repr count)=count /\Int64.unsigned(Int64.repr count)=count.
Proof.
  intro COUNT;split;[apply Int64.signed_repr|apply Int64.unsigned_repr];
    change(-9223372036854775808<=count<=9223372036854775807) ||
      change(0<=count<=18446744073709551615);lia.
Qed.

Lemma transfer_cursor_advance offset written count total :
  0<=written ->0<count ->written+count<=total ->
  Ptrofs.unsigned offset+total<=Ptrofs.modulus ->
  Ptrofs.add(Ptrofs.add offset(Ptrofs.repr written))(Ptrofs.repr count)=
    Ptrofs.add offset(Ptrofs.repr(written+count)).
Proof.
  intros WRITTEN COUNT TOTAL BOUND.
  rewrite Ptrofs.add_assoc.
  f_equal;unfold Ptrofs.add;apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add;auto with ints.
Qed.

Lemma gateway_received_bytes_append {Event}io descriptor(first second:list(gateway_event Event)) :
  gateway_received_bytes io descriptor(first++second)=
    gateway_received_bytes io descriptor first++gateway_received_bytes io descriptor second.
Proof. unfold gateway_received_bytes;apply flat_map_app. Qed.
