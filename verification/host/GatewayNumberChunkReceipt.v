(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual bounded digit loop computes the selected contiguous
   slice of the same initialized payload, rather than an independent list of digits. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Ctypes Clight.
Require Import Machine Readers.
From HostGateway Require Import GatewaySource GatewayMachine GatewayNumber GatewayNumberChunkSource GatewayIntegerMemory GatewayNumberIntegerStructure
  GatewaySourceSegments GatewayFramedRuntime GatewayObjects.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_number_middle_byte {A:Type}(before selected after:list A)position(byte:A):
  nth_error selected position=Some byte->nth_error(before++selected++after)(length before+position)=Some byte.
Proof.
  intro BYTE;rewrite nth_error_app2 by lia;replace(length before+position-length before)%nat with position by lia.
  rewrite nth_error_app1;[exact BYTE|apply nth_error_Some;rewrite BYTE;discriminate].
Qed.

Theorem gateway_number_actual_chunk_segment {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters object bytes prefix chunk suffix index width memory:
  gateway_ambient_closed backend property->bytes=prefix++chunk++suffix->Z.of_nat(length bytes)<=65536->
  index=Z.of_nat(length prefix)->width=Z.of_nat(length chunk)->0<=width<=9->
  Forall(fun byte=>48<=Byte.unsigned byte<=57)chunk->
  gateway_number_chunk_state parameters object Ptrofs.zero index width 0 0->
  (forall memory current,property memory current->Mem.loadbytes memory object 0(Z.of_nat(length bytes))=Some(inj_bytes bytes))->
  exists final,
    gateway_source_segment backend ge property
      (State f_host_json_number gateway_number_chunk_loop number_integer_chunk_cont empty_env parameters memory)
      (State f_host_json_number Sskip number_integer_chunk_cont empty_env final memory)property /\
    gateway_number_chunk_state final object Ptrofs.zero index width width(gateway_decimal_value chunk) /\
    gateway_chunk_parameters_retained parameters final.
Proof.
  intros CLOSED BYTES BOUND INDEX WIDTH WIDTH_BOUND DIGITS STATE LOAD.
  assert(INDEX_BOUND:0<=index<=65536).
  { rewrite INDEX,BYTES,!length_app in *;rewrite!Nat2Z.inj_add in BOUND;lia. }
  destruct(gateway_number_chunk_segment backend ge property empty_env number_integer_chunk_cont object Ptrofs.zero index width memory
    CLOSED INDEX_BOUND WIDTH_BOUND chunk parameters 0 0 DIGITS ltac:(lia)ltac:(lia)STATE
    ltac:(intros position byte BYTE current world GOOD;
      rewrite Ptrofs.add_zero_l;
      replace(index+0+Z.of_nat position)with(Z.of_nat(length prefix+position))by(rewrite Nat2Z.inj_add;lia);
      assert(SELECTED:nth_error bytes(length prefix+position)=Some byte)by(rewrite BYTES;apply gateway_number_middle_byte;exact BYTE);
      pose proof(gateway_integer_byte_load current object bytes(length prefix+position)byte BOUND(LOAD current world GOOD)SELECTED)as READ;
      assert(ASCII:48<=Byte.unsigned byte<=57)by(apply(proj1(Forall_forall _ _)DIGITS);eapply nth_error_In;exact BYTE);
      rewrite Byte.signed_eq_unsigned in READ by(change Byte.max_signed with 127;lia);exact READ))
    as(final &PATH &FINAL_STATE &PARAMETERS).
  exists final;split;[exact PATH|]. split;[|exact PARAMETERS].
  rewrite gateway_number_fold_exact,Z.mul_0_l,Z.add_0_l in FINAL_STATE;exact FINAL_STATE.
Qed.
