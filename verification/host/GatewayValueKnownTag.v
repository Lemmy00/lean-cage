(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A nonnull actual decoder return consumes a supported tag;
   unsupported arbitrary VM bytes remain present and reach the checked null-denial path. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayValueContext GatewayValueStack GatewayValueActual
  GatewayValueRegions GatewayValueUnknown GatewaySourceCuts GatewayPathEvents GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_actual_value_known_tag {World Event}(backend:gateway_backend World Event)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    arguments before world events value after next stream_block stream_offset initial readonly original:
  gateway_value_stream arguments=Vptr stream_block stream_offset->
  gateway_value_context native stable discipline stream_block stream_offset initial readonly original before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists byte,0<=Byte.unsigned byte<=9 /\
    gateway_received_bytes io(stream_descriptor initial)events=byte::tl(gateway_received_bytes io(stream_descriptor initial)events).
Proof.
  intros STREAM INPUT RUN NONNULL.
  destruct(gateway_actual_value_tag backend io native stable discipline thread_errno runtime arguments before world events value after next
    stream_block stream_offset initial readonly original STREAM INPUT RUN NONNULL)
    as(slots &byte &prefix &reading &suffix &word_before &word_world &word_after &word_next &final_stream &
      EVENTS &DEPTH &NODES &QUIET &PREFIX &ALLOCATED &READING &OBSERVED &LOAD &STREAM_AFTER &ACTIVE &REST).
  assert(KNOWN:Byte.unsigned byte<=9).
  { destruct(Z_le_gt_dec(Byte.unsigned byte)9)as[SMALL|LARGE];[exact SMALL|].
    set(property:=gateway_value_tagged native stable discipline slots stream_block stream_offset final_stream readonly original
      (Int64.repr(Byte.unsigned byte))).
    pose proof(gateway_value_tagged_ambient backend io native stable discipline thread_errno runtime slots stream_block stream_offset
      final_stream readonly original(Int64.repr(Byte.unsigned byte)))as CLOSED.
    pose proof(Byte.unsigned_range byte)as RANGE.
    pose proof(gateway_value_unknown_tag_failure backend(Clight.globalenv prog)property slots arguments initial word_after(Byte.unsigned byte)
      CLOSED ltac:(change Byte.modulus with 256 in RANGE;lia)ltac:(intros memory current GOOD;exact(proj2 GOOD)))as FAILURE.
    exfalso;apply NONNULL;eapply FAILURE;[exact(conj ACTIVE LOAD)|exact REST]. }
  exists byte;split;[pose proof(Byte.unsigned_range byte);lia|].
  rewrite EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)prefix QUIET),OBSERVED;reflexivity.
Qed.
