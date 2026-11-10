(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A successful field call sends its same retained bytes, including NULL empty fields. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayReturnTypes GatewayPayloadReturn
  GatewayThreadRuntime GatewayStreamInterface GatewaySendActual GatewaySendInterface GatewaySendRuntime.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_bytes_injective first second:inj_bytes first=inj_bytes second->first=second.
Proof. intro SAME;apply(f_equal proj_bytes)in SAME;rewrite !proj_inj_bytes in SAME;congruence. Qed.

Lemma gateway_payload_memory_unique memory pointer amount first second:
  gateway_sent_payload memory pointer amount first->gateway_sent_payload memory pointer amount second->first=second.
Proof.
  intros[[ZERO EMPTY]|[first_object[first_offset[FIRST FIRST_BYTES]]]]
    [[OTHER EMPTY_OTHER]|[second_object[second_offset[SECOND SECOND_BYTES]]]].
  - congruence.
  - subst amount first;rewrite Mem.loadbytes_empty in SECOND_BYTES by lia.
    injection SECOND_BYTES as SAME;apply gateway_bytes_injective;exact SAME.
  - subst amount second;rewrite Mem.loadbytes_empty in FIRST_BYTES by lia.
    injection FIRST_BYTES as SAME;apply gateway_bytes_injective;symmetry;exact SAME.
  - rewrite FIRST in SECOND;inversion SECOND;subst second_object second_offset.
    apply gateway_bytes_injective;congruence.
Qed.

Definition payload_transfer_arguments stream pointer size:=[Vptr stream Ptrofs.zero;pointer;Vlong size;Vint Int.one].

Theorem actual_successful_payload_sends {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    environment temporaries counter before world stream initial readonly pointer size expected events value after next:
  temporaries!_index__1=Some(Vint counter)->discipline None before world->native world stream->
  (forall object position,readonly object position->stable world object position)->
  gateway_send_inputs before stream Ptrofs.zero initial readonly->
  gateway_payload_cells readonly pointer(Int64.unsigned size)->
  gateway_sent_payload before pointer(Int64.unsigned size)expected->
  stream_descriptor initial<>stream_control initial->value<>Vnullptr->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_transfer)(payload_transfer_arguments stream pointer size)
      (payload_transfer_cont environment temporaries)before)world)events(gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_transfer)(payload_transfer_arguments stream pointer size)Kstop before)world)prefix
      (gateway_live(Returnstate(Vint Int.zero)Kstop memory)current) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(payload_transfer_cont environment temporaries)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next) /\
    gateway_sent_bytes io(stream_descriptor initial)prefix=expected /\
    gateway_send_receipt io native readonly before world stream Ptrofs.zero initial pointer(Int64.unsigned size)
      prefix memory current expected /\discipline None memory current /\native current stream /\
    (forall object position,readonly object position->stable current object position).
Proof.
  intros INDEX SIDE PRIVATE STABLE INPUT COVER BYTES SEPARATE NONNULL RUN.
  destruct(gateway_return_cut backend(Clight.globalenv prog)(Internal f_host_transfer)(payload_transfer_arguments stream pointer size)
    (payload_transfer_cont environment temporaries)before world events(Returnstate value Kstop after)next I ltac:(cbn;lia)RUN)
    as(prefix & suffix & returned & memory & current & EVENTS & BODY & SUFFIX).
  pose proof(gateway_actual_int_return backend(Clight.globalenv prog)f_host_transfer(payload_transfer_arguments stream pointer size)
    before world prefix returned memory current actual_host_transfer_return_profile BODY)as TYPE.
  pose proof(actual_successful_payload_return backend(Clight.globalenv prog)environment temporaries counter memory current suffix returned
    value after next INDEX TYPE NONNULL SUFFIX)as ZERO;subst returned.
  assert(CANONICAL:Int64.repr(Int64.unsigned size)=size)by apply Int64.repr_unsigned.
  assert(SIZE:0<=Int64.unsigned size<=Int64.max_unsigned).
  { pose proof(Int64.unsigned_range size);unfold Int64.max_unsigned;lia. }
  assert(RUN_BODY:gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_transfer)
      [Vptr stream Ptrofs.zero;pointer;Vlong(Int64.repr(Int64.unsigned size));Vint Int.one]Kstop before)world)prefix
    (gateway_live(Returnstate(Vint Int.zero)Kstop memory)current)).
  { rewrite CANONICAL;exact BODY. }
  destruct(gateway_actual_send_producer backend io native stable discipline thread_errno runtime before world stream Ptrofs.zero
    initial pointer(Int64.unsigned size)readonly prefix memory current SIDE PRIVATE STABLE INPUT SIZE COVER SEPARATE RUN_BODY)
    as[bytes[RECEIPT[READY[AFTER_NATIVE AFTER_STABLE]]]].
  assert(SAME:bytes=expected).
  { eapply gateway_payload_memory_unique;
      [exact(@gateway_send_payload World Event io native readonly before world stream Ptrofs.zero initial pointer
        (Int64.unsigned size)prefix memory current bytes RECEIPT)|exact BYTES]. }
  subst bytes.
  exists prefix,suffix,memory,current;split;[exact EVENTS|]. split;[exact BODY|]. split;[exact SUFFIX|]. split.
  - exact(@gateway_send_observed World Event io native readonly before world stream Ptrofs.zero initial pointer
      (Int64.unsigned size)prefix memory current expected RECEIPT).
  - split;[exact RECEIPT|]. split;[exact READY|]. split;assumption.
Qed.
