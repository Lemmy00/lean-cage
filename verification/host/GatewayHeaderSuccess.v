(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A successful original exchange derives its real header-transfer success. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayPure GatewayReturns
  GatewayReturnTypes GatewayFailurePaths GatewayHeaderTransfer GatewayPayloadControl GatewayPayloadUndefined
  GatewayHeaderComplete GatewayHeaderSend GatewaySendRuntime GatewaySendInterface GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.
Open Scope Z_scope.

Lemma actual_header_failed_return {World Event}(backend:gateway_backend World Event)ge environment temporaries memory:
  gateway_failure_result backend ge
    (Returnstate(Vint(Int.neg Int.one))(header_transfer_cont environment temporaries)memory).
Proof.
  eapply gateway_failure_edge with(target:=State f_host_exchange Sskip
    (Kseq header_transfer_bind(Kseq header_transfer_after Kstop))environment
    (PTree.set _t'30(Vint(Int.neg Int.one))temporaries)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_failure_edge with(target:=State f_host_exchange header_transfer_bind(Kseq header_transfer_after Kstop)
    environment(PTree.set _t'30(Vint(Int.neg Int.one))temporaries)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_failure_edge with(target:=State f_host_exchange Sskip(Kseq header_transfer_after Kstop)environment
    (PTree.set _failed(Vint(Int.neg Int.one))(PTree.set _t'30(Vint(Int.neg Int.one))temporaries))memory);
    [cbn;tauto|intros;apply certified_set_edge,old_expression_value;WriteAll.expression|].
  eapply gateway_failure_edge with(target:=State f_host_exchange header_transfer_after Kstop environment
    (PTree.set _failed(Vint(Int.neg Int.one))(PTree.set _t'30(Vint(Int.neg Int.one))temporaries))memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  apply actual_failed_payload_entry;apply PTree.gss.
Qed.

Lemma actual_header_undefined_return ge environment temporaries memory:
  gateway_blocked_path ge(Returnstate Vundef(header_transfer_cont environment temporaries)memory).
Proof.
  eapply gateway_blocked_next with(next:=State f_host_exchange Sskip
    (Kseq header_transfer_bind(Kseq header_transfer_after Kstop))environment(PTree.set _t'30 Vundef temporaries)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_blocked_next with(next:=State f_host_exchange header_transfer_bind(Kseq header_transfer_after Kstop)
    environment(PTree.set _t'30 Vundef temporaries)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_blocked_next with(next:=State f_host_exchange Sskip(Kseq header_transfer_after Kstop)environment
    (PTree.set _failed Vundef(PTree.set _t'30 Vundef temporaries))memory);
    [cbn;tauto|intros;apply certified_set_edge,old_expression_value;WriteAll.expression|].
  eapply gateway_blocked_next with(next:=State f_host_exchange header_transfer_after Kstop environment
    (PTree.set _failed Vundef(PTree.set _t'30 Vundef temporaries))memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  apply actual_undefined_payload_entry;apply PTree.gss.
Qed.

Theorem actual_successful_header_return {World Event}(backend:gateway_backend World Event)ge
    environment temporaries before world events returned value after next:
  gateway_int_return_value returned->value<>Vnullptr->
  gateway_steps backend ge(gateway_live(Returnstate returned(header_transfer_cont environment temporaries)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->returned=Vint Int.zero.
Proof.
  intros[UNDEFINED|[ZERO|FAILED]]NONNULL RUN;[subst returned|exact ZERO|subst returned].
  - exfalso;eapply gateway_blocked_cannot_return;[apply actual_header_undefined_return|exact RUN].
  - exfalso;apply NONNULL;exact(actual_header_failed_return backend ge environment temporaries before
      before world events value after next RUN).
Qed.

Theorem actual_successful_header_sends {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    environment temporaries before world stream header initial readonly command fault rows events value after next:
  discipline None before world->native world stream->
  (forall object position,readonly object position->stable world object position)->
  gateway_send_inputs before stream Ptrofs.zero initial readonly->
  (forall position,0<=position<112->readonly header position)->
  Mem.loadbytes before header 0 112=Some(Memdata.inj_bytes(gateway_complete_header command fault rows))->
  stream_descriptor initial<>stream_control initial->value<>Vnullptr->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_transfer)(header_transfer_arguments stream header)
      (header_transfer_cont environment temporaries)before)world)events(gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_transfer)(header_transfer_arguments stream header)Kstop before)world)prefix
      (gateway_live(Returnstate(Vint Int.zero)Kstop memory)current) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(header_transfer_cont environment temporaries)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next) /\
    gateway_sent_bytes io(stream_descriptor initial)prefix=gateway_complete_header command fault rows /\
    gateway_send_receipt io native readonly before world stream Ptrofs.zero initial(Vptr header Ptrofs.zero)112
      prefix memory current(gateway_complete_header command fault rows) /\discipline None memory current.
Proof.
  intros SIDE PRIVATE STABLE INPUT COVER BYTES SEPARATE NONNULL RUN.
  destruct(gateway_return_cut backend(Clight.globalenv prog)(Internal f_host_transfer)(header_transfer_arguments stream header)
    (header_transfer_cont environment temporaries)before world events(Returnstate value Kstop after)next I ltac:(cbn;lia)RUN)
    as(prefix & suffix & returned & memory & current & EVENTS & BODY & SUFFIX).
  pose proof(gateway_actual_int_return backend(Clight.globalenv prog)f_host_transfer(header_transfer_arguments stream header)
    before world prefix returned memory current actual_host_transfer_return_profile BODY)as TYPE.
  pose proof(actual_successful_header_return backend(Clight.globalenv prog)environment temporaries memory current suffix returned
    value after next TYPE NONNULL SUFFIX)as ZERO;subst returned.
  destruct(gateway_actual_header_send backend io native stable discipline thread_errno runtime before world stream header initial readonly
    command fault rows prefix memory current SIDE PRIVATE STABLE INPUT COVER BYTES SEPARATE BODY)
    as[OBSERVED[RECEIPT[READY REST]]].
  exists prefix,suffix,memory,current;split;[exact EVENTS|]. split;[exact BODY|]. split;[exact SUFFIX|].
  split;[exact OBSERVED|]. split;assumption.
Qed.

Theorem actual_successful_header_sends_ready {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    environment temporaries before world stream header initial readonly command fault rows events value after next:
  discipline None before world->native world stream->
  (forall object position,readonly object position->stable world object position)->
  gateway_send_inputs before stream Ptrofs.zero initial readonly->
  (forall position,0<=position<112->readonly header position)->
  Mem.loadbytes before header 0 112=Some(Memdata.inj_bytes(gateway_complete_header command fault rows))->
  stream_descriptor initial<>stream_control initial->value<>Vnullptr->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_transfer)(header_transfer_arguments stream header)
      (header_transfer_cont environment temporaries)before)world)events(gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_transfer)(header_transfer_arguments stream header)Kstop before)world)prefix
      (gateway_live(Returnstate(Vint Int.zero)Kstop memory)current) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(header_transfer_cont environment temporaries)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next) /\
    gateway_sent_bytes io(stream_descriptor initial)prefix=gateway_complete_header command fault rows /\
    gateway_send_receipt io native readonly before world stream Ptrofs.zero initial(Vptr header Ptrofs.zero)112
      prefix memory current(gateway_complete_header command fault rows) /\discipline None memory current /\
    native current stream /\(forall object position,readonly object position->stable current object position).
Proof.
  intros SIDE PRIVATE STABLE INPUT COVER BYTES SEPARATE NONNULL RUN.
  destruct(gateway_return_cut backend(Clight.globalenv prog)(Internal f_host_transfer)(header_transfer_arguments stream header)
    (header_transfer_cont environment temporaries)before world events(Returnstate value Kstop after)next I ltac:(cbn;lia)RUN)
    as(prefix & suffix & returned & memory & current & EVENTS & BODY & SUFFIX).
  pose proof(gateway_actual_int_return backend(Clight.globalenv prog)f_host_transfer(header_transfer_arguments stream header)
    before world prefix returned memory current actual_host_transfer_return_profile BODY)as TYPE.
  pose proof(actual_successful_header_return backend(Clight.globalenv prog)environment temporaries memory current suffix returned
    value after next TYPE NONNULL SUFFIX)as ZERO;subst returned.
  destruct(gateway_actual_header_send backend io native stable discipline thread_errno runtime before world stream header initial readonly
    command fault rows prefix memory current SIDE PRIVATE STABLE INPUT COVER BYTES SEPARATE BODY)
    as[OBSERVED[RECEIPT[READY[PRIVATE_AFTER STABLE_AFTER]]]].
  exists prefix,suffix,memory,current;split;[exact EVENTS|]. split;[exact BODY|]. split;[exact SUFFIX|].
  split;[exact OBSERVED|]. split;[exact RECEIPT|]. split;[exact READY|]. split;assumption.
Qed.
