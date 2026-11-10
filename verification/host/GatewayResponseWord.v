(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Header words decode the exact retained bytes of the real reply. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Clight.
From LeanImport Require Import Lean.
Require Import Machine Readers ScalarMemory.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOperations GatewayImport GatewayThreadRuntime GatewayStreamInterface
  GatewayReadContext GatewayReads GatewayReadonly GatewayReadonlyRuntime GatewayStreamWord GatewayWordsMemory GatewayWordsMath GatewayWordData
  GatewayWordReceipt GatewayPathEvents GatewayFrames GatewayPayloadSend.
Import ListNotations Ctypes Clight.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition gateway_response_context {World}native stable discipline stream response readonly initial bytes memory world:=
  @gateway_read_context World native stable discipline None stream Ptrofs.zero initial response Ptrofs.zero 24 readonly memory world /\
  Mem.loadbytes memory response 0 24=Some(inj_bytes bytes).
Definition gateway_response_word_bytes(bytes:list Byte.int)start count:=firstn count(skipn start bytes).
Definition gateway_response_word_value(bytes:list Byte.int)start count:=
  Vlong(Int64.repr(Z.of_nat(nat_of_Nat(LeanCage_Host_GatewayWords_decode
    (gateway_imported_nats(gateway_byte_naturals(gateway_response_word_bytes bytes start count))))))).

Lemma gateway_response_context_preserved {World}native stable discipline stream response readonly initial bytes before world after next:
  @gateway_response_context World native stable discipline stream response readonly initial bytes before world->
  discipline None after next->gateway_access_retained native stable before world next->
  gateway_native_frame native stable gateway_native_no_output world before after->
  gateway_response_context native stable discipline stream response readonly initial bytes after next.
Proof.
  intros[RAW LOADED]SIDE ACCESS FRAME;split.
  - eapply gateway_read_context_preserved;[exact RAW|exact SIDE|exact ACCESS|exact FRAME].
  - eapply Mem.loadbytes_unchanged_on;[exact FRAME| |exact LOADED].
    intros position INSIDE;split;[left;exact(proj1(proj2(proj2 RAW)))|intro BAD;exact BAD].
Qed.

Lemma gateway_response_context_ambient {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)stream response readonly initial bytes:
  gateway_runtime_discipline backend(gateway_response_context native stable discipline stream response readonly initial bytes).
Proof.
  intros before world after next[RAW LOADED]INTERFERENCE.
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next(proj1 RAW)INTERFERENCE)
    as[SIDE[ACCESS FRAME]].
  exact(gateway_response_context_preserved native stable discipline stream response readonly initial bytes
    before world after next(conj RAW LOADED)SIDE ACCESS FRAME).
Qed.

Lemma gateway_response_word_slice memory response bytes start count:
  Z.of_nat(length bytes)=24->(start+count<=24)%nat->
  Mem.loadbytes memory response 0 24=Some(inj_bytes bytes)->
  length(gateway_response_word_bytes bytes start count)=count /\
  Mem.loadbytes memory response(Z.of_nat start)(Z.of_nat count)=
    Some(inj_bytes(gateway_response_word_bytes bytes start count)).
Proof.
  intros LENGTH RANGE LOADED;split.
  - unfold gateway_response_word_bytes;rewrite length_firstn,length_skipn;lia.
  - pose proof(loadbytes_slice memory response 0(map Byte bytes)(Z.of_nat start)(Z.of_nat count))as SLICE.
    rewrite length_map,LENGTH in SLICE;specialize(SLICE LOADED ltac:(lia)ltac:(lia)ltac:(lia)).
    rewrite !Nat2Z.id,skipn_map,firstn_map in SLICE;exact SLICE.
Qed.

Theorem gateway_actual_response_word {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    stream response readonly initial bytes start count before world events returned after next:
  Z.of_nat(length bytes)=24->(start+count<=24)%nat->(count<=8)%nat->
  gateway_response_context native stable discipline stream response readonly initial bytes before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_get64)[Vptr response(Ptrofs.repr(Z.of_nat start));Vint(Int.repr(Z.of_nat count))]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  returned=gateway_response_word_value bytes start count /\
  gateway_response_context native stable discipline stream response readonly initial bytes after next /\
  Forall gateway_quiet_event events.
Proof.
  intros LENGTH RANGE WIDTH READY RUN.
  set(context:=gateway_response_context native stable discipline stream response readonly initial bytes).
  set(part:=gateway_response_word_bytes bytes start count).
  set(offset:=Ptrofs.repr(Z.of_nat start)).
  assert(OFFSET:Ptrofs.unsigned offset=Z.of_nat start).
  { unfold offset;apply Ptrofs.unsigned_repr;change Ptrofs.max_unsigned with 18446744073709551615;lia. }
  destruct(gateway_response_word_slice before response bytes start count LENGTH RANGE(proj2 READY))as[PART_LENGTH PART_LOAD].
  change(length part=count)in PART_LENGTH.
  change(Mem.loadbytes before response(Z.of_nat start)(Z.of_nat count)=Some(inj_bytes part))in PART_LOAD.
  assert(LENGTH_VALUES:length(map Readers.byte_word part)=count)by(rewrite length_map;exact PART_LENGTH).
  assert(BOUND:Ptrofs.unsigned offset+Z.of_nat(length(map Readers.byte_word part))<=Ptrofs.modulus).
  { rewrite OFFSET,LENGTH_VALUES;change Ptrofs.modulus with 18446744073709551616;lia. }
  assert(INPUT:gateway_read_ready response offset(map Readers.byte_word part)before).
  { apply gateway_read_ready_from_bytes.
    - rewrite OFFSET,PART_LENGTH;change Ptrofs.modulus with 18446744073709551616;lia.
    - rewrite OFFSET,PART_LENGTH;exact PART_LOAD. }
  assert(LAW:gateway_coupled_private_contract backend(gateway_byte_region response(Ptrofs.unsigned offset)
    (length(map Readers.byte_word part)))context).
  { constructor;intros memory current changed future GOOD INTERFERENCE.
    destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None memory current changed future(proj1(proj1 GOOD))INTERFERENCE)
      as[SIDE[ACCESS FRAME]]. split.
    - eapply gateway_response_context_preserved;[exact GOOD|exact SIDE|exact ACCESS|exact FRAME].
    - eapply gateway_native_frame_restrict;[exact FRAME| |].
      + intros object position[SAME INSIDE];subst object;left;exact(proj1(proj2(proj2(proj1 GOOD)))) .
      + intros object position HERE BAD;exact BAD. }
  assert(BODY:gateway_steps backend(Clight.globalenv prog)
    (gateway_live(gateway_get_initial response offset(length(map Readers.byte_word part))Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)).
  { unfold gateway_get_initial;rewrite LENGTH_VALUES;exact RUN. }
  destruct(gateway_get64_shared_coupled backend(Clight.globalenv prog)context response offset(map Readers.byte_word part)
    before world events returned after next LAW READY ltac:(rewrite LENGTH_VALUES;exact WIDTH)BOUND INPUT BODY)
    as(actual&BEFORE&AFTER&VALUE&FINAL).
  assert(SAME:actual=part).
  { apply gateway_bytes_injective.
    rewrite OFFSET,length_map,PART_LENGTH in BEFORE;unfold inj_bytes in PART_LOAD|-*;congruence. }
  subst actual;split;[exact VALUE|]. split;[exact FINAL|].
  eapply gateway_readonly_run_events;[apply gateway_actual_get64_readonly|exact RUN].
Qed.
