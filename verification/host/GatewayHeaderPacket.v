(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Each real header word extends the same retained packet. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Memdata Events Clight.
Require Import Writers WriteBytes.
From HostGateway Require Import GatewaySource GatewayMachine GatewayStreamInterface GatewayThreadRuntime
  GatewayHeaderRuntime GatewayHeaderWords GatewayFramedRuntime GatewayRuntimeTrace GatewayReadonly
  GatewayWordsMemory GatewayWordReceipt GatewayHeaderPrefix GatewayWordData.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Record gateway_header_packet {World}native stable discipline mode object held readonly original origin
    (bytes:list Byte.int)memory world:Prop:={
  gateway_packet_resources:
    @gateway_header_resources World native stable discipline mode object held readonly original origin memory world;
  gateway_packet_writable:Mem.range_perm memory object 0 112 Cur Writable;
  gateway_packet_length:(length bytes<=112)%nat;
  gateway_packet_bytes:Mem.loadbytes memory object 0(Z.of_nat(length bytes))=Some(inj_bytes bytes)
}.

Section Packet.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native:World->block->Prop)(stable:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native stable discipline thread_errno).
Variable ge:Clight.genv.

Lemma gateway_header_packet_ambient mode object held readonly original origin bytes:
  gateway_ambient_closed backend
    (gateway_header_packet native stable discipline mode object held readonly original origin bytes).
Proof.
  intros before world after next[RESOURCES WRITABLE LENGTH BYTES]INTERFERENCE.
  destruct(gateway_header_resources_ambient backend io native stable discipline thread_errno runtime
    mode object held readonly original origin before world after next RESOURCES INTERFERENCE)as[NEXT FRAME].
  constructor;[exact NEXT| |exact LENGTH|].
  - intros position RANGE;apply(gateway_header_permissions _ _ _ _ _ _ _ _ _ _ _ NEXT).
    apply(gateway_header_permissions _ _ _ _ _ _ _ _ _ _ _ RESOURCES);apply WRITABLE;exact RANGE.
  - eapply Mem.loadbytes_unchanged_on;[exact FRAME| |exact BYTES].
    intros position RANGE;split;
      [left;exact(gateway_header_private _ _ _ _ _ _ _ _ _ _ _ RESOURCES)
      |unfold gateway_native_no_output;tauto].
Qed.

Theorem gateway_header_packet_put32 mode object held readonly original origin bytes value
    before world events returned after next:
  gateway_header_packet native stable discipline mode object held readonly original origin bytes before world->
  (length bytes+4<=112)%nat->
  (forall position,0<=position<112->~readonly object position)->
  gateway_steps backend ge
    (gateway_live(writer_initial f_host_put32 object(Ptrofs.repr(Z.of_nat(length bytes)))(Vint value)Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  returned=Vundef /\
  gateway_header_packet native stable discipline mode object held readonly original origin
    (bytes++gateway_native_bytes(put32_values value))after next /\Forall gateway_quiet_event events.
Proof.
  intros PACKET SPACE DISJOINT RUN.
  destruct PACKET as[RESOURCES WRITABLE LENGTH BYTES].
  assert(OFFSET:Ptrofs.unsigned(Ptrofs.repr(Z.of_nat(length bytes)))=Z.of_nat(length bytes)).
  { apply Ptrofs.unsigned_repr;change Ptrofs.max_unsigned with 18446744073709551615;lia. }
  pose proof(gateway_header_resources_prefix native stable discipline mode object held readonly original origin
    before world bytes RESOURCES BYTES)as PREFIX.
  pose proof(gateway_put32_runtime_path backend io native stable discipline thread_errno runtime ge
    mode object(Ptrofs.repr(Z.of_nat(length bytes)))value held
    (gateway_header_prefix_region readonly object(Z.of_nat(length bytes)))before world before
    ltac:(rewrite OFFSET;change Ptrofs.modulus with 18446744073709551616;lia)
    ltac:(rewrite OFFSET;
      intros position RANGE[OLD|[SAME EARLIER]];[apply(DISJOINT position);[lia|exact OLD]|lia]))as SCRIPT.
  assert(INITIAL:gateway_header_stage native stable discipline mode object held
    (gateway_header_prefix_region readonly object(Z.of_nat(length bytes)))before world
    (Ptrofs.unsigned(Ptrofs.repr(Z.of_nat(length bytes))))4 [] before world).
  { split;[exact PREFIX|]. apply gateway_bytes_initial.
    rewrite OFFSET;intros position RANGE;apply WRITABLE;lia. }
  destruct(gateway_runtime_path_return_exact backend ge _ _ _ _ before world events returned after next
    INITIAL SCRIPT RUN)as[VALUE[FINAL WORD]].
  split;[exact VALUE|]. split.
  - constructor.
    + eapply gateway_header_resources_compose;[exact RESOURCES|exact FINAL|].
      intros;left;assumption.
    + intros position RANGE;apply(gateway_header_permissions _ _ _ _ _ _ _ _ _ _ _ FINAL).
      apply WRITABLE;exact RANGE.
    + unfold gateway_native_bytes,put32_values;rewrite length_app,length_map,length_map;cbn[length];lia.
    + eapply gateway_header_prefix_extend;[exact BYTES| |exact(gateway_header_frame _ _ _ _ _ _ _ _ _ _ _ FINAL)].
      rewrite gateway_native_memvals;change(Z.of_nat(length(gateway_native_bytes(put32_values value))))with 4.
      rewrite OFFSET in WORD.
      exact(gateway_bytes_complete object(Z.of_nat(length bytes))4(put32_values value)after WORD eq_refl).
  - exact(gateway_runtime_path_return_events backend ge _ _ _ _ before world events returned after next
      INITIAL SCRIPT RUN).
Qed.

Theorem gateway_header_packet_put64 mode object held readonly original origin bytes value
    before world events returned after next:
  gateway_header_packet native stable discipline mode object held readonly original origin bytes before world->
  (length bytes+8<=112)%nat->
  (forall position,0<=position<112->~readonly object position)->
  gateway_steps backend ge
    (gateway_live(writer_initial f_host_put64 object(Ptrofs.repr(Z.of_nat(length bytes)))(Vlong value)Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  returned=Vundef /\
  gateway_header_packet native stable discipline mode object held readonly original origin
    (bytes++gateway_native_bytes(put64_values value))after next /\Forall gateway_quiet_event events.
Proof.
  intros PACKET SPACE DISJOINT RUN.
  destruct PACKET as[RESOURCES WRITABLE LENGTH BYTES].
  assert(OFFSET:Ptrofs.unsigned(Ptrofs.repr(Z.of_nat(length bytes)))=Z.of_nat(length bytes)).
  { apply Ptrofs.unsigned_repr;change Ptrofs.max_unsigned with 18446744073709551615;lia. }
  pose proof(gateway_header_resources_prefix native stable discipline mode object held readonly original origin
    before world bytes RESOURCES BYTES)as PREFIX.
  pose proof(gateway_put64_runtime_path backend io native stable discipline thread_errno runtime ge
    mode object(Ptrofs.repr(Z.of_nat(length bytes)))value held
    (gateway_header_prefix_region readonly object(Z.of_nat(length bytes)))before world before
    ltac:(rewrite OFFSET;change Ptrofs.modulus with 18446744073709551616;lia)
    ltac:(rewrite OFFSET;
      intros position RANGE[OLD|[SAME EARLIER]];[apply(DISJOINT position);[lia|exact OLD]|lia]))as SCRIPT.
  assert(INITIAL:gateway_header_stage native stable discipline mode object held
    (gateway_header_prefix_region readonly object(Z.of_nat(length bytes)))before world
    (Ptrofs.unsigned(Ptrofs.repr(Z.of_nat(length bytes))))8 [] before world).
  { split;[exact PREFIX|]. apply gateway_bytes_initial.
    rewrite OFFSET;intros position RANGE;apply WRITABLE;lia. }
  destruct(gateway_runtime_path_return_exact backend ge _ _ _ _ before world events returned after next
    INITIAL SCRIPT RUN)as[VALUE[FINAL WORD]].
  split;[exact VALUE|]. split.
  - constructor.
    + eapply gateway_header_resources_compose;[exact RESOURCES|exact FINAL|].
      intros;left;assumption.
    + intros position RANGE;apply(gateway_header_permissions _ _ _ _ _ _ _ _ _ _ _ FINAL).
      apply WRITABLE;exact RANGE.
    + unfold gateway_native_bytes,put64_values;rewrite length_app,length_map,length_map;cbn[length];lia.
    + eapply gateway_header_prefix_extend;[exact BYTES| |exact(gateway_header_frame _ _ _ _ _ _ _ _ _ _ _ FINAL)].
      rewrite gateway_native_memvals;change(Z.of_nat(length(gateway_native_bytes(put64_values value))))with 8.
      rewrite OFFSET in WORD.
      exact(gateway_bytes_complete object(Z.of_nat(length bytes))8(put64_values value)after WORD eq_refl).
  - exact(gateway_runtime_path_return_events backend ge _ _ _ _ before world events returned after next
      INITIAL SCRIPT RUN).
Qed.
End Packet.
