(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Decoder context projections retain the same actual stream and memory. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayStreamInterface
  GatewayValueEntry GatewayValueContext GatewayValueStack GatewayValueEnvironment GatewayNativeRegions GatewayScopedMemory.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_value_context_discipline {World}native stable first second stream_block stream_offset
    initial readonly original memory world :
  (forall memory world,first None memory world ->second None memory world) ->
  @gateway_value_context World native stable first stream_block stream_offset initial readonly original memory world ->
  gateway_value_context native stable second stream_block stream_offset initial readonly original memory world.
Proof. intros MAP[SIDE REST];split;[apply MAP;exact SIDE|exact REST]. Qed.

Lemma gateway_value_active_discipline {World}native stable first second slots stream_block stream_offset
    initial readonly original memory world :
  (forall memory world,first None memory world ->second None memory world) ->
  @gateway_value_active World native stable first slots stream_block stream_offset initial readonly original memory world ->
  gateway_value_active native stable second slots stream_block stream_offset initial readonly original memory world.
Proof. intros MAP[CONTEXT REST];split;[eapply gateway_value_context_discipline;eassumption|exact REST]. Qed.

Lemma gateway_value_context_native_region {World}native stable discipline stream_block stream_offset
    initial readonly original memory world :
  @gateway_value_context World native stable discipline stream_block stream_offset initial readonly original memory world ->
  (forall object position,readonly object position ->native world object) ->
  gateway_native_region_owned native(gateway_value_input_region stream_block stream_offset readonly)memory world.
Proof.
  intros[SIDE[STREAM[READONLY[INPUT FRAME]]]]PRIVATE object position[REGION|READ].
  - destruct REGION as[SAME RANGE];subst object;split;[|exact STREAM].
    eapply Mem.perm_valid_block;apply(gateway_value_stream_owned _ _ _ _ _ INPUT(Ptrofs.unsigned stream_offset));lia.
  - split;[eapply gateway_value_readonly_live;[exact INPUT|exact READ]|eapply PRIVATE;exact READ].
Qed.

Lemma gateway_value_active_avoids {World}native stable discipline slots stream_block stream_offset
    initial readonly original memory world :
  @gateway_value_active World native stable discipline slots stream_block stream_offset initial readonly original memory world ->
  gateway_environment_avoids(gateway_value_input_region stream_block stream_offset readonly)(gateway_value_environment slots).
Proof.
  intros[CONTEXT[TAG[SIZE[TAG_OWN[SIZE_OWN[DIFFERENT[TAG_STREAM[SIZE_STREAM[TAG_READ SIZE_READ]]]]]]]]]
    identifier object ty position LOOK[REGION|READ].
  - destruct REGION as[SAME RANGE];subst object.
    destruct(gateway_value_environment_slots _ _ _ _ LOOK);congruence.
  - destruct(gateway_value_environment_slots _ _ _ _ LOOK)as[SAME|SAME];subst object;
      [apply(TAG_READ position)|apply(SIZE_READ position)];exact READ.
Qed.

Theorem gateway_value_context_after_native_region {World Event}(backend:gateway_backend World Event)io native stable
    discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    stream_block stream_offset initial readonly original before world after next :
  gateway_value_context native stable discipline stream_block stream_offset initial readonly original before world ->
  gateway_native_region_context native discipline None(gateway_value_input_region stream_block stream_offset readonly)
    before after next ->
  gateway_value_context native stable discipline stream_block stream_offset initial readonly original after next.
Proof.
  intros[OLD_SIDE[OLD_STREAM[OLD_READONLY[INPUT OLD_FRAME]]]][SIDE[OWNED FRAME]].
  split;[exact SIDE|]. split.
  - exact(proj2(OWNED stream_block(Ptrofs.unsigned stream_offset)ltac:(left;split;[reflexivity|lia]))).
  - split.
    + intros object position READ;eapply gateway_thread_native_stable;[exact runtime|exact SIDE|].
      exact(proj2(OWNED object position(or_intror READ))).
    + split;[eapply gateway_value_inputs_frame;[exact FRAME|exact INPUT]|].
      eapply Mem.unchanged_on_trans;[exact OLD_FRAME|].
      eapply Mem.unchanged_on_implies;[exact FRAME|intros;right;assumption].
Qed.
