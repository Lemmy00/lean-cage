(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Decoder stack cleanup preserves the same caller stream and readonly cells. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers Values Memory Ctypes Clight.
From HostGateway Require Import GatewayValueEntry GatewayValueContext GatewayValueStack GatewayValueEnvironment
  GatewayNativeRegions GatewayScopedMemory GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_value_return_native_region {World}native stable discipline stream_block stream_offset initial readonly original memory world :
  @gateway_value_context World native stable discipline stream_block stream_offset initial readonly original memory world ->
  (forall object position,readonly object position ->native world object) ->
  gateway_native_region_owned native(gateway_value_input_region stream_block stream_offset readonly)memory world.
Proof.
  intros[SIDE[STREAM[STABLE[INPUT FRAME]]]]NATIVE object position[[SAME RANGE]|READ].
  - subst object;split;[eapply Mem.perm_valid_block;apply(gateway_value_stream_owned _ _ _ _ _ INPUT);exact RANGE|exact STREAM].
  - split;[eapply gateway_value_readonly_live;eassumption|eapply NATIVE;exact READ].
Qed.

Lemma gateway_value_environment_avoids_inputs {World}native stable discipline slots stream_block stream_offset initial readonly original memory world :
  @gateway_value_active World native stable discipline slots stream_block stream_offset initial readonly original memory world ->
  gateway_environment_avoids(gateway_value_input_region stream_block stream_offset readonly)(gateway_value_environment slots).
Proof.
  intros[CONTEXT[TAG[SIZE[TAG_OWN[SIZE_OWN[DIFFERENT[TAG_STREAM[SIZE_STREAM[TAG_READ SIZE_READ]]]]]]]]].
  intros identifier object ty position LOOK REGION.
  destruct(gateway_value_environment_slots _ _ _ _ LOOK)as[SAME|SAME];subst object;
    destruct REGION as[[SAME RANGE]|READ];[congruence|eapply TAG_READ;exact READ|congruence|eapply SIZE_READ;exact READ].
Qed.

Theorem gateway_value_context_return_frame {World Event}(backend:GatewayMachine.gateway_backend World Event)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    stream_block stream_offset initial readonly original before world after next :
  gateway_value_context native stable discipline stream_block stream_offset initial readonly original before world ->
  discipline None after next ->
  gateway_native_region_owned native(gateway_value_input_region stream_block stream_offset readonly)after next ->
  Mem.unchanged_on(gateway_value_input_region stream_block stream_offset readonly)before after ->
  gateway_value_context native stable discipline stream_block stream_offset initial readonly original after next.
Proof.
  intros[SIDE[STREAM[STABLE[INPUT PREVIOUS]]]]NEXT OWNED FRAME.
  split;[exact NEXT|]. split.
  - exact(proj2(OWNED stream_block(Ptrofs.unsigned stream_offset)ltac:(left;split;[reflexivity|lia]))).
  - split.
    + intros object position READ;eapply gateway_thread_native_stable;[exact runtime|exact NEXT|].
      exact(proj2(OWNED object position(or_intror READ))).
    + split;[eapply gateway_value_inputs_frame;eassumption|].
      eapply Mem.unchanged_on_trans;[exact PREVIOUS|].
      eapply Mem.unchanged_on_implies;[exact FRAME|intros;right;assumption].
Qed.
