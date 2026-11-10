(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Actual readiness owns its entry, complete retry loop and return. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewaySource GatewayReadySource GatewayReadyBindings GatewayReadyContext
  GatewayReadyEntry GatewayReadyLoop GatewayThreadRuntime GatewayStreamInterface GatewayReadContext GatewayBufferReference
  GatewayTransferMath.
Import ListNotations.

Theorem actual_ready_complete {World Event} (backend : gateway_backend World Event) ge
    (io : Event -> option gateway_native_io) native_private stable_readonly discipline thread_errno
    (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    (bindings : gateway_ready_bindings ge)
    stream_block stream_offset initial data_block data_offset amount readonly direction before world events after next :
  gateway_read_context native_private stable_readonly discipline None stream_block stream_offset initial
    data_block data_offset amount readonly before world ->
  gateway_steps backend ge
    (gateway_live (Callstate (Internal f_host_ready) [Vptr stream_block stream_offset; Vint direction] Kstop before) world)
    events (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) ->
  exists final,
    gateway_read_context native_private stable_readonly discipline None stream_block stream_offset final
      data_block data_offset amount readonly after next /\ gateway_stream_transport_after initial final /\
    gateway_buffer_reference readonly stream_block data_block before after /\
    gateway_native_reference native_private before world after next /\
    gateway_received_bytes io (stream_descriptor initial) events = [].
Proof.
  intros READY RUN.
  assert (INPUT : gateway_owned_buffer_context native_private stable_readonly discipline stream_block data_block
    stream_offset data_offset initial amount readonly before world None before world).
  { split; [exact READY |]. split; [apply gateway_buffer_reference_refl |apply gateway_native_reference_refl]. }
  destruct (actual_ready_entry_slice backend ge io native_private stable_readonly discipline thread_errno runtime
    stream_block stream_offset initial data_block data_offset amount readonly before world
    direction before world events (Vint Int.zero) after next (proj1 bindings) INPUT RUN)
    as (prefix & suffix & memory & called_world & item & EVENTS & EMPTY & SLICE & PREFIX & BODY).
  assert (STREAM : (ready_temporaries (Vptr stream_block stream_offset) direction) ! _stream =
    Some (Vptr stream_block stream_offset)).
  { unfold ready_temporaries; rewrite PTree.gso by discriminate; apply PTree.gss. }
  destruct (actual_ready_loop_complete backend ge io native_private stable_readonly discipline thread_errno runtime bindings
    stream_block stream_offset initial data_block data_offset amount readonly before world
    item initial (ready_temporaries (Vptr stream_block stream_offset) direction) memory called_world suffix after next
    STREAM SLICE BODY) as (final & CHANGE & (CONTEXT & BUFFER & NATIVE) & BODY_EMPTY).
  exists final; split; [exact CONTEXT |]. split; [exact CHANGE |]. split; [exact BUFFER |]. split; [exact NATIVE |].
  rewrite EVENTS, gateway_received_bytes_append, EMPTY, BODY_EMPTY; reflexivity.
Qed.
