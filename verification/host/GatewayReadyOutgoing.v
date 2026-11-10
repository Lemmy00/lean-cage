(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Actual readiness sends cancellation only on its distinct control FD. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Clight.
From HostGateway Require Import GatewayMachine GatewaySource GatewaySendReady GatewaySendChannels
  GatewayReadyBindings GatewayOutgoingReadyComplete GatewayReadyProtected GatewayReadStable
  GatewayReadContext GatewayReadMemory GatewayThreadRuntime GatewayStreamInterface GatewayBufferReference.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_actual_ready_no_data_send {World Event} (backend : gateway_backend World Event)
    ge io native_private stable_readonly discipline thread_errno
    (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    (bindings : gateway_ready_bindings ge) :
  gateway_ready_no_data_send_source backend ge io native_private stable_readonly (discipline None).
Proof.
  intros before world stream_block stream_offset initial data_block data_offset amount readonly direction
    events after next SIDE STREAM DATA IMMUTABLE INPUT DISTINCT DIRECTION RUN.
  set (kept := gateway_ready_protected readonly data_block data_offset amount).
  set (protected := gateway_stable_readonly stable_readonly before world stream_block stream_block kept).
  assert (DUMMY_INPUT : gateway_read_inputs before stream_block stream_offset initial stream_block Ptrofs.zero 0 kept).
  { apply gateway_ready_protected_inputs; exact INPUT. }
  assert (KEPT_STABLE : forall object position, kept object position -> stable_readonly world object position).
  { eapply gateway_ready_protected_stable; [exact runtime |exact SIDE |exact DATA |exact IMMUTABLE]. }
  assert (DUMMY_CONTEXT : gateway_read_context native_private stable_readonly discipline None
    stream_block stream_offset initial stream_block Ptrofs.zero 0 kept before world).
  { split; [exact SIDE |]. split; [exact STREAM |]. split; [exact STREAM |]. split; assumption. }
  pose proof (gateway_read_stable_context native_private stable_readonly discipline None before world
    stream_block stream_offset initial stream_block Ptrofs.zero 0 kept DUMMY_CONTEXT) as PROTECTED_CONTEXT.
  assert (CHANNELS : gateway_distinct_channels initial) by exact DISTINCT.
  destruct (GatewayOutgoingReadyComplete.actual_ready_complete backend ge io native_private stable_readonly
    discipline thread_errno runtime bindings stream_block stream_offset initial stream_block Ptrofs.zero 0
    protected direction before world events after next (outgoing_channels := CHANNELS)
    PROTECTED_CONTEXT RUN) as (final & FINAL_CONTEXT & CHANGE & BUFFER & NATIVE & EMPTY).
  exact EMPTY.
Qed.
