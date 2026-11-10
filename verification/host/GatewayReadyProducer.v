(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: The complete actual source supplies readiness to the real read caller. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Clight.
From HostGateway Require Import GatewayMachine GatewaySource GatewayReadyInterface GatewayReadyBindings GatewayReadyComplete
  GatewayReadyProtected GatewayReadStable GatewayReadContext GatewayReadMemory GatewayThreadRuntime GatewayStreamInterface
  GatewayBufferReference.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_ready_producer_of_runtime {World Event} (backend : gateway_backend World Event) ge io
    native_private stable_readonly discipline thread_errno
    (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    (bindings : gateway_ready_bindings ge) :
  gateway_ready_source_producer backend ge io native_private stable_readonly (discipline None).
Proof.
  intros before world stream_block stream_offset initial data_block data_offset amount readonly direction
    events after next SIDE STREAM DATA IMMUTABLE INPUT DIRECTION RUN.
  set (kept := gateway_ready_protected readonly data_block data_offset amount).
  set (protected := gateway_stable_readonly stable_readonly before world stream_block stream_block kept).
  assert (DUMMY_INPUT : gateway_read_inputs before stream_block stream_offset initial stream_block Ptrofs.zero 0 kept)
    by (apply gateway_ready_protected_inputs; exact INPUT).
  assert (KEPT_STABLE : forall object position, kept object position -> stable_readonly world object position).
  { eapply gateway_ready_protected_stable; [exact runtime |exact SIDE |exact DATA |exact IMMUTABLE]. }
  assert (DUMMY_CONTEXT : gateway_read_context native_private stable_readonly discipline None
    stream_block stream_offset initial stream_block Ptrofs.zero 0 kept before world).
  { split; [exact SIDE |]. split; [exact STREAM |]. split; [exact STREAM |]. split; assumption. }
  pose proof (gateway_read_stable_context native_private stable_readonly discipline None before world stream_block stream_offset
    initial stream_block Ptrofs.zero 0 kept DUMMY_CONTEXT) as PROTECTED_CONTEXT.
  destruct (actual_ready_complete backend ge io native_private stable_readonly discipline thread_errno runtime bindings
    stream_block stream_offset initial stream_block Ptrofs.zero 0 protected direction before world events after next
    PROTECTED_CONTEXT RUN) as (final & FINAL_CONTEXT & CHANGE & (FRAME & PERMISSIONS) & NATIVE & EMPTY).
  assert (INCLUDED : forall object position, kept object position -> protected object position).
  { intros object position HERE; left; exact HERE. }
  assert (AFTER_SIDE : discipline None after next) by exact (proj1 FINAL_CONTEXT).
  assert (AFTER_STREAM : native_private next stream_block) by exact (proj1 (proj2 FINAL_CONTEXT)).
  destruct (NATIVE data_block (gateway_read_data_live _ _ _ _ _ _ _ _ INPUT) DATA) as [DATA_LIVE AFTER_DATA].
  assert (FINAL_INPUT : gateway_read_inputs after stream_block stream_offset final data_block data_offset amount readonly).
  { eapply gateway_ready_recover_inputs;
      [exact INPUT |exact (proj2 (proj2 (proj2 (proj2 FINAL_CONTEXT)))) |exact INCLUDED |exact FRAME |exact DATA_LIVE]. }
  assert (AFTER_READONLY : forall object position, readonly object position -> stable_readonly next object position).
  { intros object position HERE; apply (proj1 (proj2 (proj2 (proj2 FINAL_CONTEXT)))).
    apply INCLUDED; left; exact HERE. }
  exists final; split; [exact FINAL_INPUT |]. split; [exact CHANGE |]. split.
  - eapply Mem.unchanged_on_implies; [exact FRAME |]. intros object position HERE LIVE; apply INCLUDED; exact HERE.
  - split; [exact EMPTY |]. split; [exact AFTER_SIDE |]. split; [exact AFTER_STREAM |]. split; [exact AFTER_DATA |].
    split; [exact AFTER_READONLY |]. split.
    + intros position kind permission RANGE; apply (PERMISSIONS stream_block (or_introl eq_refl) position kind permission).
    + split.
      * intros object LIVE PRIVATE; exact (proj2 (NATIVE object LIVE PRIVATE)).
      * eapply gateway_read_stable_retained; [exact runtime |exact FINAL_CONTEXT].
Qed.
