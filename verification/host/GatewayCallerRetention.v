(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Sequential setup retains older caller bytes and allocation identities. *)
From Stdlib Require Import ZArith.
From compcert Require Import Maps AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewayCallerBuffers GatewayCallerFamily GatewayBufferReference
  GatewayLocalRuntime GatewayStackAllocation.

Theorem gateway_caller_buffers_rebase {World}(native_private:World->block->Prop)
    (stable_readonly:World->block->Z->Prop)readonly expanded target reference owner before world after next:
  gateway_caller_buffers native_private stable_readonly readonly target reference owner before world->
  gateway_caller_buffers native_private stable_readonly expanded target before world after next->
  (forall object position,readonly object position->expanded object position)->
  gateway_caller_buffers native_private stable_readonly readonly target reference owner after next.
Proof.
  intros[OLD_LIVE[OLD_PRIVATE[OLD_READONLY[OLD_BUFFER[OLD_NATIVE OLD_STABLE]]]]]
    [LIVE[PRIVATE[READONLY[BUFFER[NATIVE STABLE]]]]]INCLUDED.
  split;[exact LIVE|]. split;[exact PRIVATE|]. split.
  - intros object position HERE;apply READONLY,INCLUDED;exact HERE.
  - split.
    + eapply gateway_buffer_reference_transitive;[exact OLD_BUFFER|]. split.
      * eapply Mem.unchanged_on_implies;[exact(proj1 BUFFER)|]. intros object position HERE VALID;apply INCLUDED;exact HERE.
      * exact(proj2 BUFFER).
    + split.
      * eapply gateway_native_reference_transitive;[exact OLD_NATIVE|exact NATIVE].
      * eapply gateway_stable_reference_transitive;[exact OLD_STABLE|exact STABLE].
Qed.

Theorem gateway_caller_family_rebase {World}(native_private:World->block->Prop)
    (stable_readonly:World->block->Z->Prop)readonly expanded selected reference owner before world after next:
  gateway_caller_family native_private stable_readonly readonly selected reference owner before world->
  gateway_caller_family native_private stable_readonly expanded selected before world after next->
  (forall object position,readonly object position->expanded object position)->
  gateway_caller_family native_private stable_readonly readonly selected reference owner after next.
Proof.
  intros OLD NEW INCLUDED target SELECTED;eapply gateway_caller_buffers_rebase;
    [exact(OLD target SELECTED)|exact(NEW target SELECTED)|exact INCLUDED].
Qed.

Theorem gateway_caller_family_environment {World}(native_private:World->block->Prop)
    (stable_readonly:World->block->Z->Prop)readonly selected reference owner memory world environment:
  gateway_caller_family native_private stable_readonly readonly selected reference owner memory world->
  (forall identifier object ty,environment!identifier=Some(object,ty)->selected object)->
  gateway_native_environment native_private world memory environment.
Proof.
  intros FAMILY SELECTED identifier object ty LOOK.
  pose proof(FAMILY object(SELECTED identifier object ty LOOK))as[LIVE[PRIVATE REST]];split;assumption.
Qed.

Theorem gateway_caller_family_stack {World}(native_private:World->block->Prop)
    (stable_readonly:World->block->Z->Prop)readonly selected reference owner memory world environment:
  gateway_caller_family native_private stable_readonly readonly selected reference owner memory world->
  (forall identifier object ty,environment!identifier=Some(object,ty)->selected object)->
  gateway_stack_environment reference environment->gateway_stack_environment memory environment.
Proof.
  intros FAMILY SELECTED[LIVE DISTINCT];split;[|exact DISTINCT].
  intros identifier object ty LOOK;exact(proj1(FAMILY object(SELECTED identifier object ty LOOK))).
Qed.
