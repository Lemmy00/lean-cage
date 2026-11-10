(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Each actual caller array keeps its own permission history. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Events Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayStreamInterface
  GatewayCallerBuffers GatewayCallerClock GatewayClock GatewayClockRuntime
  GatewayPairBuffers GatewaySpawnRuntime GatewaySpawnResources.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_caller_family {World}(native_private:World->block->Prop)
    (stable_readonly:World->block->Z->Prop)(readonly:block->Z->Prop)(selected:block->Prop)
    reference owner(memory:mem)(world:World):Prop:=
  forall target,selected target->
    gateway_caller_buffers native_private stable_readonly readonly target reference owner memory world.

Theorem gateway_caller_family_refl {World}(native_private:World->block->Prop)
    (stable_readonly:World->block->Z->Prop) readonly selected memory world:
  (forall target,selected target->Mem.valid_block memory target /\native_private world target)->
  gateway_caller_readonly native_private stable_readonly readonly memory world->
  gateway_caller_family native_private stable_readonly readonly selected memory world memory world.
Proof.
  intros OWNED READONLY target SELECTED;destruct(OWNED target SELECTED)as[LIVE PRIVATE].
  apply gateway_caller_buffers_refl;assumption.
Qed.

Theorem gateway_caller_family_pair_laws {World Event}(backend:gateway_backend World Event)io native_private
    stable_readonly discipline thread_errno
    (runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    readonly selected destination offset reference owner:
  (forall position,~readonly destination position)->
  gateway_pair_buffer_laws backend native_private stable_readonly discipline destination offset
    (gateway_caller_family native_private stable_readonly readonly selected reference owner).
Proof.
  intro DISJOINT;constructor.
  - intros before world after next SIDE HISTORY INTERFERENCE target SELECTED.
    destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next SIDE INTERFERENCE)
      as[AFTER[ACCESS FRAME]]. eapply gateway_caller_buffers_no_output;
      [exact(HISTORY target SELECTED)|exact ACCESS|exact FRAME].
  - intros before world after next HISTORY ACCESS FRAME target SELECTED.
    eapply gateway_caller_buffers_no_output;[exact(HISTORY target SELECTED)|exact ACCESS|exact FRAME].
  - intros before world after next HISTORY ACCESS PERMISSIONS FRAME target SELECTED.
    eapply gateway_caller_buffers_operation;
      [exact(HISTORY target SELECTED)|exact ACCESS|exact FRAME|apply gateway_native_region_dec| | |].
    + intros object position HERE[SAME RANGE];subst object;exact(DISJOINT position HERE).
    + intros position kind permission[SAME RANGE];subst target;apply PERMISSIONS;exact RANGE.
    + intros object position READABLE[SAME RANGE];subst object.
      apply(proj1(PERMISSIONS position Cur Readable RANGE));exact READABLE.
  - intros before world after position value HISTORY STORE target SELECTED.
    eapply gateway_caller_buffers_store;[exact(HISTORY target SELECTED)|exact STORE|exact DISJOINT].
Qed.

Theorem actual_caller_clock_family {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    io native_private stable_readonly discipline thread_errno
    (runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    readonly selected reference owner before world events returned after next symbol descriptor:
  sizeof(genv_cenv ge)clock_sample_type=16->
  Genv.find_symbol ge _clock_gettime=Some symbol->
  Genv.find_funct_ptr ge symbol=Some clock_gettime_definition->
  discipline None before world->
  gateway_caller_family native_private stable_readonly readonly selected reference owner before world->
  (exists target,selected target)->
  gateway_steps backend ge(gateway_live(Callstate(Internal f_host_now)[]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  discipline None after next /\
  gateway_caller_family native_private stable_readonly readonly selected reference owner after next /\
  gateway_received_bytes io descriptor events=[].
Proof.
  intros SIZE SYMBOL FUNCTION SIDE HISTORY NONEMPTY RUN.
  assert(AFTER:discipline None after next).
  { eapply actual_clock_preserves_thread;[exact runtime|exact SIZE|exact SYMBOL|exact FUNCTION|exact SIDE|exact RUN]. }
  split;[exact AFTER|]. split.
  - intros target SELECTED.
    destruct(actual_caller_clock_complete backend ge io native_private stable_readonly discipline thread_errno runtime
      readonly target reference owner before world events returned after next symbol descriptor
      SIZE SYMBOL FUNCTION(conj SIDE(HISTORY target SELECTED))RUN)as[FINAL EMPTY]. exact(proj2 FINAL).
  - destruct NONEMPTY as[target SELECTED].
    destruct(actual_caller_clock_complete backend ge io native_private stable_readonly discipline thread_errno runtime
      readonly target reference owner before world events returned after next symbol descriptor
      SIZE SYMBOL FUNCTION(conj SIDE(HISTORY target SELECTED))RUN)as[FINAL EMPTY]. exact EMPTY.
Qed.
