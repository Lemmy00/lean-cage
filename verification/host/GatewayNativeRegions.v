(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Caller regions retain their actual native allocation authority. *)
From Stdlib Require Import ZArith.
From compcert Require Import Integers AST Values Memory.
From HostGateway Require Import GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewayOperations
  GatewayObjects GatewayPython GatewayFrames GatewayFramedRuntime.

Definition gateway_native_region_owned {World}(native:World->block->Prop)(protected:block->Z->Prop)
    memory world :Prop:=
  forall object position,protected object position ->Mem.valid_block memory object /\native world object.

Lemma gateway_native_region_memory_frame {World}native protected before after world :
  @gateway_native_region_owned World native protected before world ->
  Mem.unchanged_on protected before after ->gateway_native_region_owned native protected after world.
Proof.
  intros OWNED FRAME object position MEMBER;destruct(OWNED object position MEMBER)as[LIVE PRIVATE];split;
    [eapply Mem.valid_block_unchanged_on;[exact FRAME|exact LIVE]|exact PRIVATE].
Qed.

Lemma gateway_native_region_restrict {World}native stable protected(output:block->Z->Prop)before world after :
  @gateway_native_region_owned World native protected before world ->
  (forall object position,protected object position ->~output object position) ->
  gateway_native_frame native stable output world before after ->Mem.unchanged_on protected before after.
Proof.
  intros OWNED OUTPUT FRAME;eapply Mem.unchanged_on_implies;[exact FRAME|].
  intros object position MEMBER LIVE;split;[left;exact(proj2(OWNED object position MEMBER))|exact(OUTPUT object position MEMBER)].
Qed.

Lemma gateway_native_region_ambient {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)mode protected before world after next :
  discipline mode before world ->gateway_native_region_owned native protected before world ->
  gateway_interference backend before world after next ->
  discipline mode after next /\gateway_native_region_owned native protected after next /\
    Mem.unchanged_on protected before after.
Proof.
  intros SIDE OWNED INTERFERENCE.
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime mode _ _ _ _ SIDE INTERFERENCE)
    as[NEXT[[NATIVE STABLE]FRAME]].
  assert(REGION_FRAME:Mem.unchanged_on protected before after).
  { eapply gateway_native_region_restrict;[exact OWNED| |exact FRAME].
    intros;unfold gateway_native_no_output;tauto. }
  split;[exact NEXT|]. split;[|exact REGION_FRAME].
  intros object position MEMBER;destruct(OWNED object position MEMBER)as[LIVE PRIVATE];split.
  - eapply Mem.valid_block_unchanged_on;[exact REGION_FRAME|exact LIVE].
  - apply NATIVE;assumption.
Qed.

Definition gateway_native_region_context {World}native(discipline:option val->mem->World->Prop)
    mode protected original memory world :Prop:=
  discipline mode memory world /\@gateway_native_region_owned World native protected memory world /\
    Mem.unchanged_on protected original memory.

Lemma gateway_native_region_context_ambient {World Event}(backend:gateway_backend World Event)io native stable discipline
    thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)mode protected original :
  gateway_runtime_discipline backend(gateway_native_region_context native discipline mode protected original).
Proof.
  intros before world after next[SIDE[OWNED FRAME]]INTERFERENCE.
  destruct(gateway_native_region_ambient backend io native stable discipline thread_errno runtime mode protected
    before world after next SIDE OWNED INTERFERENCE)as[NEXT[AFTER STEP_FRAME]].
  split;[exact NEXT|]. split;[exact AFTER|eapply Mem.unchanged_on_trans;eassumption].
Qed.

Lemma gateway_constructor_native_region {World}(python:World->python_world)objects protected before world result after next value :
  gateway_native_region_owned(fun world object=>gateway_native_private(python world)object)protected before world ->
  gateway_constructor_return(python world)(objects world)before result(python next)(objects next)after value ->
  gateway_native_region_owned(fun world object=>gateway_native_private(python world)object)protected after next /\
    Mem.unchanged_on protected before after.
Proof.
  intros OWNED RETURN.
  assert(FRAME:Mem.unchanged_on protected before after).
  { eapply Mem.unchanged_on_implies;[exact(gateway_constructor_native _ _ _ _ _ _ _ _ RETURN)|].
    intros object position MEMBER LIVE;exact(proj2(OWNED object position MEMBER)). }
  split;[|exact FRAME]. intros object position MEMBER;destruct(OWNED object position MEMBER)as[LIVE PRIVATE];split.
  - eapply Mem.valid_block_unchanged_on;[exact FRAME|exact LIVE].
  - eapply gateway_constructor_native_retained;[exact RETURN|exact LIVE|exact PRIVATE].
Qed.
