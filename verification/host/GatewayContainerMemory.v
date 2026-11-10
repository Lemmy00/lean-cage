(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: One builtin container allocation preserves the same guarded stream,
   initialized count and live private parser storage. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayObjectDiscipline
  GatewayValueEntry GatewayValueContext GatewayValueStack GatewayValueRegions GatewayScalarFrames
  GatewayScalarConstructorMemory GatewayContainerLength GatewayContainerGuards GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_value_active_readonly_relabel {World}native stable discipline replacement slots stream_block stream_offset initial
    readonly original memory world:
  @gateway_value_active World native stable discipline slots stream_block stream_offset initial readonly original memory world->
  (forall candidate position,readonly candidate position->replacement world candidate position)->
  gateway_value_active native replacement discipline slots stream_block stream_offset initial readonly original memory world.
Proof.
  intros[[SIDE[STREAM[STABLE[INPUT FRAME]]]]REST]NEW_STABLE.
  split;[|exact REST]. split;[exact SIDE|]. split;[exact STREAM|]. split;[exact NEW_STABLE|]. split;assumption.
Qed.

Lemma gateway_container_counted_readonly_relabel {World}native stable discipline replacement container slots stream_block stream_offset
    initial readonly original size memory world:
  @gateway_container_counted World native stable discipline container slots stream_block stream_offset initial readonly original size memory world->
  (forall candidate position,readonly candidate position->replacement world candidate position)->
  gateway_container_counted native replacement discipline container slots stream_block stream_offset initial readonly original size memory world.
Proof.
  intros[[ACTIVE TAG]SIZE]NEW_STABLE;split;[split;[eapply gateway_value_active_readonly_relabel;eassumption|exact TAG]|exact SIZE].
Qed.

Lemma gateway_container_counted_effect {World}native stable discipline container slots stream_block stream_offset initial
    readonly original size before world after next:
  @gateway_container_counted World native stable discipline container slots stream_block stream_offset initial readonly original size before world->
  discipline None after next->gateway_access_retained native stable before world next->
  gateway_native_frame native stable gateway_native_no_output world before after->
  gateway_container_counted native stable discipline container slots stream_block stream_offset initial readonly original size after next.
Proof.
  intros[[ACTIVE TAG_LOAD]SIZE_LOAD]SIDE RETAINED FRAME.
  pose proof ACTIVE as[CONTEXT[TAG[SIZE REST]]]. split.
  - split;[eapply gateway_value_active_effect;eassumption|].
    change(Mem.load Mint64 before(gateway_value_tag_slot slots)0=Some(Vlong(Int64.repr(gateway_container_code container))))in TAG_LOAD.
    change(Mem.load Mint64 after(gateway_value_tag_slot slots)0=Some(Vlong(Int64.repr(gateway_container_code container)))).
    eapply Mem.load_unchanged_on;[exact FRAME| |exact TAG_LOAD].
    intros position RANGE;split;[left;exact TAG|unfold gateway_native_no_output;tauto].
  - change(Mem.load Mint64 before(gateway_value_size_slot slots)0=Some(Vlong size))in SIZE_LOAD.
    change(Mem.load Mint64 after(gateway_value_size_slot slots)0=Some(Vlong size)).
    eapply Mem.load_unchanged_on;[exact FRAME| |exact SIZE_LOAD].
    intros position RANGE;split;[left;exact SIZE|unfold gateway_native_no_output;tauto].
Qed.

Theorem gateway_container_constructor_retains {World Event}(backend:gateway_backend World Event)
    python objects detached io stable thread_errno
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    container slots stream_block stream_offset initial readonly original size before world result after next value:
  gateway_container_counted(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)container slots stream_block stream_offset initial readonly original size before world->
  (forall candidate position,readonly candidate position->gateway_native_private(python world)candidate)->
  gateway_constructor_return(python world)(objects world)before result(python next)(objects next)after value->
  gateway_container_counted(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)container slots stream_block stream_offset initial readonly original size after next /\
  (forall candidate position,readonly candidate position->gateway_native_private(python next)candidate).
Proof.
  intros COUNTED READONLY RETURN.
  pose proof COUNTED as[[[[SIDE[STREAM[STABLE[INPUT PREVIOUS]]]]SLOTS]TAG]SIZE].
  set(native:=fun current candidate=>gateway_native_private(python current)candidate).
  assert(AFTER_SIDE:gateway_python_discipline python objects detached None after next).
  { split;[exact(gateway_constructor_valid _ _ _ _ _ _ _ _ RETURN)|].
    split;[exact(gateway_constructor_gil _ _ _ _ _ _ _ _ RETURN)|exact(gateway_constructor_clear _ _ _ _ _ _ _ _ RETURN)]. }
  pose proof(gateway_constructor_native_effect python objects before world result after next value RETURN)as[RETAINED FRAME].
  pose proof(gateway_container_counted_readonly_relabel native stable _ (fun current candidate _=>native current candidate)
    container slots stream_block stream_offset initial readonly original size before world COUNTED
    ltac:(intros;apply READONLY with(position:=position);assumption))as NATIVE_COUNTED.
  pose proof(gateway_container_counted_effect native(fun current candidate _=>native current candidate)_ container slots stream_block stream_offset
    initial readonly original size before world after next NATIVE_COUNTED AFTER_SIDE RETAINED FRAME)as AFTER_COUNTED.
  assert(NEXT_READONLY:forall candidate position,readonly candidate position->native next candidate).
  { intros candidate position READ;eapply gateway_constructor_native_retained;[exact RETURN| |apply READONLY with(position:=position);exact READ].
    exact(gateway_value_readonly_live _ _ _ _ _ INPUT candidate position READ). }
  split;[|exact NEXT_READONLY]. eapply gateway_container_counted_readonly_relabel;[exact AFTER_COUNTED|].
  intros candidate position READ;eapply gateway_thread_native_stable;[exact runtime|exact AFTER_SIDE|apply NEXT_READONLY with(position:=position);exact READ].
Qed.

Lemma gateway_container_counted_side {World}native stable discipline container slots stream_block stream_offset initial
    readonly original size memory world:
  @gateway_container_counted World native stable discipline container slots stream_block stream_offset initial readonly original size memory world->
  discipline None memory world.
Proof. intros[[[[SIDE REST]SLOTS]TAG]SIZE];exact SIDE. Qed.

Lemma gateway_container_counted_readonly_live {World}native stable discipline container slots stream_block stream_offset initial
    readonly original size memory world candidate position:
  @gateway_container_counted World native stable discipline container slots stream_block stream_offset initial readonly original size memory world->
  readonly candidate position->Mem.valid_block memory candidate.
Proof. intros[[[[SIDE[STREAM[STABLE[INPUT FRAME]]]]SLOTS]TAG]SIZE]READ;eapply gateway_value_readonly_live;eassumption. Qed.
