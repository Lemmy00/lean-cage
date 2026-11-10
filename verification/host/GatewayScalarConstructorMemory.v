(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Constructors retain the current owned native scalar storage. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayObjectDiscipline GatewayValueEntry
  GatewayValueContext GatewayValueStack GatewayValueRegions GatewayScalarLength GatewayScalarContext GatewayScalarBuffer
  GatewayScalarPayloadMemory GatewayScalarTerminate GatewayScalarFrames GatewayNativeMemory GatewayHeapMemory GatewayStreamInterface
  GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_value_sized_readonly_relabel {World}native stable discipline replacement scalar slots stream_block stream_offset
    initial readonly original size memory world :
  @gateway_value_sized World native stable discipline scalar slots stream_block stream_offset initial readonly original size memory world ->
  (forall candidate position,readonly candidate position ->replacement world candidate position) ->
  gateway_value_sized native replacement discipline scalar slots stream_block stream_offset initial readonly original size memory world.
Proof.
  intros[[[[SIDE[STREAM[OLD_STABLE[INPUT FRAME]]]]SLOTS]TAG]SIZE]NEW_STABLE.
  split;[split;[split;[|exact SLOTS]|exact TAG]|exact SIZE].
  split;[exact SIDE|]. split;[exact STREAM|]. split;[exact NEW_STABLE|]. split;assumption.
Qed.

Theorem gateway_constructor_native_effect {World}(python:World->python_world)(objects:World->gateway_object_heap)
    before world result after next value :
  @gateway_constructor_return (python world)(objects world)before result(python next)(objects next)after value ->
  gateway_access_retained(fun current object=>gateway_native_private(python current)object)
    (fun current object _=>gateway_native_private(python current)object)before world next /\
  gateway_native_frame(fun current object=>gateway_native_private(python current)object)
    (fun current object _=>gateway_native_private(python current)object)gateway_native_no_output world before after.
Proof.
  intro RETURN;split.
  - split.
    + intros object LIVE PRIVATE;eapply gateway_constructor_native_retained;eassumption.
    + intros object position READ PRIVATE;eapply gateway_constructor_native_retained;
        [exact RETURN|eapply Mem.perm_valid_block;exact READ|exact PRIVATE].
  - eapply Mem.unchanged_on_implies;[exact(gateway_constructor_native _ _ _ _ _ _ _ _ RETURN)|].
    intros object position[[PRIVATE|PRIVATE]OUTPUT]LIVE;exact PRIVATE.
Qed.

Theorem gateway_scalar_constructor_retains {World Event}(backend:gateway_backend World Event)
    python objects detached io stable thread_errno
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    heap_allocation scalar slots stream_block stream_offset initial readonly original size object bytes before world result after next value :
  gateway_scalar_terminated_ready(fun current object=>gateway_native_private(python current)object)stable
    (gateway_python_discipline python objects detached)heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes before world ->
  (forall candidate position,readonly candidate position ->gateway_native_private(python world)candidate) ->
  gateway_constructor_return(python world)(objects world)before result(python next)(objects next)after value ->
  gateway_scalar_terminated_ready(fun current object=>gateway_native_private(python current)object)stable
    (gateway_python_discipline python objects detached)heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes after next /\
  (forall candidate position,readonly candidate position ->gateway_native_private(python next)candidate).
Proof.
  intros[[[SIZED[HEAP SEPARATE]][COUNT PAYLOAD]]TERMINATED]READONLY RETURN.
  pose proof SIZED as[[[[INITIAL_SIDE[INITIAL_STREAM[INITIAL_STABLE[INITIAL_INPUT INITIAL_FRAME]]]]INITIAL_SLOTS]INITIAL_TAG]INITIAL_SIZE].
  let native:=constr:(fun current object=>gateway_native_private(python current)object)in
    set(NATIVE:=native).
  assert(AFTER_SIDE:gateway_python_discipline python objects detached None after next).
  { split;[exact(gateway_constructor_valid _ _ _ _ _ _ _ _ RETURN)|].
    split;[exact(gateway_constructor_gil _ _ _ _ _ _ _ _ RETURN)|exact(gateway_constructor_clear _ _ _ _ _ _ _ _ RETURN)]. }
  pose proof(gateway_constructor_native_effect python objects before world result after next value RETURN)as[RETAINED FRAME].
  pose proof(gateway_value_sized_readonly_relabel NATIVE stable _ (fun current object _=>NATIVE current object)
    scalar slots stream_block stream_offset initial readonly original size before world SIZED ltac:(intros;apply READONLY with(position:=position);assumption))
    as NATIVE_SIZED.
  pose proof(gateway_value_sized_effect NATIVE(fun current object _=>NATIVE current object)_ scalar slots stream_block stream_offset
    initial readonly original size before world after next NATIVE_SIZED AFTER_SIDE RETAINED FRAME)as AFTER_SIZED.
  assert(NEXT_READONLY:forall candidate position,readonly candidate position ->NATIVE next candidate).
  { intros candidate position READ;eapply gateway_constructor_native_retained;[exact RETURN| |apply READONLY with(position:=position);exact READ].
    exact(gateway_value_readonly_live _ _ _ _ _ INITIAL_INPUT candidate position READ). }
  assert(FINAL_SIZED:gateway_value_sized NATIVE stable(gateway_python_discipline python objects detached)scalar slots stream_block
    stream_offset initial readonly original size after next).
  { eapply gateway_value_sized_readonly_relabel;[exact AFTER_SIZED|].
    intros candidate position READ;eapply gateway_thread_native_stable;[exact runtime|exact AFTER_SIDE|apply NEXT_READONLY with(position:=position);exact READ]. }
  destruct HEAP as[OLD_SIDE[PRIVATE[ORIGIN BLOCK]]].
  assert(HEAP_FRAME:Mem.unchanged_on(gateway_heap_region object(Int64.unsigned size+1))before after).
  { eapply Mem.unchanged_on_implies;[exact(gateway_constructor_native _ _ _ _ _ _ _ _ RETURN)|].
    intros candidate position[SAME RANGE]LIVE;subst candidate;exact PRIVATE. }
  assert(OBJECT_LIVE:Mem.valid_block before object).
  { destruct BLOCK as[BOUND[HEADER OWNED]];eapply Mem.perm_valid_block;apply(OWNED(-8));lia. }
  split;[|exact NEXT_READONLY]. split.
  - split.
    + split;[exact FINAL_SIZED|]. split;[|exact SEPARATE]. split;[exact AFTER_SIDE|].
      split;[eapply gateway_constructor_native_retained;eassumption|]. split;[exact ORIGIN|].
      eapply gateway_heap_block_frame;eassumption.
    + split;[exact COUNT|]. eapply Mem.loadbytes_unchanged_on;[exact HEAP_FRAME| |exact PAYLOAD].
      intros position RANGE;split;[reflexivity|lia].
  - eapply Mem.loadbytes_unchanged_on;[exact HEAP_FRAME| |exact TERMINATED].
    intros position RANGE;split;[reflexivity|lia].
Qed.
