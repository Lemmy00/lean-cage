(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Each actual builtin container mutation retains the same live
   private stream, count/tag cells and readonly inputs. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayObjectDiscipline
  GatewayContainerMemory GatewayContainerLength GatewayContainerGuards GatewayValueEntry GatewayValueStack
  GatewayStreamInterface GatewayThreadRuntime GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_container_native_effect {World}(python:World->python_world)(objects:World->gateway_object_heap)
    before world container after next value :
  @gateway_container_return (python world)(objects world)before container(python next)(objects next)after value ->
  gateway_access_retained(fun current object=>gateway_native_private(python current)object)
    (fun current object _=>gateway_native_private(python current)object)before world next /\
  gateway_native_frame(fun current object=>gateway_native_private(python current)object)
    (fun current object _=>gateway_native_private(python current)object)gateway_native_no_output world before after.
Proof.
  intro RETURN;split.
  - split.
    + intros object LIVE PRIVATE;eapply gateway_container_native_retained;eassumption.
    + intros object position READ PRIVATE;eapply gateway_container_native_retained;
        [exact RETURN|eapply Mem.perm_valid_block;exact READ|exact PRIVATE].
  - eapply Mem.unchanged_on_implies;[exact(gateway_container_native _ _ _ _ _ _ _ _ RETURN)|].
    intros object position[[PRIVATE|PRIVATE]OUTPUT]LIVE;exact PRIVATE.
Qed.

Theorem gateway_container_mutation_retains {World Event}(backend:gateway_backend World Event)
    python objects detached io stable thread_errno
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    container slots stream_block stream_offset initial readonly original size before world parent after next value:
  gateway_container_counted(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)container slots stream_block stream_offset initial readonly original size before world->
  (forall candidate position,readonly candidate position->gateway_native_private(python world)candidate)->
  gateway_container_return(python world)(objects world)before parent(python next)(objects next)after value->
  gateway_container_counted(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)container slots stream_block stream_offset initial readonly original size after next /\
  (forall candidate position,readonly candidate position->gateway_native_private(python next)candidate).
Proof.
  intros COUNTED READONLY RETURN.
  pose proof COUNTED as[[[[SIDE[STREAM[STABLE[INPUT PREVIOUS]]]]SLOTS]TAG]SIZE].
  set(native:=fun current candidate=>gateway_native_private(python current)candidate).
  assert(AFTER_SIDE:gateway_python_discipline python objects detached None after next)
    by(exact(gateway_container_ready _ _ _ _ _ _ _ _ RETURN)).
  pose proof(gateway_container_native_effect python objects before world parent after next value RETURN)as[RETAINED FRAME].
  pose proof(gateway_container_counted_readonly_relabel native stable _ (fun current candidate _=>native current candidate)
    container slots stream_block stream_offset initial readonly original size before world COUNTED
    ltac:(intros;apply READONLY with(position:=position);assumption))as NATIVE_COUNTED.
  pose proof(gateway_container_counted_effect native(fun current candidate _=>native current candidate)_ container slots stream_block stream_offset
    initial readonly original size before world after next NATIVE_COUNTED AFTER_SIDE RETAINED FRAME)as AFTER_COUNTED.
  assert(NEXT_READONLY:forall candidate position,readonly candidate position->native next candidate).
  { intros candidate position READ;eapply gateway_container_native_retained;[exact RETURN| |apply READONLY with(position:=position);exact READ].
    exact(gateway_value_readonly_live _ _ _ _ _ INPUT candidate position READ). }
  split;[|exact NEXT_READONLY]. eapply gateway_container_counted_readonly_relabel;[exact AFTER_COUNTED|].
  intros candidate position READ;eapply gateway_thread_native_stable;[exact runtime|exact AFTER_SIDE|apply NEXT_READONLY with(position:=position);exact READ].
Qed.
