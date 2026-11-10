(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The singleton reference operation retains actual native caller regions. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences
  GatewayObjectConstants GatewayObjectDiscipline GatewayNoneReferenceRun GatewayReturnRuntime GatewayReturnMemory GatewayNativeRegions
  GatewayOperations GatewayReadonly GatewayThreadRuntime GatewayStreamInterface GatewayRuntime GatewayLocalRuntime.
Import ListNotations.

Theorem gateway_actual_none_api_memory {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects detached io stable thread_errno
    (runtime:gateway_thread_runtime backend io(fun world object=>gateway_native_private(python world)object)
      stable(gateway_python_discipline python objects detached)thread_errno)
    (references:gateway_reference_runtime backend python objects)
    none environment protected original before world events returned after next :
  gateway_none_runtime python objects none ->
  gateway_return_region_context(fun world object=>gateway_native_private(python world)object)
    (gateway_python_discipline python objects detached)None environment protected original before world ->
  gateway_steps backend ge(gateway_live(Callstate python_incref_definition[none]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  gateway_return_region_context(fun world object=>gateway_native_private(python world)object)
    (gateway_python_discipline python objects detached)None environment protected original after next.
Proof.
  intros CONSTANTS INITIAL RUN.
  set(native:=fun world object=>gateway_native_private(python world)object).
  set(base:=gateway_python_discipline python objects detached).
  set(ready:=gateway_return_region_context native base None environment protected original).
  pose proof(gateway_return_region_ambient backend io native stable base thread_errno runtime
    None environment protected original)as CLOSED.
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ _ _ _ _ _ _ RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &PENDING &PREFIX &OPERATION &SUFFIX).
  destruct(gateway_pending_run_ready backend ge ready CLOSED(Callstate python_incref_definition[none]Kstop before)
    before world prefix called called_world INITIAL PENDING PREFIX)as[[SIDE OWNED][REGION FRAME]].
  destruct(gateway_none_identity _ _ _ CONSTANTS _ _ SIDE)as[LIVE[VALUE PRIVATE]].
  assert(API:gateway_object_operation backend gateway_api_incref[none]called called_world returned changed changed_world observed).
  { exists python_incref_definition;split;[reflexivity|exact OPERATION]. }
  destruct(gateway_runtime_incref_objects _ _ _ references _ _ _ _ _ _ _ SIDE LIVE API)
    as[RETURN[AFTER_READY REST]].
  assert(STEP_FRAME:Mem.unchanged_on protected called changed).
  { eapply Mem.unchanged_on_implies;[exact(gateway_incref_native_frame _ _ _ _ _ _ SIDE RETURN)|].
    intros object position MEMBER BLOCK;exact(proj2(REGION object position MEMBER)). }
  assert(AFTER:ready changed changed_world).
  { split.
    - split;[exact AFTER_READY|eapply gateway_reference_native_environment;[exact OWNED|exact RETURN]].
    - split;[|eapply Mem.unchanged_on_trans;[exact FRAME|exact STEP_FRAME]].
      intros object position MEMBER;destruct(REGION object position MEMBER)as[BLOCK NATIVE];split.
      + eapply Mem.valid_block_unchanged_on;[exact STEP_FRAME|exact BLOCK].
      + unfold native,gateway_native_private in *;rewrite(python_incref_heap _ _ _ _ _ RETURN);exact NATIVE. }
  eapply(gateway_readonly_run_side backend ge ready CLOSED(Returnstate returned Kstop changed)changed_world
    suffix returned after next);[exact I|exact AFTER|exact SUFFIX].
Qed.
