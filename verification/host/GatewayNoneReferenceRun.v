(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual singleton API run retains its new owned reference and native caller cells. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayRootLeases
  GatewayObjectConstants GatewayObjectDiscipline GatewayObjectThreads GatewayReturnRuntime GatewayLocalRuntime
  GatewayOperations GatewayReadonly GatewayThreadRuntime GatewayStreamInterface GatewayRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Section NoneReferenceRun.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (python:World->python_world)(objects:World->gateway_object_heap)
  (detached:Values.val->mem->World->Prop)(io:Event->option gateway_native_io)
  (stable:World->block->Z->Prop)(thread_errno:World->int)(heap_allocation:block->BinNums.Z->Prop)
  (decimal_float:list BinNums.Z->Floats.float->Prop)(leases:World->nat->Values.val->Prop).
Let native:=fun world object=>gateway_native_private(python world)object.
Let base:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno)
  (references:gateway_reference_runtime backend python objects)
  (roots:gateway_root_lease_runtime backend python objects decimal_float leases)
  (object_threads:gateway_object_thread_contract backend native stable base heap_allocation
    python objects leases).

Lemma gateway_reference_native_environment before world object after next environment :
  gateway_native_environment native world before environment ->
  python_incref_return(python world)object before(python next)after ->
  gateway_native_environment native next after environment.
Proof.
  intros OWNED RETURN identifier candidate ty LOOK.
  destruct(OWNED identifier candidate ty LOOK)as[LIVE PRIVATE].
  destruct(python_incref_object _ _ _ _ _ RETURN)as[object_block[offset[OBJECT FRAME]]].
  split;[eapply Mem.valid_block_unchanged_on;[exact FRAME|exact LIVE]|].
  unfold native,gateway_native_private in *;rewrite(python_incref_heap _ _ _ _ _ RETURN);exact PRIVATE.
Qed.

Theorem gateway_actual_none_api_run none environment before world events returned after next :
  gateway_none_runtime python objects none ->
  gateway_return_environment native base None environment before world ->
  gateway_steps backend ge
    (gateway_live(Callstate python_incref_definition[none]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  exists ticket,gateway_held_values python objects decimal_float leases
      [{|gateway_held_ticket:=ticket;gateway_held_object:=none;
        gateway_held_view:=gateway_held_scalar_value gateway_none_object|}]next /\
    gateway_return_environment native base None environment after next.
Proof.
  intros CONSTANTS INITIAL RUN.
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ _ _ _ _ _ _ RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &PENDING &PREFIX &OPERATION &SUFFIX).
  assert(CALLED:gateway_return_environment native base None environment called called_world).
  { eapply(gateway_pending_run_ready backend ge _
      (gateway_return_environment_ambient backend io native stable base thread_errno runtime None environment)
      (Callstate python_incref_definition[none]Kstop before)before world prefix called called_world INITIAL PENDING).
    exact PREFIX. }
  destruct CALLED as[READY NATIVE_ENV].
  assert(API:gateway_object_operation backend gateway_api_incref[none]called called_world returned changed changed_world observed).
  { exists python_incref_definition;split;[reflexivity|exact OPERATION]. }
  destruct(gateway_actual_none_reference_held backend python objects decimal_float leases none references roots CONSTANTS
    called called_world returned changed changed_world observed READY API)
    as(ticket &CREATED &AFTER_READY &HELD &RETURN).
  set(captured:={|gateway_held_ticket:=ticket;gateway_held_object:=none;
    gateway_held_view:=gateway_held_scalar_value gateway_none_object|}).
  set(ready:=fun memory current=>gateway_return_environment native base None environment memory current /\
    gateway_held_values python objects decimal_float leases[captured]current).
  assert(CLOSED:gateway_runtime_discipline backend ready).
  { intros first current last following[[SIDE ENV]HOLD]INTERFERENCE;split.
    - eapply gateway_return_environment_ambient;[exact runtime|split;[exact SIDE|exact ENV]|exact INTERFERENCE].
    - eapply gateway_held_values_effect;[exact roots|exact HOLD|].
      eapply gateway_object_thread_ambient;[exact object_threads|exact SIDE|exact INTERFERENCE]. }
  assert(AFTER:ready changed changed_world).
  { split;[split;[exact AFTER_READY|eapply gateway_reference_native_environment;eassumption]|exact HELD]. }
  assert(FINAL:ready after next).
  { eapply(gateway_readonly_run_side backend ge ready CLOSED(Returnstate returned Kstop changed)changed_world
      suffix returned after next);[exact I|exact AFTER|exact SUFFIX]. }
  exists ticket;split;[exact(proj2 FINAL)|exact(proj1 FINAL)].
Qed.

End NoneReferenceRun.
