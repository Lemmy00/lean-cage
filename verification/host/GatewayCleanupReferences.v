(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Individual cleanup syscalls retain the invocation's
   source-owned reference projection beside their actual native C output spans. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayRuntimeABI GatewayThreadRuntime GatewayStreamInterface
  GatewaySpawnABI GatewayExchangeABI GatewayReapABI GatewayReapRuntime GatewayClockModeInterface GatewayPython GatewayObjects
  GatewayReferences GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads GatewayThreadInvariant.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Section CleanupReferences.
Context {World Event}(backend:gateway_backend World Event)
  (native:World->block->Prop)(stable:World->block->Z->Prop)(base:option val->mem->World->Prop)
  (python:World->python_world)(objects:World->gateway_object_heap).

(* These are exact primitive calls, not a helper transcript or a claim that a
   group number still names the old child. Writable outputs are native-private. *)
Inductive gateway_cleanup_graph_operation:option val->mem->World->mem->World->Prop:=
| gateway_cleanup_graph_close:forall before world descriptor result after next observed,
    base None before world->base None after next->
    gateway_spawn_operation backend gateway_close_api[Vint descriptor]before world result after next observed->
    gateway_cleanup_graph_operation None before world after next
| gateway_cleanup_graph_signal:forall mode before world group result after next observed,
    base mode before world->base mode after next->Int.signed group<0->
    gateway_runtime_operation backend gateway_kill_definition[Vint group;Vint(Int.repr 9)]before world result after next observed->
    gateway_cleanup_graph_operation mode before world after next
| gateway_cleanup_graph_wait:forall mode before world child options object offset result after next observed,
    base mode before world->base mode after next->0<Int.signed child->(options=Int.zero\/options=Int.one)->
    native world object->gateway_native_pointer before object offset 4 Writable->
    gateway_runtime_operation backend gateway_waitpid_definition[Vint child;Vptr object offset;Vint options]
      before world result after next observed->gateway_cleanup_graph_operation mode before world after next
| gateway_cleanup_graph_pause:forall mode before world object offset result after next observed,
    base mode before world->base mode after next->native world object->gateway_native_pointer before object offset 16 Readable->
    gateway_runtime_operation backend gateway_nanosleep_definition[Vptr object offset;Vnullptr]before world result after next observed->
    gateway_cleanup_graph_operation mode before world after next
| gateway_cleanup_graph_clock:forall mode before world object offset result after next observed,
    base mode before world->base mode after next->native world object->gateway_native_pointer before object offset 16 Writable->
    gateway_runtime_operation backend gateway_clock_gettime_definition[Vint Int.one;Vptr object offset]
      before world result after next observed->gateway_cleanup_graph_operation mode before world after next.

Record gateway_cleanup_reference_runtime:Prop:={
  gateway_cleanup_reference_effect:forall mode before world after next,
    gateway_cleanup_graph_operation mode before world after next->gateway_reference_thread_effect python objects world next
}.

Definition gateway_cleanup_scope(decimal_float:list Z->Floats.float->Prop)ledger held mode memory world:Prop:=
  base mode memory world /\gateway_reference_scope python objects decimal_float ledger held world.

Theorem gateway_reap_with_reference_scope io observation thread_errno decimal_float ledger held
    (runtime:gateway_reap_runtime backend io observation native stable base thread_errno)
    (contract:gateway_cleanup_reference_runtime):
  gateway_reap_runtime backend io observation native stable(gateway_cleanup_scope decimal_float ledger held)thread_errno.
Proof.
  constructor.
  - intros mode before world group result after next observed[SIDE SCOPE]NEGATIVE API.
    destruct(gateway_reap_kill_operation _ _ _ _ _ _ _ runtime mode before world group result after next observed SIDE NEGATIVE API)
      as(status&RESULT&STATUS&OBSERVATION&AFTER&ACCESS&FRAME&IO).
    exists status;split;[exact RESULT|]. split;[exact STATUS|]. split;[exact OBSERVATION|].
    split;[|split;[exact ACCESS|split;assumption]]. split;[exact AFTER|].
    eapply gateway_reference_scope_thread_effect;[exact SCOPE|].
    eapply gateway_cleanup_reference_effect;[exact contract|]. eapply gateway_cleanup_graph_signal;eassumption.
  - intros mode before world child options object offset result after next observed[SIDE SCOPE]CHILD OPTIONS NATIVE POINTER API.
    destruct(gateway_reap_wait_operation _ _ _ _ _ _ _ runtime mode before world child options object offset result after next observed
      SIDE CHILD OPTIONS NATIVE POINTER API)
      as(status&word&RESULT&CHOICE&LOADED&OTHER&OBSERVATION&AFTER&ACCESS&PERMISSIONS&FRAME&IO).
    exists status,word;split;[exact RESULT|]. split;[exact CHOICE|]. split;[exact LOADED|]. split;[exact OTHER|].
    split;[exact OBSERVATION|]. split;[|split;[exact ACCESS|split;[exact PERMISSIONS|split;assumption]]].
    split;[exact AFTER|]. eapply gateway_reference_scope_thread_effect;[exact SCOPE|].
    eapply gateway_cleanup_reference_effect;[exact contract|]. eapply gateway_cleanup_graph_wait;eassumption.
  - intros mode before world object offset result after next observed[SIDE SCOPE]NATIVE POINTER API.
    destruct(gateway_reap_pause_operation _ _ _ _ _ _ _ runtime mode before world object offset result after next observed SIDE NATIVE POINTER API)
      as(status&RESULT&STATUS&OBSERVATION&AFTER&ACCESS&FRAME&IO).
    exists status;split;[exact RESULT|]. split;[exact STATUS|]. split;[exact OBSERVATION|].
    split;[|split;[exact ACCESS|split;assumption]]. split;[exact AFTER|].
    eapply gateway_reference_scope_thread_effect;[exact SCOPE|].
    eapply gateway_cleanup_reference_effect;[exact contract|]. eapply gateway_cleanup_graph_pause;eassumption.
Qed.

Theorem gateway_clock_with_reference_scope io decimal_float ledger held mode
    (runtime:gateway_clock_mode_operation backend io native stable base mode)
    (contract:gateway_cleanup_reference_runtime):
  gateway_clock_mode_operation backend io native stable(gateway_cleanup_scope decimal_float ledger held)mode.
Proof.
  intros before world object offset result after next observed[SIDE SCOPE]NATIVE POINTER API.
  destruct(runtime before world object offset result after next observed SIDE NATIVE POINTER API)
    as(status&RESULT&TIME&AFTER&ACCESS&PERMISSIONS&FRAME&IO).
  exists status;split;[exact RESULT|]. split;[exact TIME|].
  split;[|split;[exact ACCESS|split;[exact PERMISSIONS|split;assumption]]]. split;[exact AFTER|].
  eapply gateway_reference_scope_thread_effect;[exact SCOPE|].
  eapply gateway_cleanup_reference_effect;[exact contract|]. eapply gateway_cleanup_graph_clock;eassumption.
Qed.
End CleanupReferences.
