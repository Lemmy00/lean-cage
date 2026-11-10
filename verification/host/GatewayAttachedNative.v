(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Attached source memory operations need no SDK callback-frame premise. *)
From compcert Require Import Integers AST Values Memory.
From HostGateway Require Import GatewayMachine GatewayThreadRuntime GatewayErrorRuntime.

Record gateway_attached_native_runtime {World Event} (backend : gateway_backend World Event)
    (native : World -> block -> Prop) (stable : World -> block -> BinNums.Z -> Prop)
    (attached : mem -> World -> Prop) : Prop := {
  gateway_attached_native_ambient : forall before world after next,
    attached before world -> gateway_interference backend before world after next ->
    attached after next /\ gateway_access_retained native stable before world next /\
    gateway_native_frame native stable gateway_native_no_output world before after;
  gateway_attached_native_allocate : forall before world after object low high,
    attached before world -> Mem.alloc before low high = (after, object) -> attached after world;
  gateway_attached_native_store : forall before world after object offset chunk value,
    attached before world -> native world object -> Mem.store chunk before object offset value = Some after ->
    attached after world;
  gateway_attached_native_free : forall before world after object low high,
    attached before world -> native world object -> Mem.free before object low high = Some after -> attached after world
}.

Theorem gateway_error_attached_native {World Event} (backend : gateway_backend World Event)
    io native stable normal attached exception pending errno_cell :
  gateway_error_runtime backend io native stable normal attached exception pending errno_cell ->
  gateway_attached_native_runtime backend native stable attached.
Proof.
  intro RUNTIME; constructor.
  - exact (gateway_error_ambient _ _ _ _ _ _ _ _ _ RUNTIME).
  - exact (gateway_error_native_alloc _ _ _ _ _ _ _ _ _ RUNTIME).
  - exact (gateway_error_native_store _ _ _ _ _ _ _ _ _ RUNTIME).
  - exact (gateway_error_native_free _ _ _ _ _ _ _ _ _ RUNTIME).
Qed.
