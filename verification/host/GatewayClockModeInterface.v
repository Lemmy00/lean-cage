(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: The reap clock keeps its actual released-thread mode. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Memdata Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayRuntimeABI GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.
Open Scope Z_scope.

(* This is one actual clock_gettime operation at the given mode. No source-helper,
   wall-clock progress, pending-exception or successful sample is assumed. *)
Definition gateway_clock_mode_operation {World Event}(backend:gateway_backend World Event)
    (io:Event->option gateway_native_io)(native_private:World->block->Prop)
    (stable_readonly:World->block->Z->Prop)(discipline:option val->mem->World->Prop)(mode:option val):Prop:=
forall before world object offset result after next observed,
    discipline mode before world -> native_private world object ->
    gateway_native_pointer before object offset 16 Writable ->
    gateway_runtime_operation backend gateway_clock_gettime_definition
      [Vint Int.one; Vptr object offset] before world result after next observed ->
    exists status,
      result = Vint status /\
      (status = Int.zero -> exists seconds nanoseconds,
        0 <= Int64.signed seconds /\ 0 <= Int64.signed nanoseconds < 1000000000 /\
        Mem.loadv Mint64 after (Vptr object offset) = Some (Vlong seconds) /\
        Mem.loadv Mint64 after (Vptr object (Ptrofs.add offset (Ptrofs.repr 8))) = Some (Vlong nanoseconds)) /\
      discipline mode after next /\
      gateway_access_retained native_private stable_readonly before world next /\
      gateway_native_permissions before after object offset 16 /\
      gateway_native_frame native_private stable_readonly (gateway_native_region object offset 16)
        world before after /\ io observed = None.

Lemma gateway_held_clock_mode_operation {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno:
  gateway_thread_runtime backend io native stable discipline thread_errno->
  gateway_clock_mode_operation backend io native stable discipline None.
Proof. intro thread;exact(gateway_clock_operation _ _ _ _ _ _ thread). Qed.
