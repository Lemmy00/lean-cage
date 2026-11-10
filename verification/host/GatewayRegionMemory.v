(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Individual allocation operations retain current caller capabilities. *)
From Stdlib Require Import ZArith.
From compcert Require Import Values Memory.
From HostGateway Require Import GatewayMachine GatewayNativeMemory GatewayNativeRegions GatewayRegionThreads
  GatewayThreadRuntime GatewayStreamInterface.

Theorem gateway_memory_with_native_region {World Event}(backend:gateway_backend World Event)
    io native stable base heap_allocation
    (runtime:gateway_native_memory_runtime backend io native stable base heap_allocation)protected :
  gateway_native_memory_runtime backend io native stable(gateway_native_region_discipline native base protected)heap_allocation.
Proof.
  constructor.
  - intros mode before world amount result after next observed[SIDE HELD]AMOUNT OPERATION.
    destruct(gateway_malloc_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ SIDE AMOUNT OPERATION)
      as[NEXT[RETAINED[FRAME[EVENT RESULT]]]].
    split;[|split;[exact RETAINED|split;[exact FRAME|split;assumption]]].
    split;[exact NEXT|];eapply gateway_native_region_effect;eassumption.
  - intros mode before world object amount result after next observed[SIDE HELD]NATIVE AUTHORITY BLOCK OPERATION.
    destruct(gateway_free_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ SIDE NATIVE AUTHORITY BLOCK OPERATION)
      as[RESULT[NEXT[RETAINED[FRAME[FREE[PERMISSIONS EVENT]]]]]].
    split;[exact RESULT|]. split;[|split;[exact RETAINED|split;[exact FRAME|split;[exact FREE|split;assumption]]]].
    split;[exact NEXT|];eapply gateway_native_region_effect;eassumption.
  - intros mode before world object offset amount bytes result after next observed[SIDE HELD]READABLE POINTER LOAD OPERATION.
    destruct(gateway_memchr_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ _ _
      SIDE READABLE POINTER LOAD OPERATION)as[RESULT[NEXT[RETAINED[FRAME EVENT]]]].
    split;[exact RESULT|]. split;[|split;[exact RETAINED|split;assumption]].
    split;[exact NEXT|];eapply gateway_native_region_effect;eassumption.
Qed.
