(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Individual descriptor calls retain the caller's other native
   roots. *)
From Stdlib Require Import List.
From compcert Require Import Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewaySpawnRuntime GatewaySpawnResources GatewayNativeRoots.

Section DescriptorRoots.
Context {World Event}(backend:gateway_backend World Event)io native stable base resources ipc
    (runtime:gateway_spawn_descriptor_runtime backend io native stable base resources ipc)
.
Variable held:list block.

Theorem gateway_descriptors_with_native_roots:
  gateway_spawn_descriptor_runtime backend io native stable
    (gateway_native_root_discipline native base held)resources ipc.
Proof.
  constructor.
  - intros before world after next[SIDE ROOTS]VALID INTERFERENCE.
    eapply gateway_spawn_ambient;[exact runtime|exact SIDE|exact VALID|exact INTERFERENCE].
  - intros before world object offset result after next observed[SIDE ROOTS]VALID PRIVATE POINTER OPERATION.
    destruct(gateway_socketpair_operation _ _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ SIDE VALID PRIVATE POINTER OPERATION)
      as(AFTER&STATE&ACCESS&PERMISSIONS&FRAME&EXCLUSIVE&IO&RESULT).
    split;[split;[exact AFTER|eapply gateway_native_roots_effect;eassumption]|].
    split;[exact STATE|]. split;[exact ACCESS|]. split;[exact PERMISSIONS|]. split;[exact FRAME|].
    split;[exact EXCLUSIVE|]. split;assumption.
  - intros before world source minimum entry result after next observed[SIDE ROOTS]VALID OWNED BOUND OPERATION.
    destruct(gateway_duplicate_operation _ _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ SIDE VALID OWNED BOUND OPERATION)
      as(AFTER&STATE&ACCESS&FRAME&EXCLUSIVE&IO&RESULT).
    split;[split;[exact AFTER|eapply gateway_native_roots_effect;eassumption]|].
    split;[exact STATE|]. split;[exact ACCESS|]. split;[exact FRAME|]. split;[exact EXCLUSIVE|]. split;assumption.
  - intros before world source entry result after next observed[SIDE ROOTS]VALID OWNED EXCLUSIVE OPERATION.
    destruct(gateway_get_flags_operation _ _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ SIDE VALID OWNED EXCLUSIVE OPERATION)
      as(AFTER&STATE&ACCESS&FRAME&REFERENCE&STATUS&KEPT&IO&RESULT).
    split;[split;[exact AFTER|eapply gateway_native_roots_effect;eassumption]|].
    split;[exact STATE|]. split;[exact ACCESS|]. split;[exact FRAME|]. split;[exact REFERENCE|].
    split;[exact STATUS|]. split;[exact KEPT|]. split;assumption.
  - intros before world source entry flags result after next observed[SIDE ROOTS]VALID OWNED EXCLUSIVE OPERATION.
    destruct(gateway_set_flags_operation _ _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ SIDE VALID OWNED EXCLUSIVE OPERATION)
      as(AFTER&STATE&ACCESS&FRAME&REFERENCE&STATUS&KEPT&IO&RESULT).
    split;[split;[exact AFTER|eapply gateway_native_roots_effect;eassumption]|].
    split;[exact STATE|]. split;[exact ACCESS|]. split;[exact FRAME|]. split;[exact REFERENCE|].
    split;[exact STATUS|]. split;[exact KEPT|]. split;assumption.
  - intros before world source entry result after next observed[SIDE ROOTS]VALID OWNED OPERATION.
    destruct(gateway_close_operation _ _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ SIDE VALID OWNED OPERATION)
      as(RESULT&AFTER&STATE&ACCESS&FRAME&REMOVED&REFERENCE&STATUS&KEPT&IO).
    split;[exact RESULT|]. split;[split;[exact AFTER|eapply gateway_native_roots_effect;eassumption]|].
    split;[exact STATE|]. split;[exact ACCESS|]. split;[exact FRAME|]. split;[exact REMOVED|].
    split;[exact REFERENCE|]. split;[exact STATUS|]. split;assumption.
Qed.
End DescriptorRoots.
