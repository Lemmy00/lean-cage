(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Actual callback stack allocation retains existing native flag cells. *)
From Stdlib Require Import List.
From compcert Require Import Integers AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayInitializationCells GatewayInitializationRegions GatewayInitializationFailure GatewayThreadRuntime GatewayErrorRuntime GatewayAttachedNative.
Import ListNotations.

Theorem gateway_initialization_cells_allocate {World} native symbols active complete before (world : World) after object low high :
  gateway_initialization_cells native symbols active complete before world ->
  Mem.alloc before low high = (after, object) ->
  gateway_initialization_cells native symbols active complete after world.
Proof.
  intros CELLS ALLOCATED.
  eapply gateway_initialization_cells_quiet with (stable := fun _ _ _ => False); [exact CELLS | |].
  - split; intros; assumption.
  - unfold gateway_native_frame; eapply Mem.alloc_unchanged_on; exact ALLOCATED.
Qed.

Section Allocations.
Context {World Event} (backend : gateway_backend World Event) native stable rooted
  (runtime : gateway_attached_native_runtime backend native stable rooted)
  (symbols : gateway_initialization_symbols) (active complete : int).
Let property := gateway_initialization_failure_context rooted native symbols active complete.

Theorem gateway_initialization_rooted_allocate before world after object low high :
  property before world -> Mem.alloc before low high = (after, object) -> property after world.
Proof.
  intros [ROOTED CELLS] ALLOCATED; split.
  - eapply gateway_attached_native_allocate; [exact runtime |exact ROOTED |exact ALLOCATED].
  - eapply gateway_initialization_cells_allocate; eassumption.
Qed.

Theorem gateway_initialization_rooted_allocations ge environment before variables after_environment after world :
  alloc_variables ge environment before variables after_environment after -> property before world -> property after world.
Proof.
  intro ALLOCATED; induction ALLOCATED; intros INPUT; [exact INPUT |].
  apply IHALLOCATED; eapply gateway_initialization_rooted_allocate; eassumption.
Qed.

Theorem gateway_initialization_rooted_entry ge function arguments before environment parameters allocated world :
  function_entry2 ge function arguments before environment parameters allocated ->
  property before world -> property allocated world.
Proof.
  intros ENTRY INPUT; inversion ENTRY; subst.
  eapply gateway_initialization_rooted_allocations; eassumption.
Qed.
End Allocations.
