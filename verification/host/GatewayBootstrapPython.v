(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Individual loader/string APIs do not execute Python callbacks. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayBootstrapABI GatewayBootstrapRuntime
  GatewayPython GatewayObjects GatewayRootLeases.
From HostGateway Require Import GatewayThreadRuntime GatewayErrorRuntime.
Import ListNotations.

Definition gateway_bootstrap_python_outputs python api arguments : Prop :=
  match api, arguments with
  | gateway_loader_address_api, [_; Vptr object _]
  | gateway_canonical_path_api, [_; Vptr object _]
  | gateway_memory_copy_api, [Vptr object _; _; _] => ~ python_runtime_owned python object
  | gateway_bounded_length_api, [_; _]
  | gateway_memory_compare_api, [_; _; _] => True
  | _, _ => False
  end.

Definition gateway_bootstrap_arguments_valid memory api arguments : Prop :=
  match api, arguments with
  | gateway_loader_address_api, [_; Vptr object offset] =>
      gateway_native_pointer memory object offset 32 Writable /\
      Mem.valid_access memory Mptr object (Ptrofs.unsigned offset) Writable
  | gateway_canonical_path_api, [filename; Vptr object offset] =>
      (exists bytes, gateway_error_cstring memory filename bytes) /\
      gateway_native_pointer memory object offset 4096 Writable /\
      gateway_bootstrap_separate_source filename object
  | gateway_bounded_length_api, [filename; Vlong _] =>
      exists bytes, gateway_error_cstring memory filename bytes
  | gateway_memory_compare_api, [first; second; Vlong count] =>
      exists left right, Z.of_nat (length left) = Int64.unsigned count /\ length left = length right /\
        gateway_bootstrap_bytes memory first left /\ gateway_bootstrap_bytes memory second right
  | gateway_memory_copy_api, [Vptr destination destination_offset; Vptr source source_offset; Vlong count] =>
      exists bytes, Z.of_nat (length bytes) = Int64.unsigned count /\
        gateway_native_pointer memory destination destination_offset (Int64.unsigned count) Writable /\
        gateway_bootstrap_bytes memory (Vptr source source_offset) bytes /\
        gateway_bootstrap_disjoint destination destination_offset (Int64.unsigned count) source source_offset
  | _, _ => False
  end.

(* This is an individual libc/loader footprint, not an initialization contract.
   The source supplies the actual destination and proves its heap separation.
   Invalid arguments remain broad in GatewayMachine and satisfy no such law. *)
Record gateway_bootstrap_python_runtime {World Event} (backend : gateway_backend World Event)
    (python : World -> python_world) (objects : World -> gateway_object_heap)
    (leases : World -> nat -> Values.val -> Prop) : Prop := {
  gateway_bootstrap_python_operation : forall api arguments before world result after next observed,
    gateway_objects_ready (python world) (objects world) before ->
    gateway_bootstrap_python_outputs (python world) api arguments ->
    gateway_bootstrap_arguments_valid before api arguments ->
    gateway_bootstrap_operation backend api arguments before world result after next observed ->
    python next = python world /\ objects next = objects world /\
    gateway_leases_retained leases world next /\
    Mem.unchanged_on (fun object _ => python_runtime_owned (python world) object) before after
}.

Theorem gateway_bootstrap_python_ready {World Event} (backend : gateway_backend World Event)
    python objects leases (runtime : gateway_bootstrap_python_runtime backend python objects leases)
    api arguments before world result after next observed :
  gateway_objects_ready (python world) (objects world) before ->
  gateway_bootstrap_python_outputs (python world) api arguments ->
  gateway_bootstrap_arguments_valid before api arguments ->
  gateway_bootstrap_operation backend api arguments before world result after next observed ->
  gateway_objects_ready (python next) (objects next) after /\ gateway_leases_retained leases world next.
Proof.
  intros READY OUTPUTS VALID OPERATION.
  destruct (gateway_bootstrap_python_operation _ _ _ _ runtime _ _ _ _ _ _ _ _ READY OUTPUTS VALID OPERATION)
    as [PYTHON [OBJECTS [LEASES FRAME]]].
  rewrite PYTHON, OBJECTS; split; [|exact LEASES].
  eapply gateway_objects_ready_native_frame; eassumption.
Qed.
