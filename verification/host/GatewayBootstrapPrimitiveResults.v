(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Real libc results expose their precise write regions to source consumers. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayBootstrapABI
  GatewayBootstrapRuntime GatewayThreadRuntime GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_bootstrap_actual_length_post {World Event} (backend : gateway_backend World Event)
    io native stable discipline module_filename canonicalizes
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes)
    ge pointer bytes maximum continuation before world returned after next observed :
  discipline None before world -> gateway_error_cstring before pointer bytes ->
  gateway_bootstrap_protected native stable before world pointer (bytes ++ [Byte.zero]) ->
  0 <= maximum <= Int64.max_unsigned ->
  gateway_step backend ge
    (gateway_live (Callstate (gateway_bootstrap_signature gateway_bounded_length_api)
      [pointer; Vlong (Int64.repr maximum)] continuation before) world)
    (gateway_primitive observed) (gateway_live (Returnstate returned continuation after) next) ->
  gateway_bootstrap_post io native stable discipline gateway_native_no_output before world after next observed /\
    returned = Vlong (Int64.repr (Z.min maximum (Z.of_nat (length bytes)))).
Proof.
  intros SIDE STRING PROTECTED BOUND STEP.
  eapply gateway_bounded_length_operation;
    [exact runtime |exact SIDE |exact STRING |exact PROTECTED |exact BOUND |].
  inversion STEP; subst; cbn [gateway_bootstrap_operation gateway_bootstrap_signature gateway_runtime_operation]; eassumption.
Qed.

Theorem gateway_bootstrap_actual_realpath_post {World Event} (backend : gateway_backend World Event)
    io native stable discipline module_filename canonicalizes
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes)
    ge pointer original destination continuation before world returned after next observed :
  discipline None before world -> gateway_error_cstring before pointer original ->
  gateway_bootstrap_protected native stable before world pointer (original ++ [Byte.zero]) ->
  native world destination -> gateway_native_pointer before destination Ptrofs.zero 4096 Writable ->
  gateway_bootstrap_separate_source pointer destination ->
  gateway_step backend ge
    (gateway_live (Callstate (gateway_bootstrap_signature gateway_canonical_path_api)
      [pointer; Vptr destination Ptrofs.zero] continuation before) world)
    (gateway_primitive observed) (gateway_live (Returnstate returned continuation after) next) ->
  gateway_bootstrap_post io native stable discipline (gateway_native_region destination Ptrofs.zero 4096)
    before world after next observed /\ gateway_native_permissions before after destination Ptrofs.zero 4096 /\
  (returned = Vnullptr \/ exists canonical,
    returned = Vptr destination Ptrofs.zero /\ Z.of_nat (length canonical) <= 4095 /\
    gateway_error_cstring after returned canonical /\ canonicalizes world next original canonical).
Proof.
  intros SIDE STRING PROTECTED PRIVATE POINTER SEPARATE STEP.
  eapply gateway_canonical_path_operation;
    [exact runtime |exact SIDE |exact STRING |exact PROTECTED |exact PRIVATE |exact POINTER |exact SEPARATE |].
  inversion STEP; subst; cbn [gateway_bootstrap_operation gateway_bootstrap_signature gateway_runtime_operation]; eassumption.
Qed.
