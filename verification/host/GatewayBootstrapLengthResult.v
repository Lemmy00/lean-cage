(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual length result and retained filename share one operation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Events Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayBootstrapABI GatewayBootstrapRuntime
  GatewayBootstrapInformation GatewayBootstrapLengthSource GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_actual_bootstrap_length_result {World Event} (backend : gateway_backend World Event)
    io native stable discipline module_filename canonicalizes
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes)
    ge before world information resolved filename bytes temporaries returned after next observed :
  gateway_bootstrap_filename_information native stable discipline information filename bytes before world ->
  gateway_step backend ge
    (gateway_live (Callstate (gateway_bootstrap_signature gateway_bounded_length_api)
      [filename; Vlong (Int64.repr 4096)]
      (bootstrap_length_cont information resolved temporaries) before) world)
    (gateway_primitive observed)
    (gateway_live (Returnstate returned (bootstrap_length_cont information resolved temporaries) after) next) ->
  returned = Vlong (Int64.repr (Z.min 4096 (Z.of_nat (length bytes)))) /\
    gateway_bootstrap_filename_information native stable discipline information filename bytes after next.
Proof.
  intros INFORMATION STEP.
  destruct INFORMATION as [INFO [STRING PROTECTED]].
  assert (OPERATION : gateway_bootstrap_operation backend gateway_bounded_length_api
    [filename; Vlong (Int64.repr 4096)] before world returned after next observed).
  { inversion STEP; subst; cbn [gateway_bootstrap_operation gateway_bootstrap_signature gateway_runtime_operation]; eassumption. }
  destruct (@gateway_bounded_length_operation World Event backend io native stable discipline module_filename canonicalizes
    runtime before world filename bytes 4096 returned after next observed (proj1 INFO) STRING PROTECTED
    ltac:(change (0 <= 4096 <= 18446744073709551615); lia)
    OPERATION) as [[SIDE [ACCESS [FRAME QUIET]]] RESULT].
  split; [exact RESULT |].
  eapply gateway_bootstrap_filename_information_retained;
    [exact (conj INFO (conj STRING PROTECTED)) |exact SIDE |exact ACCESS |exact FRAME].
Qed.
