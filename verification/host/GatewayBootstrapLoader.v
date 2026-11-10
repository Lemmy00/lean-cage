(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: One actual loader call produces the string ownership used by C checks. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Events Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayBootstrapABI
  GatewayBootstrapSource GatewayBootstrapRuntime GatewayBootstrapInformation GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_actual_bootstrap_loader_result {World Event} (backend : gateway_backend World Event)
    io native stable discipline module_filename canonicalizes
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes)
    ge before world address information resolved result after next observed :
  discipline None before world -> native world information ->
  gateway_native_pointer before information Ptrofs.zero 32 Writable ->
  Mem.valid_access before Mptr information 0 Writable ->
  gateway_step backend ge
    (gateway_live (Callstate (gateway_bootstrap_signature gateway_loader_address_api)
      [address; Vptr information Ptrofs.zero] (bootstrap_loader_cont information resolved) before) world)
    (gateway_primitive observed)
    (gateway_live (Returnstate result (bootstrap_loader_cont information resolved) after) next) ->
  exists status, result = Vint status /\
    (status <> Int.zero -> exists filename,
      Mem.load Mptr after information 0 = Some filename /\
      (filename = Vnullptr \/ exists bytes name name_offset,
        filename = Vptr name name_offset /\
        gateway_bootstrap_filename_information native stable discipline information filename bytes after next /\
        ~ native next name /\ module_filename next address bytes)).
Proof.
  intros SIDE PRIVATE ACCESS FIELD STEP.
  assert (OPERATION : gateway_bootstrap_operation backend gateway_loader_address_api
    [address; Vptr information Ptrofs.zero] before world result after next observed).
  { inversion STEP; subst; cbn [gateway_bootstrap_operation gateway_bootstrap_signature gateway_runtime_operation]; eassumption. }
  destruct (@gateway_loader_address_operation World Event backend io native stable discipline module_filename canonicalizes
    runtime before world address information Ptrofs.zero result after next observed SIDE PRIVATE ACCESS FIELD OPERATION)
    as [[NEXT [RETAINED [FRAME QUIET]]] [PERMISSIONS [status [VALUE SUCCESS]]]].
  exists status; split; [exact VALUE |]. intro NONZERO.
  destruct (SUCCESS NONZERO) as [filename [LOAD [NULL |[bytes [name [name_offset [POINTER
    [STRING [PROTECTED [SEPARATE IDENTITY]]]]]]]]]].
  - exists filename; split; [exact LOAD |left; exact NULL].
  - exists filename; split; [exact LOAD |right].
    exists bytes, name, name_offset; split; [exact POINTER |]. split.
    + split.
      * split; [exact NEXT |]. split; [|exact LOAD].
        apply (proj1 RETAINED information); [exact (proj1 (proj2 (proj2 ACCESS))) |exact PRIVATE].
      * split; [exact STRING |exact PROTECTED].
    + split; assumption.
Qed.
