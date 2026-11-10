(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The canonical validation uses the actual strnlen return and source size binding. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Clight.
Require Import ClightSteps StoreSteps LocalAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewaySourcePaths
  GatewayFramedRuntime GatewaySourceAutomation GatewayBootstrapABI GatewayBootstrapRuntime
  GatewayBootstrapSource GatewayBootstrapInformation GatewayBootstrapCanonicalResult
  GatewayBootstrapCanonicalAmbient GatewayBootstrapCanonicalSource GatewayBootstrapValidationSource
  GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_actual_bootstrap_canonical_length {World Event} (backend : gateway_backend World Event)
    io native stable discipline module_filename canonicalizes
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes)
    ge before world information object offset original resolved canonical continuation returned after next observed :
  gateway_bootstrap_canonical_information native stable discipline
    information object offset original resolved canonical before world ->
  gateway_step backend ge
    (gateway_live (Callstate (gateway_bootstrap_signature gateway_bounded_length_api)
      [Vptr resolved Ptrofs.zero; Vlong (Int64.repr 4096)] continuation before) world)
    (gateway_primitive observed)
    (gateway_live (Returnstate returned continuation after) next) ->
  returned = Vlong (Int64.repr (Z.min 4096 (Z.of_nat (length canonical)))) /\
  gateway_bootstrap_canonical_information native stable discipline
    information object offset original resolved canonical after next.
Proof.
  intros INFO STEP.
  assert (OPERATION : gateway_bootstrap_operation backend gateway_bounded_length_api
    [Vptr resolved Ptrofs.zero; Vlong (Int64.repr 4096)] before world returned after next observed).
  { inversion STEP; subst;
      cbn [gateway_bootstrap_operation gateway_bootstrap_signature gateway_runtime_operation]; eassumption. }
  destruct INFO as [INPUT [PRIVATE [WRITABLE [STRING PROTECTED]]]].
  destruct (@gateway_bounded_length_operation World Event backend io native stable discipline module_filename canonicalizes
    runtime before world (Vptr resolved Ptrofs.zero) canonical 4096 returned after next observed
    (proj1 (proj1 INPUT)) STRING PROTECTED ltac:(change (0 <= 4096 <= 18446744073709551615); lia) OPERATION)
    as [[SIDE [ACCESS [FRAME QUIET]]] RESULT].
  split; [exact RESULT |].
  eapply gateway_bootstrap_canonical_retained;
    [exact (conj INPUT (conj PRIVATE (conj WRITABLE (conj STRING PROTECTED)))) |
     exact SIDE |exact ACCESS |exact FRAME].
Qed.

Definition bootstrap_canonical_sized_temporaries resolved filename loaded_size size temporaries :=
  PTree.set _size (Vlong size) (PTree.set _t'9 (Vlong size)
    (bootstrap_canonical_return_temporaries resolved filename loaded_size temporaries)).

Theorem actual_bootstrap_canonical_size_binding {World Event} (backend : gateway_backend World Event)
    ge definition arguments target property information resolved filename loaded_size temporaries memory size result :
  gateway_ambient_closed backend property ->
  gateway_source_path backend ge definition arguments target property
    (State f_host_bootstrap bootstrap_canonical_validation
      (Kseq (match bootstrap_after_canonical_length with Ssequence _ rest => rest | _ => Sskip end) Kstop)
      (bootstrap_environment information resolved)
      (bootstrap_canonical_sized_temporaries resolved filename loaded_size size temporaries) memory) result ->
  gateway_source_path backend ge definition arguments target property
    (Returnstate (Vlong size)
      (bootstrap_canonical_length_cont information resolved filename loaded_size temporaries) memory) result.
Proof.
  intros CLOSED REST.
  unfold bootstrap_canonical_length_cont.
  repeat gateway_source_structure CLOSED.
  eapply gateway_source_same with (target := State f_host_bootstrap Sskip
    (Kseq bootstrap_after_canonical_length Kstop) (bootstrap_environment information resolved)
    (bootstrap_canonical_sized_temporaries resolved filename loaded_size size temporaries) memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros; apply certified_set_edge, old_expression_value, value_temp, PTree.gss.
  - do 2 gateway_source_structure CLOSED.
    exact REST.
Qed.
