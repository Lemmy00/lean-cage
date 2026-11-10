(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual length returns reach the same guarded validation states. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySourceSegments
  GatewaySourceSegmentAutomation GatewayFramedRuntime GatewayBootstrapSource
  GatewayBootstrapLengthSource GatewayBootstrapLengthBindings GatewayBootstrapValidationSource
  GatewayBootstrapCanonicalSource GatewayBootstrapCanonicalLength GatewayBootstrapCopySource.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_bootstrap_loaded_length_segment {World Event} (backend : gateway_backend World Event)
    (ge : Clight.genv) property information resolved temporaries memory size :
  gateway_ambient_closed backend property ->
  gateway_source_segment backend ge property
    (Returnstate (Vlong size) (bootstrap_length_cont information resolved temporaries) memory)
    (State f_host_bootstrap bootstrap_loaded_validation
      (Kseq bootstrap_after_loaded_validation Kstop) (bootstrap_environment information resolved)
      (bootstrap_loaded_bound_temporaries size temporaries) memory) property.
Proof.
  intro CLOSED.
  let loads _ := first [apply gateway_bootstrap_sizeof_expression] in
  let reduce _ := reflexivity in
  gateway_segment_dynamic CLOSED loads reduce.
Qed.

Theorem actual_bootstrap_canonical_length_segment {World Event} (backend : gateway_backend World Event)
    (ge : Clight.genv) property information resolved filename loaded_size temporaries memory size :
  gateway_ambient_closed backend property ->
  gateway_source_segment backend ge property
    (Returnstate (Vlong size)
      (bootstrap_canonical_length_cont information resolved filename loaded_size temporaries) memory)
    (State f_host_bootstrap bootstrap_canonical_validation
      (Kseq bootstrap_after_canonical_validation Kstop) (bootstrap_environment information resolved)
      (bootstrap_canonical_sized_temporaries resolved filename loaded_size size temporaries) memory) property.
Proof.
  intro CLOSED.
  let loads _ := fail "unexpected load in canonical length binding" in
  let reduce _ := reflexivity in
  gateway_segment_dynamic CLOSED loads reduce.
Qed.
