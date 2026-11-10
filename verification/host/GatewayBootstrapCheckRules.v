(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual libc replies feed the corresponding source guard on the same operation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySetupPaths GatewaySetupComposition
  GatewaySourceSegments GatewaySourceSegmentAutomation GatewayFramedRuntime GatewayBootstrapABI
  GatewayBootstrapRuntime GatewayBootstrapPrimitiveResults GatewayBootstrapSuffixResult
  GatewayBootstrapSource GatewayBootstrapValidationSource GatewayBootstrapValidationChecks
  GatewayBootstrapCompareReturn GatewayBootstrapConstants GatewayThreadRuntime GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem bootstrap_suffix_rejection_segment {World Event} (backend : gateway_backend World Event)
    (ge : Clight.genv) property compared flag information resolved temporaries continuation memory status :
  gateway_ambient_closed backend property -> status <> Int.zero ->
  exists changed,
    gateway_source_segment backend ge property
      (Returnstate (Vint status)
        (bootstrap_comparison_cont compared flag f_host_bootstrap (bootstrap_environment information resolved)
          temporaries continuation) memory)
      (State f_host_bootstrap bootstrap_path_reject continuation
        (bootstrap_environment information resolved) changed memory) property.
Proof.
  intros CLOSED NONZERO; eexists.
  let loads _ := fail "unexpected source load after nonzero comparison" in
  let reduce _ := cbn; rewrite ?(Int.eq_false status Int.zero NONZERO); reflexivity in
  gateway_segment_dynamic CLOSED loads reduce.
Qed.

Theorem gateway_bootstrap_suffix_setup {World Event} (backend : gateway_backend World Event)
    io native stable discipline module_filename canonicalizes
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes)
    (ge : Clight.genv) property result object offset bytes suffix compared flag
    information resolved temporaries continuation memory :
  gateway_ambient_closed backend property -> call_cont continuation = Kstop ->
  (30 < length bytes)%nat ->
  (forall memory world, property memory world -> discipline None memory world /\
    gateway_bootstrap_protected native stable memory world (Vptr object offset) (bytes ++ [Byte.zero]) /\
    gateway_bootstrap_protected native stable memory world (Vptr suffix Ptrofs.zero)
      (bootstrap_suffix_bytes ++ [Byte.zero])) ->
  (forall before world after next observed, property before world ->
    gateway_bootstrap_post io native stable discipline gateway_native_no_output before world after next observed ->
    property after next) ->
  (skipn (length bytes - 30) bytes = bootstrap_suffix_bytes -> forall memory,
    gateway_setup_path backend ge result property
      (Returnstate (Vint Int.zero)
        (bootstrap_comparison_cont compared flag f_host_bootstrap (bootstrap_environment information resolved)
          temporaries continuation) memory)) ->
  gateway_setup_path backend ge result property
    (Callstate (gateway_bootstrap_signature gateway_memory_compare_api)
      [Vptr object (Ptrofs.add offset (Ptrofs.repr (Z.of_nat (length bytes) - 30)));
       Vptr suffix Ptrofs.zero; Vlong (Int64.repr 30)]
      (bootstrap_comparison_cont compared flag f_host_bootstrap (bootstrap_environment information resolved)
        temporaries continuation) memory).
Proof.
  intros CLOSED STOP LONG INPUT RETAIN CONTINUE.
  cbn [gateway_bootstrap_signature]; apply gateway_setup_external; [exact CLOSED |].
  intros before world returned after next observed GOOD OPERATION.
  destruct (INPUT _ _ GOOD) as [SIDE [PROTECTED SUFFIX]].
  destruct (gateway_actual_bootstrap_suffix_result backend io native stable discipline module_filename canonicalizes
    runtime ge before world object offset bytes suffix
    (bootstrap_comparison_cont compared flag f_host_bootstrap (bootstrap_environment information resolved)
      temporaries continuation) returned after next observed
    SIDE PROTECTED LONG SUFFIX ltac:(apply gateway_external_returned; exact OPERATION))
    as [POST [status [VALUE EQUAL]]].
  subst returned.
  assert (READY : property after next) by (eapply RETAIN; [exact GOOD |exact POST]).
  exists property; split; [exact READY |].
  destruct (Int.eq_dec status Int.zero) as [ZERO |NONZERO].
  - subst status; apply CONTINUE; apply (proj1 EQUAL); reflexivity.
  - destruct (bootstrap_suffix_rejection_segment backend ge property compared flag information resolved temporaries
      continuation after status CLOSED NONZERO) as [changed SEGMENT].
    eapply gateway_setup_after_segment; [exact SEGMENT |apply bootstrap_rejected_setup; exact STOP].
Qed.

Theorem gateway_bootstrap_length_setup {World Event} (backend : gateway_backend World Event)
    io native stable discipline module_filename canonicalizes
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes)
    (ge : Clight.genv) property result pointer bytes continuation memory :
  gateway_ambient_closed backend property ->
  (forall memory world, property memory world -> discipline None memory world /\
    gateway_error_cstring memory pointer bytes /\
    gateway_bootstrap_protected native stable memory world pointer (bytes ++ [Byte.zero])) ->
  (forall before world after next observed, property before world ->
    gateway_bootstrap_post io native stable discipline gateway_native_no_output before world after next observed ->
    property after next) ->
  (forall memory, gateway_setup_path backend ge result property
    (Returnstate (Vlong (Int64.repr (Z.min 4096 (Z.of_nat (length bytes))))) continuation memory)) ->
  gateway_setup_path backend ge result property
    (Callstate (gateway_bootstrap_signature gateway_bounded_length_api)
      [pointer; Vlong (Int64.repr 4096)] continuation memory).
Proof.
  intros CLOSED INPUT RETAIN CONTINUE.
  cbn [gateway_bootstrap_signature]; apply gateway_setup_external; [exact CLOSED |].
  intros before world returned after next observed GOOD OPERATION.
  destruct (INPUT _ _ GOOD) as [SIDE [STRING PROTECTED]].
  destruct (gateway_bootstrap_actual_length_post backend io native stable discipline module_filename canonicalizes
    runtime ge pointer bytes 4096 continuation before world returned after next observed SIDE STRING PROTECTED
    ltac:(change (0 <= 4096 <= 18446744073709551615); lia)
    ltac:(apply gateway_external_returned; exact OPERATION)) as [POST VALUE].
  subst returned; exists property; split; [eapply RETAIN; [exact GOOD |exact POST] |apply CONTINUE].
Qed.
