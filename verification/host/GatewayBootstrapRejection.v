(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual loader failure reaches the real rejection before any string call. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySourceSegments GatewaySourceSegmentAutomation
  GatewayFramedRuntime GatewayBootstrapSource GatewayBootstrapLengthSource GatewayBootstrapValidationSource GatewayBootstrapCopySource
  GatewayIntegerFailures GatewayBootstrapFilename GatewayBootstrapRealpathSource.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_bootstrap_zero_loader_segment {World Event} (backend : gateway_backend World Event)
    (ge : Clight.genv) property information resolved memory :
  gateway_ambient_closed backend property ->
  exists temporaries,
    gateway_source_segment backend ge property
      (Returnstate (Vint Int.zero) (bootstrap_loader_cont information resolved) memory)
      (State f_host_bootstrap bootstrap_path_reject (Kseq bootstrap_after_first Kstop)
        (bootstrap_environment information resolved) temporaries memory) property.
Proof.
  intro CLOSED; eexists.
  let loads _ :=
    apply old_expression_value; eapply value_unary;
      [apply value_temp; repeat rewrite PTree.gso by discriminate; apply PTree.gss |reflexivity] in
  let reduce _ := reflexivity in
  gateway_segment_dynamic CLOSED loads reduce.
Qed.

Theorem actual_bootstrap_zero_loader_fails {World Event} (backend : gateway_backend World Event)
    (ge : Clight.genv) property information resolved before world events after next :
  gateway_ambient_closed backend property -> property before world ->
  gateway_steps backend ge
    (gateway_live (Returnstate (Vint Int.zero) (bootstrap_loader_cont information resolved) before) world)
    events (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) -> False.
Proof.
  intros CLOSED INPUT RUN.
  destruct (actual_bootstrap_zero_loader_segment backend ge property information resolved before CLOSED)
    as [temporaries SEGMENT].
  destruct (gateway_source_segment_cut backend ge property _ _ property SEGMENT
    before world events (Vint Int.zero) after next INPUT RUN)
    as (prefix & suffix & memory & current & EVENTS & QUIET & PREFIX & READY & REST).
  pose proof (gateway_actual_selected_integer_failure backend ge f_host_bootstrap bootstrap_path_reject
    (Kseq bootstrap_after_first Kstop) (bootstrap_environment information resolved) temporaries
    memory current suffix (Vint Int.zero) after next eq_refl ltac:(cbn; reflexivity) eq_refl REST) as FALSE.
  discriminate FALSE.
Qed.

Theorem actual_bootstrap_short_name_segment {World Event} (backend : gateway_backend World Event)
    (ge : Clight.genv) (canonical : bool) property information resolved temporaries memory size :
  gateway_ambient_closed backend property ->
  temporaries ! _size = Some (Vlong size) -> temporaries ! _tail = Some (Vlong (Int64.repr 30)) ->
  Int64.cmpu Cgt size (Int64.repr 4095) = false -> Int64.cmpu Cle size (Int64.repr 30) = true ->
  exists changed,
    gateway_source_segment backend ge property
      (State f_host_bootstrap (if canonical then bootstrap_canonical_validation else bootstrap_loaded_validation)
        (Kseq (if canonical then bootstrap_after_canonical_validation else bootstrap_after_loaded_validation) Kstop)
        (bootstrap_environment information resolved) temporaries memory)
      (State f_host_bootstrap bootstrap_path_reject
        (Kseq (if canonical then bootstrap_after_canonical_validation else bootstrap_after_loaded_validation) Kstop)
        (bootstrap_environment information resolved) changed memory) property.
Proof.
  intros CLOSED SIZE TAIL BOUNDED SHORT; destruct canonical; eexists.
  all: let loads _ := fail "unexpected source load in short-name rejection" in
    let reduce _ :=
      cbn [sem_binary_operation sem_binarith classify_binarith cast_int_long typeof];
      try change (Int.signed (Int.repr 4095)) with 4095;
      rewrite ?BOUNDED, ?SHORT;
      cbn [bool_val classify_bool Val.of_bool]; reflexivity in
    gateway_segment_dynamic CLOSED loads reduce.
Qed.

Theorem actual_bootstrap_null_loader_name_segment {World Event} (backend : gateway_backend World Event)
    (ge : Clight.genv) property information resolved memory status :
  gateway_ambient_closed backend property -> gateway_bootstrap_information_layout ge ->
  (forall memory world, property memory world -> Mem.load Mptr memory information 0 = Some Vnullptr) ->
  status <> Int.zero ->
  exists temporaries,
    gateway_source_segment backend ge property
      (Returnstate (Vint status) (bootstrap_loader_cont information resolved) memory)
      (State f_host_bootstrap bootstrap_path_reject (Kseq bootstrap_after_first Kstop)
        (bootstrap_environment information resolved) temporaries memory) property.
Proof.
  intros CLOSED LAYOUT NULL_NAME NONZERO; eexists.
  let loads _ :=
    first [eapply gateway_bootstrap_filename_value; [exact LAYOUT |eapply NULL_NAME; eassumption]
      |apply old_expression_value; eapply value_unary;
        [apply value_temp; repeat rewrite PTree.gso by discriminate;
          first [apply PTree.gss |reflexivity] |
         cbn; rewrite ?(Int.eq_false status Int.zero NONZERO); reflexivity]] in
  let reduce _ := cbn; rewrite ?(Int.eq_false status Int.zero NONZERO); reflexivity in
  gateway_segment_dynamic CLOSED loads reduce.
Qed.

Theorem actual_bootstrap_null_realpath_segment {World Event} (backend : gateway_backend World Event)
    (ge : Clight.genv) property information resolved filename loaded_size temporaries memory :
  gateway_ambient_closed backend property ->
  exists changed,
    gateway_source_segment backend ge property
      (Returnstate Vnullptr
        (bootstrap_realpath_cont information resolved filename loaded_size temporaries) memory)
      (State f_host_bootstrap bootstrap_path_reject (Kseq bootstrap_after_realpath Kstop)
        (bootstrap_environment information resolved) changed memory) property.
Proof.
  intro CLOSED; eexists.
  let loads _ := apply old_expression_value; eapply value_unary;
    [apply value_temp; repeat rewrite PTree.gso by discriminate; apply PTree.gss |reflexivity] in
  let reduce _ := reflexivity in
  gateway_segment_dynamic CLOSED loads reduce.
Qed.
