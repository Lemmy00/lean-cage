(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Failed object setup cannot return a usable module. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayInitializerObjectsSource
  GatewayInitializerObjectFrontiers GatewaySourceSegmentAutomation GatewaySourceBoundCalls GatewayUnaryExpressions GatewayFramedRuntime
  GatewayFailurePaths GatewaySourceCuts GatewayModuleSource GatewayModulePublication.
Import ListNotations.

Lemma initializer_pointer_return : gateway_pointer_return f_host_initialize.
Proof. repeat eexists; reflexivity. Qed.

Ltac initializer_null_negation :=
  eapply gateway_unary_expression_value with (value := Vnullptr) (result := Vint Int.one);
    [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |reflexivity].

Theorem gateway_initializer_import_failed {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters memory :
  gateway_ambient_closed backend property ->
  gateway_failure_when backend ge property (Returnstate Vnullptr (initializer_import_cont parameters) memory).
Proof.
  intro CLOSED; gateway_bound_source_failure CLOSED ltac:(fun _ => initializer_null_negation)
    ltac:(fun _ => reflexivity) initializer_pointer_return.
Qed.

Theorem gateway_initializer_module_failed {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters memory :
  gateway_ambient_closed backend property ->
  gateway_failure_when backend ge property (Returnstate Vnullptr (initializer_module_cont parameters) memory).
Proof.
  intro CLOSED; gateway_bound_source_failure CLOSED ltac:(fun _ => initializer_null_negation)
    ltac:(fun _ => reflexivity) initializer_pointer_return.
Qed.

Theorem gateway_initializer_workspace_failed {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters memory :
  gateway_ambient_closed backend property ->
  gateway_failure_when backend ge property (Returnstate Vnullptr (initializer_workspace_cont parameters) memory).
Proof.
  intro CLOSED; gateway_bound_source_failure CLOSED ltac:(fun _ => initializer_null_negation)
    ltac:(fun _ => reflexivity) initializer_pointer_return.
Qed.

Theorem gateway_initializer_path_failed {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters memory symbol result :
  gateway_ambient_closed backend property -> Genv.find_symbol ge _host_path_class = Some symbol ->
  (forall memory world, property memory world -> Mem.load Mptr memory symbol 0 = Some Vnullptr) ->
  gateway_failure_when backend ge property (Returnstate result (initializer_pathlib_cont parameters) memory).
Proof.
  intros CLOSED SYMBOL LOAD.
  gateway_bound_source_failure CLOSED
    ltac:(fun _ => first [initializer_null_negation |
      match goal with GOOD : property ?current ?world |- _ =>
        apply initializer_global_pointer_expression with (symbol := symbol); [exact SYMBOL |exact (LOAD current world GOOD)] end])
    ltac:(fun _ => reflexivity) initializer_pointer_return.
Qed.

Theorem gateway_initializer_cancel_failed {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters memory symbol :
  gateway_ambient_closed backend property -> Genv.find_symbol ge _host_cancellation_class = Some symbol ->
  (forall memory world, property memory world -> Mem.load Mptr memory symbol 0 = Some Vnullptr) ->
  gateway_failure_when backend ge property
    (State f_host_initialize Sskip (Kseq initializer_after_cancel Kstop) empty_env parameters memory).
Proof.
  intros CLOSED SYMBOL LOAD.
  gateway_bound_source_failure CLOSED
    ltac:(fun _ => first [initializer_null_negation |
      match goal with GOOD : property ?current ?world |- _ =>
        apply initializer_global_pointer_expression with (symbol := symbol); [exact SYMBOL |exact (LOAD current world GOOD)] end])
    ltac:(fun _ => reflexivity) initializer_pointer_return.
Qed.

Theorem gateway_initializer_outcome_failed {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters memory symbol :
  gateway_ambient_closed backend property -> Genv.find_symbol ge _host_outcome_class = Some symbol ->
  (forall memory world, property memory world -> Mem.load Mptr memory symbol 0 = Some Vnullptr) ->
  gateway_failure_when backend ge property
    (State f_host_initialize Sskip (Kseq module_outcome_rest Kstop) empty_env parameters memory).
Proof.
  intros CLOSED SYMBOL LOAD.
  gateway_bound_source_failure CLOSED
    ltac:(fun _ => first [initializer_null_negation |
      match goal with GOOD : property ?current ?world |- _ =>
        apply initializer_global_pointer_expression with (symbol := symbol); [exact SYMBOL |exact (LOAD current world GOOD)] end])
    ltac:(fun _ => reflexivity) initializer_pointer_return.
Qed.

Theorem gateway_initializer_workspace_publication_failed {World Event}
    (backend : gateway_backend World Event) ge (property : mem -> World -> Prop) parameters memory status :
  gateway_ambient_closed backend property -> status <> Int.zero ->
  gateway_failure_when backend ge property
    (Returnstate (Vint status) (initializer_workspace_add_cont parameters) memory).
Proof.
  intros CLOSED NONZERO; pose proof (Int.eq_false _ _ NONZERO) as DIFFERENT.
  gateway_bound_source_failure CLOSED ltac:(fun _ => fail)
    ltac:(fun _ => cbn -[Int.eq]; rewrite DIFFERENT; reflexivity) initializer_pointer_return.
Qed.

Theorem gateway_initializer_cancel_publication_failed {World Event}
    (backend : gateway_backend World Event) ge (property : mem -> World -> Prop) parameters memory status :
  gateway_ambient_closed backend property -> status <> Int.zero ->
  gateway_failure_when backend ge property
    (Returnstate (Vint status) (initializer_cancel_add_cont parameters) memory).
Proof.
  intros CLOSED NONZERO; pose proof (Int.eq_false _ _ NONZERO) as DIFFERENT.
  gateway_bound_source_failure CLOSED ltac:(fun _ => fail)
    ltac:(fun _ => cbn -[Int.eq]; rewrite DIFFERENT; reflexivity) initializer_pointer_return.
Qed.

Theorem gateway_initializer_outcome_publication_failed {World Event}
    (backend : gateway_backend World Event) ge (property : mem -> World -> Prop) parameters memory status :
  gateway_ambient_closed backend property -> status <> Int.zero ->
  gateway_failure_when backend ge property
    (Returnstate (Vint status) (module_outcome_add_cont parameters Kstop) memory).
Proof.
  intros CLOSED NONZERO; pose proof (Int.eq_false _ _ NONZERO) as DIFFERENT.
  gateway_bound_source_failure CLOSED ltac:(fun _ => fail)
    ltac:(fun _ => cbn -[Int.eq]; rewrite DIFFERENT; reflexivity) initializer_pointer_return.
Qed.
