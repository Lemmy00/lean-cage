(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: The same covered source execution retains pointer origins. *)
From Stdlib Require Import List Bool.
From compcert Require Import Coqlib Maps AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayGlobalAddresses GatewayPointerOrigins GatewayPointerMemory
  GatewayPointerExpressions GatewayPointerEntry GatewayPointerControl GatewayPointerExecution
  GatewayLinkedSource GatewayLinkedPointerExecution GatewayRuntimeMemory GatewayRuntimeCoverage.
Import ListNotations.

Definition gateway_pointer_state {World} ge (source : gateway_state World) : Prop :=
  match source with
  | gateway_live source _ => gateway_pointer_source ge source
  | gateway_dead memory _ => gateway_memory_avoids (gateway_private_cell ge) memory /\
      forall object, gateway_private_cell ge object -> Mem.valid_block memory object
  end.

Theorem gateway_pointer_replace_memory ge source after :
  gateway_pointer_source ge source -> gateway_memory_avoids (gateway_private_cell ge) after ->
  (forall object, gateway_private_cell ge object -> Mem.valid_block after object) ->
  gateway_pointer_source ge (gateway_replace_memory source after).
Proof.
  intros [MEMORY [LIVE CONTROL]] AFTER RETAINED; destruct source;
    cbn [gateway_pointer_source gateway_replace_memory memory_of].
  all: split; [exact AFTER |split; assumption].
Qed.

Theorem gateway_pointer_builtin_arguments ge body destination ef types arguments continuation environment temporaries before values :
  gateway_pointer_source ge
    (State body (Sbuiltin destination ef types arguments) continuation environment temporaries before) ->
  eval_exprlist ge environment temporaries before arguments types values ->
  Forall (gateway_pointer_avoids (gateway_private_cell ge)) values.
Proof.
  intros [MEMORY [LIVE [WHOLE [CURRENT [CONTINUATION [LOCALS TEMPORARIES]]]]]] EVALUATED.
  change ((forallb (gateway_expression_addresses gateway_private_cell_name) arguments && true) = true) in CURRENT.
  apply andb_true_iff in CURRENT as [SCOPED TRIVIAL].
  eapply gateway_private_arguments; [exact LOCALS |exact TEMPORARIES |exact MEMORY | |exact EVALUATED].
  apply Forall_forall; intros expression MEMBER; exact (proj1 (forallb_forall _ _) SCOPED expression MEMBER).
Qed.

Theorem gateway_covered_pointer_step {World Event} (backend : gateway_backend World Event) runtime storage callback first observed target :
  forallb gateway_runtime_function runtime = true ->
  (forall object, storage object -> ~ gateway_private_cell (Clight.globalenv (gateway_linked_program runtime)) object) ->
  gateway_callback_pointer_origin (gateway_private_cell (Clight.globalenv (gateway_linked_program runtime))) callback ->
  gateway_pointer_state (Clight.globalenv (gateway_linked_program runtime)) first ->
  gateway_covered_step backend (Clight.globalenv (gateway_linked_program runtime)) storage callback first observed target ->
  gateway_pointer_state (Clight.globalenv (gateway_linked_program runtime)) target.
Proof.
  intros RUNTIME STORAGE CALLBACK READY STEP; inversion STEP; subst; cbn [gateway_pointer_state] in READY |- *.
  - eapply gateway_runtime_linked_pointer_source; eassumption.
  - destruct READY as [MEMORY [LIVE [FUNCTION [CONTINUATION ARGUMENTS]]]].
    destruct (gateway_runtime_memory_pointer_scope _ _ _ _ _ _ _ _ STORAGE CALLBACK
      ltac:(split; [exact MEMORY |split; [exact LIVE |exact ARGUMENTS]]) H0)
      as [AFTER [RETAINED POOL]].
    split; [exact AFTER |split; [exact RETAINED |]]. split; [exact CONTINUATION |].
    eapply gateway_runtime_pool_origin; eassumption.
  - pose proof (gateway_pointer_builtin_arguments _ _ _ _ _ _ _ _ _ _ _ READY H) as ARGUMENTS.
    destruct READY as [MEMORY [LIVE [WHOLE [CURRENT [CONTINUATION [LOCALS TEMPORARIES]]]]]].
    destruct (gateway_runtime_memory_pointer_scope _ _ _ _ _ _ _ _ STORAGE CALLBACK
      ltac:(split; [exact MEMORY |split; [exact LIVE |exact ARGUMENTS]]) H1)
      as [AFTER [RETAINED POOL]].
    split; [exact AFTER |split; [exact RETAINED |]]. repeat split; try assumption; try reflexivity.
    apply gateway_opttemp_avoids; [exact TEMPORARIES |eapply gateway_runtime_pool_origin; eassumption].
  - pose proof READY as ORIGINAL; destruct READY as [MEMORY [LIVE CONTROL]].
    destruct (gateway_runtime_memory_pointer_scope _ _ _ _ _ _ _ _ STORAGE CALLBACK
      ltac:(split; [exact MEMORY |split; [exact LIVE |constructor]]) H0)
      as [AFTER [RETAINED POOL]].
    apply gateway_pointer_replace_memory; assumption.
  - exact READY.
  - exact (conj (proj1 READY) (proj1 (proj2 READY))).
  - destruct READY as [MEMORY [LIVE [FUNCTION [CONTINUATION ARGUMENTS]]]].
    destruct (gateway_runtime_memory_pointer_scope _ _ _ _ _ _ _ _ STORAGE CALLBACK
      ltac:(split; [exact MEMORY |split; [exact LIVE |exact ARGUMENTS]]) H0)
      as [AFTER [RETAINED POOL]]. split; assumption.
  - pose proof (gateway_pointer_builtin_arguments _ _ _ _ _ _ _ _ _ _ _ READY H) as ARGUMENTS.
    destruct READY as [MEMORY [LIVE CONTROL]].
    destruct (gateway_runtime_memory_pointer_scope _ _ _ _ _ _ _ _ STORAGE CALLBACK
      ltac:(split; [exact MEMORY |split; [exact LIVE |exact ARGUMENTS]]) H1)
      as [AFTER [RETAINED POOL]]. split; assumption.
Qed.

Theorem gateway_covered_pointer_prefix {World Event} (backend : gateway_backend World Event) runtime storage callback first observed target :
  forallb gateway_runtime_function runtime = true ->
  (forall object, storage object -> ~ gateway_private_cell (Clight.globalenv (gateway_linked_program runtime)) object) ->
  gateway_callback_pointer_origin (gateway_private_cell (Clight.globalenv (gateway_linked_program runtime))) callback ->
  gateway_pointer_state (Clight.globalenv (gateway_linked_program runtime)) first ->
  gateway_covered_steps backend (Clight.globalenv (gateway_linked_program runtime)) storage callback first observed target ->
  gateway_pointer_state (Clight.globalenv (gateway_linked_program runtime)) target.
Proof.
  intros RUNTIME STORAGE CALLBACK READY RUN; revert READY; induction RUN; intro READY; [exact READY |].
  apply IHRUN; eapply gateway_covered_pointer_step; eassumption.
Qed.
