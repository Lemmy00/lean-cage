(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Linked visitor capabilities preserve source address scopes. *)
From Stdlib Require Import List Bool.
From compcert Require Import Coqlib Maps AST Values Memory Events Globalenvs Ctypes Cop Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayGlobalAddresses
  GatewayPointerOrigins GatewayPointerMemory GatewayPointerExpressions GatewayPointerEntry
  GatewayPointerControl GatewayPointerLabels GatewayPointerExecution GatewayLinkedSource.
Import ListNotations.

Lemma gateway_linked_pointer_expression (ge : Clight.genv) environment temporaries memory expression value :
  gateway_locals_avoid (gateway_private_cell ge) environment ->
  gateway_temporaries_avoid (gateway_private_cell ge) temporaries ->
  gateway_memory_avoids (gateway_private_cell ge) memory ->
  gateway_expression_addresses gateway_private_cell_name expression = true ->
  eval_expr ge environment temporaries memory expression value ->
  gateway_pointer_avoids (gateway_private_cell ge) value.
Proof.
  intros LOCALS TEMPORARIES MEMORY SCOPED EVALUATED.
  eapply (proj1 (gateway_expression_lvalue_avoids ge environment temporaries memory
    (gateway_private_cell ge) gateway_private_cell_name LOCALS
    (gateway_nonprivate_symbol _) TEMPORARIES MEMORY)); eassumption.
Qed.

Theorem gateway_linked_internal_pointer_source (ge : Clight.genv) source observed target :
  (forall value definition, Genv.find_funct ge value = Some definition -> gateway_pointer_definition definition = true) ->
  internal_state source -> gateway_pointer_source ge source ->
  step2 ge source observed target -> gateway_pointer_source ge target.
Proof.
  intros FUNCTIONS INTERNAL GOOD STEP; inversion STEP; subst;
    cbn [internal_state] in INTERNAL; try contradiction;
    cbn [gateway_pointer_source memory_of] in GOOD |- *.
  all: destruct GOOD as [MEMORY [LIVE CONTROL]].
  all: try (destruct CONTROL as [WHOLE [CURRENT [CONTINUATION [LOCALS TEMPORARIES]]]]).
  all: try (cbn [gateway_pointer_statement gateway_statement_addresses] in CURRENT;
    repeat rewrite andb_true_iff in CURRENT).
  all: try (cbn [gateway_pointer_cont] in CONTINUATION).
  all: cbn [gateway_pointer_source memory_of gateway_pointer_cont gateway_pointer_statement gateway_statement_addresses].
  all: repeat rewrite andb_true_iff.
  all: try solve [repeat split; assumption || reflexivity || tauto].
  - destruct CURRENT as [[TARGET VALUE] TRIVIAL].
    assert (SAFE : gateway_pointer_avoids (gateway_private_cell ge) v).
    { eapply gateway_cast_avoids; [eapply gateway_linked_pointer_expression; eassumption |eassumption]. }
    split; [eapply gateway_assign_avoids; eassumption |]. split.
    + intros candidate PRIVATE; eapply gateway_assign_blocks; [eassumption |apply LIVE; exact PRIVATE].
    + repeat split; assumption || reflexivity.
  - destruct CURRENT as [VALUE TRIVIAL].
    split; [exact MEMORY |]. split; [exact LIVE |].
    repeat split; try assumption; try reflexivity.
    apply gateway_temporaries_store; [exact TEMPORARIES |eapply gateway_linked_pointer_expression; eassumption].
  - destruct CURRENT as [[CALLEE ARGUMENTS] TRIVIAL].
    split; [exact MEMORY |]. split; [exact LIVE |]. split.
    + eapply FUNCTIONS; eassumption.
    + split; [repeat split; assumption |].
      eapply gateway_private_arguments; [exact LOCALS |exact TEMPORARIES |exact MEMORY | |eassumption].
      apply Forall_forall; intros expression MEMBER; exact (proj1 (forallb_forall _ _) ARGUMENTS expression MEMBER).
  - destruct b; repeat split; tauto.
  - split; [exact MEMORY |]. split; [exact LIVE |]. split; [exact WHOLE |]. split.
    + change ((true && (gateway_pointer_statement s1 && gateway_pointer_statement s2)) = true).
      repeat rewrite andb_true_iff; tauto.
    + repeat split; assumption || tauto.
  - destruct CURRENT as [VALUE TRIVIAL].
    split; [eapply gateway_free_list_avoids; eassumption |]. split.
    + intros object PRIVATE; eapply gateway_free_list_blocks; [eassumption |apply LIVE; exact PRIVATE].
    + split; [apply gateway_pointer_call_cont; exact CONTINUATION |exact I].
  - destruct CURRENT as [VALUE TRIVIAL].
    split; [eapply gateway_free_list_avoids; eassumption |]. split.
    + intros object PRIVATE; eapply gateway_free_list_blocks; [eassumption |apply LIVE; exact PRIVATE].
    + split; [apply gateway_pointer_call_cont; exact CONTINUATION |].
      eapply gateway_cast_avoids; [eapply gateway_linked_pointer_expression; eassumption |eassumption].
  - split; [eapply gateway_free_list_avoids; eassumption |]. split.
    + intros object PRIVATE; eapply gateway_free_list_blocks; [eassumption |apply LIVE; exact PRIVATE].
    + split; [exact CONTINUATION |exact I].
  - split; [exact MEMORY |]. split; [exact LIVE |].
    repeat split; try assumption.
    + apply gateway_pointer_switch; exact (proj2 CURRENT).
  - destruct (gateway_pointer_find_label (gateway_private_cell ge)
      lbl (fn_body f) (call_cont k) s' k' WHOLE
      (gateway_pointer_call_cont _ _ CONTINUATION) H) as [BODY CONT].
    repeat split; assumption.
  - destruct CONTROL as [FUNCTION [CONTINUATION ARGUMENTS]].
    destruct (gateway_function_entry_avoids (gateway_private_cell ge)
      _ _ _ _ _ _ _ LIVE MEMORY ARGUMENTS H) as [FINAL_MEMORY [LOCALS [TEMPORARIES FINAL_LIVE]]].
    split; [exact FINAL_MEMORY |]. split; [exact FINAL_LIVE |].
    repeat split; assumption.
  - destruct CONTROL as [[WHOLE [LOCALS [TEMPORARIES CONTINUATION]]] VALUE].
    split; [exact MEMORY |]. split; [exact LIVE |].
    repeat split; try assumption; try reflexivity.
    apply gateway_opttemp_avoids; assumption.
Qed.

Theorem gateway_runtime_linked_pointer_source runtime source observed target :
  forallb gateway_runtime_function runtime = true ->
  internal_state source ->
  gateway_pointer_source (Clight.globalenv (gateway_linked_program runtime)) source ->
  step2 (Clight.globalenv (gateway_linked_program runtime)) source observed target ->
  gateway_pointer_source (Clight.globalenv (gateway_linked_program runtime)) target.
Proof.
  intros RUNTIME INTERNAL SOURCE STEP.
  eapply gateway_linked_internal_pointer_source;
    [intros value definition FOUND; eapply gateway_linked_pointer_function; eassumption
    |exact INTERNAL |exact SOURCE |exact STEP].
Qed.
