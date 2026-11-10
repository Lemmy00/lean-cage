(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Source address and control proofs derive private global frames. *)
From Stdlib Require Import ZArith List Bool.
From compcert Require Import Coqlib Maps AST Values Memory Events Globalenvs Ctypes Cop Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayGlobalAddresses GatewayPointerOrigins
  GatewayPointerMemory GatewayPointerExpressions GatewayPointerEntry GatewayPointerControl GatewayOrdinarySource GatewayOrdinaryControl
  GatewayScopedMemory.
Import ListNotations.

Definition gateway_private_cells_region (ge : Clight.genv) object (_ : Z) := gateway_private_cell ge object.

Lemma gateway_assign_other_cells ge ty before object offset field value after :
  ~ gateway_private_cell ge object -> assign_loc ge ty before object offset field value after ->
  Mem.unchanged_on (gateway_private_cells_region ge) before after.
Proof.
  intros OTHER ASSIGN; inversion ASSIGN; subst.
  - eapply Mem.storev_unchanged_on; [eassumption |intros; exact OTHER].
  - eapply Mem.storebytes_unchanged_on; [eassumption |intros; exact OTHER].
  - match goal with STORE : store_bitfield _ _ _ _ _ _ _ _ _ _ |- _ => inversion STORE; subst end.
    eapply Mem.storev_unchanged_on; [eassumption |intros; exact OTHER].
Qed.

Theorem gateway_ordinary_assignment_frame ge body lhs rhs continuation environment temporaries before observed target :
  gateway_pointer_source ge (State body (Sassign lhs rhs) continuation environment temporaries before) ->
  gateway_ordinary_source (State body (Sassign lhs rhs) continuation environment temporaries before) ->
  step2 ge (State body (Sassign lhs rhs) continuation environment temporaries before) observed target ->
  Mem.unchanged_on (gateway_private_cells_region ge) before (memory_of target).
Proof.
  intros [MEMORY [LIVE [WHOLE [CURRENT [CONTINUATION [LOCALS TEMPORARIES]]]]]]
    [FUNCTION [ORDINARY REST]] STEP.
  change ((gateway_statement_addresses (Sassign lhs rhs) && true) = true) in CURRENT.
  apply andb_true_iff in CURRENT as [ADDRESSES TRIVIAL].
  change ((gateway_assignment_address_inputs lhs && gateway_expression_addresses gateway_private_cell_name rhs) = true)
    in ADDRESSES.
  apply andb_true_iff in ADDRESSES as [INPUTS VALUE].
  inversion STEP; subst; try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
  cbn [memory_of].
  eapply (gateway_assign_other_cells ge (typeof lhs) before loc ofs bf v m'); [|exact H11].
  intro PRIVATE.
  destruct (gateway_assignment_private_target ge environment temporaries before lhs loc ofs bf
    LOCALS TEMPORARIES MEMORY INPUTS H8 PRIVATE) as [identifier [ty [DIRECT [NAME OTHER]]]].
  subst lhs; change ((negb (gateway_private_cell_name identifier) && true) = true) in ORDINARY.
  rewrite NAME in ORDINARY; discriminate.
Qed.

Theorem gateway_ordinary_internal_frame ge source observed target :
  internal_state source -> gateway_pointer_source ge source -> gateway_ordinary_source source ->
  step2 ge source observed target ->
  Mem.unchanged_on (gateway_private_cells_region ge) (memory_of source) (memory_of target).
Proof.
  intros INTERNAL POINTER ORDINARY STEP.
  inversion STEP; subst; cbn [internal_state] in INTERNAL; try contradiction;
    cbn [memory_of]; try apply Mem.unchanged_on_refl.
  - exact (gateway_ordinary_assignment_frame ge f a1 a2 k e le m E0
      (State f Sskip k e le m') POINTER ORDINARY STEP).
  - destruct POINTER as [MEMORY [LIVE [WHOLE [CURRENT [CONTINUATION [LOCALS TEMPORARIES]]]]]].
    eapply gateway_environment_avoids_free; [|eassumption].
    intros identifier object ty position LOOKUP; exact (LOCALS identifier object ty LOOKUP).
  - destruct POINTER as [MEMORY [LIVE [WHOLE [CURRENT [CONTINUATION [LOCALS TEMPORARIES]]]]]].
    eapply gateway_environment_avoids_free; [|eassumption].
    intros identifier object ty position LOOKUP; exact (LOCALS identifier object ty LOOKUP).
  - destruct POINTER as [MEMORY [LIVE [WHOLE [CURRENT [CONTINUATION [LOCALS TEMPORARIES]]]]]].
    eapply gateway_environment_avoids_free; [|eassumption].
    intros identifier object ty position LOOKUP; exact (LOCALS identifier object ty LOOKUP).
  - destruct POINTER as [MEMORY [LIVE CONTROL]]; inversion H; subst.
    match goal with ALLOC : alloc_variables _ _ _ _ _ _ |- _ =>
      destruct (gateway_scope_allocation ge (gateway_private_cells_region ge) _ _ _ _ _ ALLOC
        (fun object position PRIVATE => LIVE object PRIVATE) (gateway_environment_empty_avoids _)) as [ENVIRONMENT FRAME]
    end.
    exact FRAME.
Qed.
