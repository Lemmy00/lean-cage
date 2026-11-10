(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: The actual exec closes all protected aliases, including SDK/stderr slots. *)
From Stdlib Require Import ZArith List Lia.
From HostGateway Require Import GatewaySpawnDescriptors.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_aliases_closeexec {Object} (protected : Object -> Prop)
    (table : gateway_descriptor_table Object) : Prop :=
  forall fd entry, table fd = Some entry -> protected (gateway_descriptor_object entry) ->
    gateway_descriptor_cloexec entry = true.

Lemma gateway_public_descriptor_put {Object} (protected : Object -> Prop) table fd entry :
  gateway_aliases_closeexec protected table -> ~ protected (gateway_descriptor_object entry) ->
  gateway_aliases_closeexec protected (gateway_descriptor_put table fd entry).
Proof.
  intros CLOSED PUBLIC query actual FOUND PRIVATE.
  unfold gateway_descriptor_put in FOUND; destruct (Z.eq_dec query fd).
  - inversion FOUND; subst actual; contradiction.
  - eapply CLOSED; eassumption.
Qed.

Lemma gateway_closefrom_aliases {Object} (protected : Object -> Prop) table minimum :
  gateway_aliases_closeexec protected table ->
  gateway_aliases_closeexec protected (fun fd => if Z_le_dec minimum fd then None else table fd).
Proof.
  intros CLOSED fd entry FOUND PRIVATE; destruct (Z_le_dec minimum fd); [discriminate |].
  eapply CLOSED; eassumption.
Qed.

Lemma gateway_exec_closes_private {Object} (protected : Object -> Prop) table :
  gateway_aliases_closeexec protected table ->
  forall fd entry, gateway_descriptor_exec table fd = Some entry ->
    ~ protected (gateway_descriptor_object entry).
Proof.
  intros CLOSED fd entry FOUND PRIVATE.
  unfold gateway_descriptor_exec in FOUND; destruct (table fd) as [actual |] eqn:INPUT; [|discriminate].
  rewrite (CLOSED fd actual INPUT) in FOUND; [discriminate |].
  destruct (gateway_descriptor_cloexec actual); [discriminate |].
  inversion FOUND; subst actual; exact PRIVATE.
Qed.

(* This consumes the SAME full inherited table and source-built action plan.
   It deliberately retains slot2 and any SDK support entries until actual exec;
   close-on-exec, rather than deleting them from a projection, removes aliases. *)
Theorem gateway_private_spawn_closes_aliases {Object} (protected : Object -> Prop)
    (table : gateway_descriptor_table Object) data_peer cancel_peer data_endpoint cancel_endpoint prepared :
  4 <= data_peer -> 4 <= cancel_peer ->
  table data_peer = Some data_endpoint -> table cancel_peer = Some cancel_endpoint ->
  ~ protected (gateway_descriptor_object data_endpoint) ->
  ~ protected (gateway_descriptor_object cancel_endpoint) ->
  gateway_aliases_closeexec protected table ->
  gateway_spawn_actions_apply table (gateway_private_spawn_plan data_peer cancel_peer) = Some prepared ->
  forall fd entry, gateway_descriptor_exec prepared fd = Some entry ->
    ~ protected (gateway_descriptor_object entry).
Proof.
  intros DATA_BOUND CANCEL_BOUND DATA CANCEL DATA_PUBLIC CANCEL_PUBLIC CLOSED PLAN.
  apply gateway_exec_closes_private.
  unfold gateway_private_spawn_plan in PLAN;
    cbn [gateway_spawn_actions_apply gateway_spawn_action_apply] in PLAN; rewrite DATA in PLAN.
  unfold gateway_descriptor_put at 1 in PLAN.
  destruct (Z.eq_dec data_peer 0); [lia |]; rewrite DATA in PLAN.
  unfold gateway_descriptor_put at 1 2 in PLAN.
  destruct (Z.eq_dec cancel_peer 1); [lia |]; destruct (Z.eq_dec cancel_peer 0); [lia |].
  rewrite CANCEL in PLAN; inversion PLAN; subst prepared.
  apply gateway_closefrom_aliases.
  apply gateway_public_descriptor_put; [|exact CANCEL_PUBLIC].
  apply gateway_public_descriptor_put; [|exact DATA_PUBLIC].
  apply gateway_public_descriptor_put; [exact CLOSED |exact DATA_PUBLIC].
Qed.
