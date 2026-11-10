(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Spawn actions retain endpoints and close inherited aliases. *)
From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Open Scope Z_scope.

Record gateway_descriptor(Object:Type):={
  gateway_descriptor_object:Object;
  gateway_descriptor_cloexec:bool
}.
Arguments gateway_descriptor_object {Object} _.
Arguments gateway_descriptor_cloexec {Object} _.
Definition gateway_descriptor_table Object:=Z->option(gateway_descriptor Object).

Definition gateway_descriptor_put {Object}(table:gateway_descriptor_table Object)fd entry:=
  fun query=>if Z.eq_dec query fd then Some entry else table query.

Inductive gateway_spawn_action:=gateway_spawn_dup(source target:Z)|gateway_spawn_closefrom(lower:Z).

Definition gateway_spawn_action_apply {Object}(table:gateway_descriptor_table Object)action:
    option(gateway_descriptor_table Object):=
  match action with
  |gateway_spawn_dup source target=>match table source with
    |None=>None
    |Some descriptor=>Some(gateway_descriptor_put table target
      {|gateway_descriptor_object:=gateway_descriptor_object descriptor;gateway_descriptor_cloexec:=false|})end
  |gateway_spawn_closefrom lower=>Some(fun fd=>if Z_le_dec lower fd then None else table fd)
  end.

Fixpoint gateway_spawn_actions_apply {Object}(table:gateway_descriptor_table Object)(actions:list gateway_spawn_action):
    option(gateway_descriptor_table Object):=
  match actions with
  |[]=>Some table
  |first::rest=>match gateway_spawn_action_apply table first with
    |None=>None|Some changed=>gateway_spawn_actions_apply changed rest end
  end.

Definition gateway_descriptor_exec {Object}(table:gateway_descriptor_table Object):gateway_descriptor_table Object:=
  fun fd=>match table fd with
  |Some descriptor=>if gateway_descriptor_cloexec descriptor then None else Some descriptor
  |None=>None end.

Definition gateway_private_spawn_plan data_peer cancel_peer:=
  [gateway_spawn_dup data_peer 0;gateway_spawn_dup data_peer 1;
   gateway_spawn_dup cancel_peer 3;gateway_spawn_closefrom 4].

Theorem gateway_private_spawn_descriptors {Object}(table:gateway_descriptor_table Object)
    data_peer cancel_peer data_endpoint cancel_endpoint:
  4<=data_peer->4<=cancel_peer->table data_peer=Some data_endpoint->table cancel_peer=Some cancel_endpoint->
  exists prepared,gateway_spawn_actions_apply table(gateway_private_spawn_plan data_peer cancel_peer)=Some prepared /\
    gateway_descriptor_exec prepared 0=Some
      {|gateway_descriptor_object:=gateway_descriptor_object data_endpoint;gateway_descriptor_cloexec:=false|} /\
    gateway_descriptor_exec prepared 1=Some
      {|gateway_descriptor_object:=gateway_descriptor_object data_endpoint;gateway_descriptor_cloexec:=false|} /\
    gateway_descriptor_exec prepared 3=Some
      {|gateway_descriptor_object:=gateway_descriptor_object cancel_endpoint;gateway_descriptor_cloexec:=false|} /\
    (forall fd,4<=fd->gateway_descriptor_exec prepared fd=None).
Proof.
  intros DATA_BOUND CANCEL_BOUND DATA CANCEL.
  unfold gateway_private_spawn_plan;cbn[gateway_spawn_actions_apply gateway_spawn_action_apply];rewrite DATA.
  unfold gateway_descriptor_put at 1.
  destruct(Z.eq_dec data_peer 0);[lia|]. rewrite DATA.
  unfold gateway_descriptor_put at 1 2.
  destruct(Z.eq_dec cancel_peer 1);[lia|]. destruct(Z.eq_dec cancel_peer 0);[lia|]. rewrite CANCEL.
  eexists;split;[reflexivity|].
  split;[reflexivity|]. split;[reflexivity|]. split;[reflexivity|].
  intros fd BOUND;unfold gateway_descriptor_exec;destruct(Z_le_dec 4 fd);[reflexivity|lia].
Qed.

(* Standard error and other low inherited descriptors are deliberately outside
   the three-role application projection; this theorem does not erase them. *)
Theorem gateway_private_spawn_stderr {Object}(table:gateway_descriptor_table Object)
    data_peer cancel_peer data_endpoint cancel_endpoint prepared:
  4<=data_peer->4<=cancel_peer->table data_peer=Some data_endpoint->table cancel_peer=Some cancel_endpoint->
  gateway_spawn_actions_apply table(gateway_private_spawn_plan data_peer cancel_peer)=Some prepared->
  gateway_descriptor_exec prepared 2=gateway_descriptor_exec table 2.
Proof.
  intros DATA_BOUND CANCEL_BOUND DATA CANCEL PLAN.
  unfold gateway_private_spawn_plan in PLAN;cbn[gateway_spawn_actions_apply gateway_spawn_action_apply]in PLAN;rewrite DATA in PLAN.
  unfold gateway_descriptor_put at 1 in PLAN.
  destruct(Z.eq_dec data_peer 0);[lia|];rewrite DATA in PLAN.
  unfold gateway_descriptor_put at 1 2 in PLAN.
  destruct(Z.eq_dec cancel_peer 1);[lia|];destruct(Z.eq_dec cancel_peer 0);[lia|];rewrite CANCEL in PLAN.
  inversion PLAN;subst prepared;unfold gateway_descriptor_exec,gateway_descriptor_put;
    repeat destruct Z_le_dec;repeat destruct Z.eq_dec;try lia;reflexivity.
Qed.
