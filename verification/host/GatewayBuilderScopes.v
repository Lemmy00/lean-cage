(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Fresh source headers select their own SDK view without global emptiness. *)
From Stdlib Require Import List.
From compcert Require Import Integers AST Values Memory.
From HostGateway Require Import GatewaySpawnActions GatewaySpawnDescriptors.

Record gateway_builder_registry := {
  gateway_registered_actions : val -> option (list gateway_spawn_action);
  gateway_registered_attributes : val -> option gateway_spawn_attributes
}.

Definition gateway_scoped_builders {World} (registry : World -> gateway_builder_registry)
    (actions attributes : block) (world : World) : gateway_spawn_builders :=
  {| gateway_builder_actions :=
       option_map (fun plan => (Vptr actions Ptrofs.zero, plan)) (gateway_registered_actions (registry world) (Vptr actions Ptrofs.zero));
     gateway_builder_attributes :=
       option_map (fun settings => (Vptr attributes Ptrofs.zero, settings))
         (gateway_registered_attributes (registry world) (Vptr attributes Ptrofs.zero)) |}.

(* This records only allocation incarnation. Mem.valid_block remains true after
   free; there is no assertion that an old SDK object remains initialized/live. *)
Definition gateway_builder_registry_allocated (memory : mem) registry : Prop :=
  (forall pointer plan, gateway_registered_actions registry pointer = Some plan ->
    exists object offset, pointer = Vptr object offset /\ Mem.valid_block memory object) /\
  (forall pointer settings, gateway_registered_attributes registry pointer = Some settings ->
    exists object offset, pointer = Vptr object offset /\ Mem.valid_block memory object).

Theorem gateway_fresh_builder_scope_empty {World} (registry : World -> gateway_builder_registry)
    world before actions attributes :
  gateway_builder_registry_allocated before (registry world) ->
  ~ Mem.valid_block before actions -> ~ Mem.valid_block before attributes ->
  gateway_builder_actions (gateway_scoped_builders registry actions attributes world) = None /\
  gateway_builder_attributes (gateway_scoped_builders registry actions attributes world) = None.
Proof.
  intros [ACTIONS ATTRIBUTES] FRESH_ACTIONS FRESH_ATTRIBUTES; split; unfold gateway_scoped_builders; cbn.
  - destruct (gateway_registered_actions (registry world) (Vptr actions Ptrofs.zero)) as [plan |] eqn:LOOKUP;
      [|reflexivity].
    destruct (ACTIONS _ _ LOOKUP) as [object [offset [SAME LIVE]]]; inversion SAME; subst; contradiction.
  - destruct (gateway_registered_attributes (registry world) (Vptr attributes Ptrofs.zero)) as [settings |] eqn:LOOKUP;
      [|reflexivity].
    destruct (ATTRIBUTES _ _ LOOKUP) as [object [offset [SAME LIVE]]]; inversion SAME; subst; contradiction.
Qed.

Lemma gateway_scoped_actions_pointer {World} (registry : World -> gateway_builder_registry) actions attributes world pointer plan :
  gateway_builder_actions (gateway_scoped_builders registry actions attributes world) = Some (pointer, plan) ->
  pointer = Vptr actions Ptrofs.zero.
Proof.
  unfold gateway_scoped_builders; cbn; destruct (gateway_registered_actions (registry world) (Vptr actions Ptrofs.zero));
    intro SAME; inversion SAME; reflexivity.
Qed.

Lemma gateway_scoped_attributes_pointer {World} (registry : World -> gateway_builder_registry)
    actions attributes world pointer settings :
  gateway_builder_attributes (gateway_scoped_builders registry actions attributes world) = Some (pointer, settings) ->
  pointer = Vptr attributes Ptrofs.zero.
Proof.
  unfold gateway_scoped_builders; cbn; destruct (gateway_registered_attributes (registry world) (Vptr attributes Ptrofs.zero));
    intro SAME; inversion SAME; reflexivity.
Qed.
