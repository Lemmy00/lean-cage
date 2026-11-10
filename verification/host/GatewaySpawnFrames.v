(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Source memory instructions preserve only the actual disjoint SDK representation. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewaySpawnResources GatewaySpawnActions.
Open Scope Z_scope.

Section SourceFrames.
Context {World Event} (backend : gateway_backend World Event) io native stable discipline resources
  builders genuine footprint
  (runtime : gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint).

Lemma gateway_builder_allocation before after world low high object :
  genuine before world -> Mem.alloc before low high = (after, object) -> genuine after world.
Proof.
  intros GENUINE ALLOCATED.
  eapply (gateway_builder_representation_frame _ _ _ _ _ _ _ _ _ runtime); [exact GENUINE |].
  eapply Mem.alloc_unchanged_on; exact ALLOCATED.
Qed.

Definition gateway_not_builder_block world object : Prop :=
  (forall offset actions, gateway_builder_actions (builders world) <> Some (Vptr object offset, actions)) /\
  (forall offset attributes, gateway_builder_attributes (builders world) <> Some (Vptr object offset, attributes)).

Lemma gateway_builder_other_block before world object :
  genuine before world -> native world object -> gateway_not_builder_block world object ->
  forall position, ~ footprint world object position.
Proof.
  intros GENUINE NATIVE [ACTIONS ATTRIBUTES] position INSIDE.
  destruct (gateway_builder_native_footprint _ _ _ _ _ _ _ _ _ runtime
    before world object position GENUINE NATIVE INSIDE) as [[offset [actions LIVE]] | [offset [attributes LIVE]]].
  - exact (ACTIONS offset actions LIVE).
  - exact (ATTRIBUTES offset attributes LIVE).
Qed.

Lemma gateway_builder_store before after world object offset chunk value :
  genuine before world -> native world object -> gateway_not_builder_block world object ->
  Mem.store chunk before object offset value = Some after -> genuine after world.
Proof.
  intros GENUINE NATIVE OTHER STORED.
  eapply (gateway_builder_representation_frame _ _ _ _ _ _ _ _ _ runtime); [exact GENUINE |].
  eapply Mem.store_unchanged_on; [exact STORED |].
  intros position _; eapply gateway_builder_other_block; eassumption.
Qed.

Lemma gateway_builder_free before after world object low high :
  genuine before world -> native world object -> gateway_not_builder_block world object ->
  Mem.free before object low high = Some after -> genuine after world.
Proof.
  intros GENUINE NATIVE OTHER FREED.
  eapply (gateway_builder_representation_frame _ _ _ _ _ _ _ _ _ runtime); [exact GENUINE |].
  eapply Mem.free_unchanged_on; [exact FREED |].
  intros position _; eapply gateway_builder_other_block; eassumption.
Qed.
End SourceFrames.
