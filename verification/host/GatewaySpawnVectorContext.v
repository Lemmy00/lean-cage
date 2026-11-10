(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Individual runtime/SDK laws discharge launch-vector memory obligations. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Clight.
From HostGateway Require Import GatewayMachine GatewayThreadRuntime GatewaySpawnResources GatewaySpawnActions
  GatewaySpawnFrames GatewayVectorCells GatewaySpawnVectorMemory.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_spawn_local_block blocks object : Prop :=
  object = spawn_child_block blocks \/ object = spawn_arguments_block blocks \/ object = spawn_environment_block blocks.

Lemma gateway_spawn_selected_block blocks symbols cell :
  In cell (gateway_spawn_cell_plan blocks symbols) -> gateway_spawn_local_block blocks (vector_cell_block cell).
Proof.
  intro MEMBER; cbn [gateway_spawn_cell_plan] in MEMBER.
  repeat destruct MEMBER as [SAME | MEMBER]; try contradiction; subst cell;
    unfold gateway_spawn_local_block, spawn_pointer_cell; cbn; tauto.
Qed.

Section VectorContext.
Context {World Event} (backend : gateway_backend World Event) io native stable discipline thread_errno resources
  builders genuine footprint
  (thread : gateway_thread_runtime backend io native stable discipline thread_errno)
  (sdk : gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint).
Variable blocks : gateway_spawn_vector_blocks.
Variable state : World -> Prop.
Hypothesis STATE_AMBIENT : forall before world after next,
  discipline None before world -> state world -> gateway_interference backend before world after next -> state next.

Definition gateway_spawn_vector_base memory world : Prop :=
  discipline None memory world /\ genuine memory world /\ state world /\
  (forall object, gateway_spawn_local_block blocks object -> Mem.valid_block memory object /\ native world object /\
    gateway_not_builder_block builders world object).

Theorem gateway_spawn_base_ambient symbols before world after next :
  gateway_spawn_vector_base before world -> gateway_interference backend before world after next ->
  gateway_spawn_vector_base after next /\
  Mem.unchanged_on (gateway_vector_span (gateway_spawn_cell_plan blocks symbols)) before after.
Proof.
  intros [SIDE [GENUINE [STATE LOCALS]]] INTERFERENCE.
  destruct (gateway_thread_ambient _ _ _ _ _ _ thread None _ _ _ _ SIDE INTERFERENCE)
    as [NEXT_SIDE [ACCESS FRAME]].
  destruct (gateway_builder_ambient _ _ _ _ _ _ _ _ _ sdk _ _ _ _ SIDE GENUINE INTERFERENCE)
    as [BUILDERS NEXT_GENUINE].
  split.
  - split; [exact NEXT_SIDE |]. split; [exact NEXT_GENUINE |]. split.
    + exact (STATE_AMBIENT before world after next SIDE STATE INTERFERENCE).
    + intros object LOCAL; destruct (LOCALS object LOCAL) as [LIVE [PRIVATE OUTSIDE]].
      split; [eapply Mem.valid_block_unchanged_on; [exact FRAME |exact LIVE] |]. split.
      * apply (proj1 ACCESS); assumption.
      * unfold gateway_not_builder_block in *; rewrite BUILDERS; exact OUTSIDE.
  - eapply Mem.unchanged_on_implies; [exact FRAME |].
    intros object position [cell [MEMBER [OBJECT INSIDE]]].
    split; [left |tauto].
    destruct (LOCALS object) as [_ [PRIVATE _]]; [|exact PRIVATE].
    rewrite <- OBJECT; eapply gateway_spawn_selected_block; exact MEMBER.
Qed.

Theorem gateway_spawn_base_store symbols before world after cell :
  gateway_spawn_vector_base before world -> In cell (gateway_spawn_cell_plan blocks symbols) ->
  Mem.store (vector_cell_chunk cell) before (vector_cell_block cell) (vector_cell_offset cell)
    (vector_cell_value cell) = Some after -> gateway_spawn_vector_base after world.
Proof.
  intros [SIDE [GENUINE [STATE LOCALS]]] MEMBER STORE.
  destruct (LOCALS (vector_cell_block cell) (gateway_spawn_selected_block blocks symbols cell MEMBER))
    as [LIVE [PRIVATE OUTSIDE]].
  split.
  - eapply gateway_thread_native_store; [exact thread |exact SIDE |exact PRIVATE |exact STORE].
  - split.
    + eapply (gateway_builder_store backend io native stable discipline resources builders genuine footprint sdk);
        eassumption.
    + split; [exact STATE |]. intros object LOCAL.
      destruct (LOCALS object LOCAL) as [VALID [NATIVE OTHER]].
      split; [eapply Mem.store_valid_block_1; eassumption |]. split; assumption.
Qed.
End VectorContext.
