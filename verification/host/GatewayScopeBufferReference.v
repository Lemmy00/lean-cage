(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Actual local memory effects retain separated caller regions. *)
From Stdlib Require Import ZArith.
From compcert Require Import AST Values Memory.
From HostGateway Require Import GatewayBufferReference.
Open Scope Z_scope.

Lemma gateway_scope_store_buffer {World} (native_private : World -> block -> Prop)
    readonly first second before after world chunk object position value :
  Mem.store chunk before object position value = Some after ->
  (forall offset, ~ readonly object offset) ->
  gateway_buffer_reference readonly first second before after /\
    gateway_native_reference native_private before world after world.
Proof.
  intros STORE READONLY; split.
  - split.
    + eapply Mem.store_unchanged_on; [exact STORE |]. intros offset RANGE HERE; exact (READONLY offset HERE).
    + intros other HERE offset kind permission; split;
        [eapply Mem.perm_store_1 | eapply Mem.perm_store_2]; exact STORE.
  - intros other LIVE PRIVATE; split; [eapply Mem.store_valid_block_1; eassumption | exact PRIVATE].
Qed.

Lemma gateway_scope_free_buffer {World} (native_private : World -> block -> Prop)
    readonly first second before after world object low high :
  Mem.free before object low high = Some after ->
  (forall offset, ~ readonly object offset) -> object <> first -> object <> second ->
  Mem.valid_block before first -> Mem.valid_block before second ->
  gateway_buffer_reference readonly first second before after /\
    gateway_native_reference native_private before world after world.
Proof.
  intros FREE READONLY FIRST SECOND FIRST_LIVE SECOND_LIVE.
  assert (FRAME : Mem.unchanged_on (fun other _ => other <> object) before after).
  { eapply Mem.free_unchanged_on; [exact FREE |]. intros offset RANGE DIFFERENT; contradiction. }
  split.
  - split.
    + eapply Mem.unchanged_on_implies; [exact FRAME |].
      intros other offset HERE LIVE SAME; subst other; exact (READONLY offset HERE).
    + intros other [SAME | SAME] offset kind permission; subst other;
        apply (Mem.unchanged_on_perm _ _ _ FRAME _ offset kind permission); congruence.
  - intros other LIVE PRIVATE; split; [eapply Mem.valid_block_free_1; eassumption | exact PRIVATE].
Qed.

Lemma gateway_scope_alloc_buffer {World} (native_private : World -> block -> Prop)
    readonly first second before after world object low high :
  Mem.alloc before low high = (after, object) ->
  Mem.valid_block before first -> Mem.valid_block before second ->
  gateway_buffer_reference readonly first second before after /\
    gateway_native_reference native_private before world after world.
Proof.
  intros ALLOC FIRST SECOND.
  assert (FRAME : Mem.unchanged_on (fun _ _ => True) before after) by
    (eapply Mem.alloc_unchanged_on; exact ALLOC).
  split.
  - split.
    + eapply Mem.unchanged_on_implies; [exact FRAME |]. intros; exact I.
    + intros other [SAME | SAME] offset kind permission; subst other;
        apply (Mem.unchanged_on_perm _ _ _ FRAME _ offset kind permission); auto.
  - intros other LIVE PRIVATE; split; [eapply Mem.valid_block_alloc; eassumption | exact PRIVATE].
Qed.
