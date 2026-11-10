(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Derive retained snapshots from actual primitive write extents. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Integers Values Memory.
From HostGateway Require Import GatewayThreadRuntime.
Open Scope Z_scope.

Definition gateway_protected_native {World} (native : World -> block -> Prop)
    (protected immutable : block -> Prop) world object : Prop :=
  native world object /\ (protected object -> immutable object).

Record gateway_protected_memory {World} (native : World -> block -> Prop)
    (protected immutable : block -> Prop) (snapshot memory : mem) (world : World) : Prop := {
  gateway_protected_live : forall object, protected object -> Mem.valid_block memory object;
  gateway_protected_owned : forall object, protected object -> native world object;
  gateway_protected_readonly : forall object, protected object -> immutable object ->
    forall position, ~ Mem.perm memory object position Cur Writable;
  gateway_protected_snapshot : Mem.unchanged_on (fun object _ => protected object) snapshot memory
}.

Theorem gateway_protected_access {World} native stable protected immutable before world next :
  @gateway_access_retained World native stable before world next ->
  gateway_access_retained (gateway_protected_native native protected immutable) stable before world next.
Proof.
  intros [NATIVE STABLE]; split; [|exact STABLE].
  intros object LIVE [OWNED EXCLUDED]; split; [apply NATIVE; assumption |exact EXCLUDED].
Qed.

Theorem gateway_protected_frame {World} native stable protected immutable output world before after :
  @gateway_native_frame World native stable output world before after ->
  gateway_native_frame (gateway_protected_native native protected immutable) stable output world before after.
Proof.
  intro FRAME; eapply Mem.unchanged_on_implies; [exact FRAME |].
  intros object position [OWNED OUTSIDE]; split; [|exact OUTSIDE].
  destruct OWNED as [NATIVE |STABLE].
  - left; exact (proj1 NATIVE).
  - right; exact STABLE.
Qed.

Theorem gateway_protected_effect {World} native stable protected immutable snapshot before world after next output :
  @gateway_protected_memory World native protected immutable snapshot before world ->
  gateway_access_retained native stable before world next ->
  gateway_native_frame native stable output world before after ->
  (forall object position, protected object -> ~ output object position) ->
  gateway_protected_memory native protected immutable snapshot after next.
Proof.
  intros STATE ACCESS FRAME OUTSIDE.
  assert (RETAINED : Mem.unchanged_on (fun object _ => protected object) before after).
  { eapply Mem.unchanged_on_implies; [exact FRAME |].
    intros object position PROTECTED; split;
      [left; eapply gateway_protected_owned; eassumption |apply OUTSIDE; exact PROTECTED]. }
  constructor.
  - intros object PROTECTED; eapply Mem.valid_block_unchanged_on;
      [exact RETAINED |eapply gateway_protected_live; eassumption].
  - intros object PROTECTED; eapply (proj1 ACCESS);
      [eapply gateway_protected_live; eassumption |eapply gateway_protected_owned; eassumption].
  - intros object PROTECTED IMMUTABLE position WRITABLE.
    eapply (gateway_protected_readonly native protected immutable snapshot before world STATE object PROTECTED IMMUTABLE position).
    apply (proj2 (Mem.unchanged_on_perm _ _ _ RETAINED object position Cur Writable PROTECTED
      (gateway_protected_live native protected immutable snapshot before world STATE object PROTECTED))).
    exact WRITABLE.
  - eapply Mem.unchanged_on_trans; [eapply gateway_protected_snapshot; exact STATE |exact RETAINED].
Qed.

Theorem gateway_protected_writable_separate {World} native protected immutable snapshot memory world object position :
  @gateway_protected_memory World native protected immutable snapshot memory world ->
  gateway_protected_native native protected immutable world object ->
  Mem.perm memory object position Cur Writable -> ~ protected object.
Proof.
  intros STATE [_ EXCLUDED] WRITABLE PROTECTED.
  exact (gateway_protected_readonly native protected immutable snapshot memory world STATE object
    PROTECTED (EXCLUDED PROTECTED) position WRITABLE).
Qed.

Theorem gateway_protected_pointer_separate {World} native protected immutable snapshot memory world object offset amount :
  @gateway_protected_memory World native protected immutable snapshot memory world ->
  gateway_protected_native native protected immutable world object ->
  gateway_native_pointer memory object offset amount Writable -> 0 < amount -> ~ protected object.
Proof.
  intros STATE NATIVE [_ [_ [_ RANGE]]] POSITIVE.
  eapply gateway_protected_writable_separate;
    [exact STATE |exact NATIVE |apply (RANGE (Ptrofs.unsigned offset)); lia].
Qed.

Theorem gateway_protected_alloc {World} native protected immutable snapshot before world after object low high :
  @gateway_protected_memory World native protected immutable snapshot before world ->
  Mem.alloc before low high = (after, object) ->
  gateway_protected_memory native protected immutable snapshot after world.
Proof.
  intros STATE ALLOC.
  assert (FRAME : Mem.unchanged_on (fun _ _ => True) before after)
    by (eapply Mem.alloc_unchanged_on; exact ALLOC).
  constructor.
  - intros candidate PROTECTED; eapply Mem.valid_block_alloc;
      [exact ALLOC |eapply gateway_protected_live; eassumption].
  - intros; eapply gateway_protected_owned; eassumption.
  - intros candidate PROTECTED IMMUTABLE position WRITABLE.
    eapply (gateway_protected_readonly native protected immutable snapshot before world STATE candidate PROTECTED IMMUTABLE position).
    apply (proj2 (Mem.unchanged_on_perm _ _ _ FRAME candidate position Cur Writable I
      (gateway_protected_live native protected immutable snapshot before world STATE candidate PROTECTED))); exact WRITABLE.
  - eapply Mem.unchanged_on_trans; [eapply gateway_protected_snapshot; exact STATE |].
    eapply Mem.unchanged_on_implies; [exact FRAME |intros; exact I].
Qed.

Theorem gateway_protected_store {World} native protected immutable snapshot before world after object offset chunk value :
  @gateway_protected_memory World native protected immutable snapshot before world ->
  gateway_protected_native native protected immutable world object ->
  Mem.store chunk before object offset value = Some after ->
  gateway_protected_memory native protected immutable snapshot after world.
Proof.
  intros STATE NATIVE STORE.
  assert (FRAME : Mem.unchanged_on (fun candidate _ => protected candidate) before after).
  { eapply Mem.store_unchanged_on; [exact STORE |].
    intros position RANGE PROTECTED.
    eapply gateway_protected_writable_separate;
      [exact STATE |exact NATIVE | |exact PROTECTED].
    apply (proj1 (Mem.store_valid_access_3 _ _ _ _ _ _ STORE)); exact RANGE. }
  constructor.
  - intros candidate PROTECTED; eapply Mem.store_valid_block_1;
      [exact STORE |eapply gateway_protected_live; eassumption].
  - intros; eapply gateway_protected_owned; eassumption.
  - intros candidate PROTECTED IMMUTABLE position WRITABLE.
    eapply (gateway_protected_readonly native protected immutable snapshot before world STATE candidate PROTECTED IMMUTABLE position).
    apply (proj2 (Mem.unchanged_on_perm _ _ _ FRAME candidate position Cur Writable PROTECTED
      (gateway_protected_live native protected immutable snapshot before world STATE candidate PROTECTED))); exact WRITABLE.
  - eapply Mem.unchanged_on_trans; [eapply gateway_protected_snapshot; exact STATE |exact FRAME].
Qed.

Theorem gateway_protected_free {World} native protected immutable snapshot before world after object low high :
  @gateway_protected_memory World native protected immutable snapshot before world ->
  gateway_protected_native native protected immutable world object ->
  Mem.free before object low high = Some after ->
  gateway_protected_memory native protected immutable snapshot after world.
Proof.
  intros STATE NATIVE FREE.
  assert (FRAME : Mem.unchanged_on (fun candidate _ => protected candidate) before after).
  { eapply Mem.free_unchanged_on; [exact FREE |].
    intros position RANGE PROTECTED.
    eapply gateway_protected_writable_separate;
      [exact STATE |exact NATIVE | |exact PROTECTED].
    eapply Mem.perm_implies; [apply (Mem.free_range_perm _ _ _ _ _ FREE position RANGE) |constructor]. }
  constructor.
  - intros candidate PROTECTED; eapply Mem.valid_block_free_1;
      [exact FREE |eapply gateway_protected_live; eassumption].
  - intros; eapply gateway_protected_owned; eassumption.
  - intros candidate PROTECTED IMMUTABLE position WRITABLE.
    eapply (gateway_protected_readonly native protected immutable snapshot before world STATE candidate PROTECTED IMMUTABLE position).
    apply (proj2 (Mem.unchanged_on_perm _ _ _ FRAME candidate position Cur Writable PROTECTED
      (gateway_protected_live native protected immutable snapshot before world STATE candidate PROTECTED))); exact WRITABLE.
  - eapply Mem.unchanged_on_trans; [eapply gateway_protected_snapshot; exact STATE |exact FRAME].
Qed.
