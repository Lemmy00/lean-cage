(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.memory: The exact result constructor also retains every pre-existing permission. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Slice Machine Deterministic StoreSteps ScalarMemory ResultLayout ResultSource ResultSafety.
Import ListNotations.
Open Scope Z_scope.
Definition old_permissions base after := forall b pos pk permission,
  Mem.perm base b pos pk permission -> Mem.perm after b pos pk permission.
Definition result_owned_preserved base output ofs after :=
  result_preserved base output ofs after /\ old_permissions base after.
Lemma result_owned_store : forall base output ofs local chunk pos value m after,
  ~Mem.valid_block base local -> result_owned_preserved base output ofs m ->
  Mem.store chunk m local pos value=Some after -> result_owned_preserved base output ofs after.
Proof.
  intros base output ofs local chunk pos value m after FRESH [OLD PERMS] STORE;split.
  - eapply result_local_store_preserves; eassumption.
  - unfold old_permissions;intros; eapply Mem.perm_store_1; [exact STORE|apply PERMS; assumption].
Qed.
Lemma result_owned_stores : forall base output ofs local m cells after,
  ~Mem.valid_block base local -> scalar_stores local m cells after ->
  result_owned_preserved base output ofs m -> result_owned_preserved base output ofs after.
Proof.
  intros base output ofs local m cells after FRESH STORES;induction STORES;intros OLD;[exact OLD|].
  apply IHSTORES; eapply result_owned_store; eassumption.
Qed.
Theorem result_owned_execution : forall base output ofs kind stage detail entry uid run k,
  result_input base output ofs run uid ->
  exists final,
    store_path result_ge (result_owned_preserved base output ofs)
      (result_initial output ofs kind stage detail entry k base) 161
      (Returnstate Vundef (call_cont k) final) /\
    result_contents final output ofs kind stage detail entry uid run /\
    (exists local before, ~ Mem.valid_block base local /\ Mem.free before local 0 144 = Some final).
Proof.
  intros base output ofs kind stage detail entry uid run k [DEST [rb [ub [RS [US GLOBAL]]]]].
  destruct DEST as [LOW [HIGH [ALIGN WRITABLE]]].
  destruct (Mem.alloc base 0 144) as [allocated local] eqn:ALLOC.
  assert (FRESH : ~ Mem.valid_block base local) by (eapply Mem.fresh_block_alloc; exact ALLOC).
  assert (LOCAL : Mem.range_perm allocated local 0 144 Cur Freeable).
  { red; intros; eapply Mem.perm_alloc_2; eassumption. }
  assert (RN : rb <> local).
  { intro EQ; subst rb; apply FRESH. eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies with (p1 := Readable);
    [eapply Mem.load_valid_access; exact (proj1 GLOBAL)|constructor]. }
  assert (UN : ub <> local).
  { intro EQ; subst ub; apply FRESH. eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies with (p1 := Readable);
    [eapply Mem.load_valid_access; exact (proj2 GLOBAL)|constructor]. }
  assert (ON : output <> local).
  { intro EQ; subst output; apply FRESH. eapply Mem.perm_valid_block.
    apply WRITABLE with (ofs := ofs); lia. }
  assert (GLOBALS : result_globals allocated rb ub run uid).
  { destruct GLOBAL as [R U]. split; eapply Mem.load_alloc_other; eassumption. }
  destruct (scalar_stores_exist local 144 (result_cells kind stage detail entry uid run) allocated
    (result_cells_valid _ _ _ _ _ _) LOCAL) as [built STORES].
  assert (BUILT_RANGE : Mem.range_perm built local 0 144 Cur Freeable).
  { red; intros; apply (scalar_stores_permissions _ _ _ _ STORES); apply LOCAL; assumption. }
  destruct (Mem.range_perm_loadbytes built local 0 144) as [bytes LOAD].
  { red; intros pos BOUND. eapply Mem.perm_implies; [apply BUILT_RANGE; cbn in *; lia|constructor]. }
  pose proof (Mem.loadbytes_length _ _ _ _ _ LOAD) as LENGTH.
  assert (LEN : Z.of_nat (length bytes) = 144) by (rewrite LENGTH; reflexivity).
  assert (OUT : Mem.range_perm built output ofs (ofs + Z.of_nat (length bytes)) Cur Writable).
  { rewrite LEN. red; intros pos BOUND. apply (scalar_stores_permissions _ _ _ _ STORES).
    eapply Mem.perm_alloc_1; [exact ALLOC|apply WRITABLE; exact BOUND]. }
  destruct (Mem.range_perm_storebytes _ _ _ _ OUT) as [copied COPY].
  assert (COPYLOC : assign_loc result_ge result_type built output (Ptrofs.repr ofs) Full
      (Vptr local Ptrofs.zero) copied).
  { assert (REP : Ptrofs.unsigned (Ptrofs.repr ofs) = ofs)
      by (apply Ptrofs.unsigned_repr; unfold Ptrofs.max_unsigned; lia).
    eapply assign_loc_copy with (bytes := bytes).
    - reflexivity.
    - intros; exists 0; reflexivity.
    - intros; rewrite REP; exact ALIGN.
    - left; congruence.
    - exact LOAD.
    - rewrite REP; exact COPY. }
  assert (COPIED_RANGE : Mem.range_perm copied local 0 144 Cur Freeable).
  { red; intros; eapply Mem.perm_storebytes_1; [exact COPY|apply BUILT_RANGE; assumption]. }
  destruct (Mem.range_perm_free _ _ _ _ COPIED_RANGE) as [final FREE].
  assert (PA : result_owned_preserved base output ofs allocated).
  { split; [eapply Mem.alloc_unchanged_on; exact ALLOC|].
    unfold old_permissions;intros; eapply Mem.perm_alloc_1; eassumption. }
  assert (PB : result_owned_preserved base output ofs built).
  { eapply result_owned_stores; eassumption. }
  assert (PC : result_owned_preserved base output ofs copied).
  { split.
    - eapply Mem.unchanged_on_trans; [exact (proj1 PB)|]. eapply Mem.storebytes_unchanged_on; [exact COPY|].
      intros pos BOUND [_ [NE|[BEFORE|AFTER]]]; rewrite LEN in BOUND; lia.
    - unfold old_permissions;intros; eapply Mem.perm_storebytes_1; [exact COPY|apply (proj2 PB); assumption]. }
  assert (PF : result_owned_preserved base output ofs final).
  { split.
    - eapply Mem.unchanged_on_trans; [exact (proj1 PC)|]. eapply Mem.free_unchanged_on; [exact FREE|].
      intros pos BOUND [VALID _]; contradiction.
    - intros object pos pk permission PERM. eapply Mem.perm_free_1; [exact FREE| |apply (proj2 PC); exact PERM].
      left; intro EQ; subst object; apply FRESH; eapply Mem.perm_valid_block; exact PERM. }
  exists final. split.
  - eapply result_construction_source_path with (rb := rb) (ub := ub)
      (allocated := allocated) (local := local) (built := built) (copied := copied)
      (uid := uid) (run := run).
    + exact RS.
    + exact US.
    + exact RN.
    + exact UN.
    + exact ALLOC.
    + exact STORES.
    + exact GLOBALS.
    + exact COPYLOC.
    + exact FREE.
    + split; [apply Mem.unchanged_on_refl|unfold old_permissions;intros; assumption].
    + exact PA.
    + exact PC.
    + exact PF.
    + intros; eapply result_owned_store; eassumption.
  - split.
    + intros c IN. erewrite Mem.load_free; [|exact FREE|left; exact ON].
      eapply result_struct_copy_fields; [eapply result_cells_complete; exact STORES|exact ALIGN|exact LOAD|exact COPY|exact IN].
    + exists local, copied; auto.
Qed.
