(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-structures.result: Independent ownership constructs the actual source path. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Slice Machine Deterministic StoreSteps ScalarMemory ResultLayout ResultSource LibraryMachine LibraryPreservation.
Import ListNotations.
Open Scope Z_scope.

Definition result_input m output ofs run uid :=
  result_destination m output ofs /\ exists rb ub,
    Genv.find_symbol result_ge _run_id = Some rb /\ Genv.find_symbol result_ge _run_uid = Some ub /\
    result_globals m rb ub run uid.
Definition result_outside base output ofs b pos :=
  Mem.valid_block base b /\ (b <> output \/ pos < ofs \/ ofs+144 <= pos).
Definition result_preserved base output ofs after :=
  Mem.unchanged_on (result_outside base output ofs) base after.

Lemma result_local_store_preserves : forall base output ofs local chunk pos value m after,
  ~ Mem.valid_block base local -> result_preserved base output ofs m ->
  Mem.store chunk m local pos value = Some after -> result_preserved base output ofs after.
Proof.
  intros base output ofs local chunk pos value m after FRESH PRE STORE.
  eapply Mem.unchanged_on_trans; [exact PRE|]. eapply Mem.store_unchanged_on; [exact STORE|].
  intros x BOUND [VALID _]; contradiction.
Qed.

Lemma result_local_stores_preserves : forall base output ofs local m cells after,
  ~ Mem.valid_block base local -> scalar_stores local m cells after ->
  result_preserved base output ofs m -> result_preserved base output ofs after.
Proof.
  intros base output ofs local m cells after FRESH STORES; induction STORES; intros PRE; [exact PRE|].
  apply IHSTORES. eapply result_local_store_preserves; eassumption.
Qed.

Theorem result_source_execution : forall base output ofs kind stage detail entry uid run k,
  result_input base output ofs run uid ->
  exists final,
    store_path result_ge (result_preserved base output ofs)
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
  assert (PA : result_preserved base output ofs allocated).
  { eapply Mem.alloc_unchanged_on; exact ALLOC. }
  assert (PB : result_preserved base output ofs built).
  { eapply result_local_stores_preserves; eassumption. }
  assert (PC : result_preserved base output ofs copied).
  { eapply Mem.unchanged_on_trans; [exact PB|]. eapply Mem.storebytes_unchanged_on; [exact COPY|].
    intros pos BOUND [_ [NE|[BEFORE|AFTER]]]; rewrite LEN in BOUND; lia. }
  assert (PF : result_preserved base output ofs final).
  { eapply Mem.unchanged_on_trans; [exact PC|]. eapply Mem.free_unchanged_on; [exact FREE|].
    intros pos BOUND [VALID _]; contradiction. }
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
    + apply Mem.unchanged_on_refl.
    + exact PA.
    + exact PC.
    + exact PF.
    + intros; eapply result_local_store_preserves; eassumption.
  - split.
    + intros c IN. erewrite Mem.load_free; [|exact FREE|left; exact ON].
      eapply result_struct_copy_fields; [eapply result_cells_complete; exact STORES|exact ALIGN|exact LOAD|exact COPY|exact IN].
    + exists local, copied; auto.
Qed.

Theorem result_return_exact : forall cell base output ofs kind stage detail entry uid run events value after,
  result_input base output ofs run uid ->
  library_steps result_ge cell (live (result_initial output ofs kind stage detail entry Kstop base)) events
    (live (Returnstate value Kstop after)) ->
  value = Vundef /\ result_contents after output ofs kind stage detail entry uid run /\
  result_preserved base output ofs after /\
  events = map original_event (repeat (source_step E0) 161) /\
  (exists local before, ~ Mem.valid_block base local /\ Mem.free before local 0 144 = Some after).
Proof.
  intros cell base output ofs kind stage detail entry uid run events value after INPUT RUN.
  destruct (result_source_execution base output ofs kind stage detail entry uid run Kstop INPUT) as [final [PATH [CONTENTS FREED]]].
  destruct (store_path_library_projection _ _ _ _ _ _ _ PATH _ _ RUN) as [old [EVENTS ORIGINAL]].
  destruct (store_path_return_exact _ _ _ _ _ _ _ _ _ _ PATH ORIGINAL) as [VALUE [MEM TRACE]]; subst.
  split; [reflexivity|]. split; [exact CONTENTS|]. split.
  - destruct (store_path_prefix_invariant _ _ _ _ _ _ _ _ _ PATH ORIGINAL); assumption.
  - split; [reflexivity|exact FREED].
Qed.

Theorem result_all_prefixes : forall cell base output ofs kind stage detail entry uid run events target,
  result_input base output ofs run uid ->
  library_steps result_ge cell (live (result_initial output ofs kind stage detail entry Kstop base)) events target ->
  result_preserved base output ofs (routine_memory target) /\ (length events <= 162)%nat.
Proof.
  intros cell base output ofs kind stage detail entry uid run events target INPUT RUN.
  destruct (result_source_execution base output ofs kind stage detail entry uid run Kstop INPUT) as [final [PATH _]].
  destruct (store_path_library_projection _ _ _ _ _ _ _ PATH _ _ RUN) as [old [EVENTS ORIGINAL]].
  subst events; rewrite map_length. eapply store_path_prefix_invariant; eassumption.
Qed.

Theorem result_defined_prefix : forall cell base output ofs kind stage detail entry uid run events s,
  result_input base output ofs run uid ->
  library_steps result_ge cell (live (result_initial output ofs kind stage detail entry Kstop base)) events (live s) ->
  (exists final, s = Returnstate Vundef Kstop final /\
    result_contents final output ofs kind stage detail entry uid run) \/
  (exists next, library_step result_ge cell (live s) (original_event (source_step E0)) (live next)).
Proof.
  intros cell base output ofs kind stage detail entry uid run events s INPUT RUN.
  destruct (result_source_execution base output ofs kind stage detail entry uid run Kstop INPUT) as [final [PATH [CONTENTS _]]].
  destruct (store_path_library_projection _ _ _ _ _ _ _ PATH _ _ RUN) as [old [EVENTS ORIGINAL]].
  destruct (store_path_defined_prefix _ _ _ _ _ _ _ _ _ PATH ORIGINAL) as [DONE|[next STEP]].
  - left; exists final; auto.
  - right; exists next; constructor; assumption.
Qed.

Theorem result_success_exists : forall cell base output ofs kind stage detail entry uid run k,
  result_input base output ofs run uid -> exists final,
  library_steps result_ge cell (live (result_initial output ofs kind stage detail entry k base))
    (map original_event (repeat (source_step E0) 161)) (live (Returnstate Vundef (call_cont k) final)) /\
  result_contents final output ofs kind stage detail entry uid run.
Proof.
  intros cell base output ofs kind stage detail entry uid run k INPUT.
  destruct (result_source_execution base output ofs kind stage detail entry uid run k INPUT) as [final [PATH [CONTENTS _]]].
  exists final; split; [apply original_runs_preserved; eapply store_path_actual; exact PATH|exact CONTENTS].
Qed.

Theorem result_freed_local_has_no_permission : forall cell base output ofs kind stage detail entry uid run events value after,
  result_input base output ofs run uid ->
  library_steps result_ge cell (live (result_initial output ofs kind stage detail entry Kstop base)) events
    (live (Returnstate value Kstop after)) ->
  exists local, ~ Mem.valid_block base local /\
    forall pos perm_kind permission, 0 <= pos < 144 -> ~ Mem.perm after local pos perm_kind permission.
Proof.
  intros cell base output ofs kind stage detail entry uid run events value after INPUT RUN.
  destruct (result_return_exact _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT RUN)
    as [_ [_ [_ [_ [local [before [FRESH FREE]]]]]]].
  exists local; split; [assumption|]. intros; eapply Mem.perm_free_2; eassumption.
Qed.

Theorem result_loss_every_prefix : forall cell base output ofs kind stage detail entry uid run n,
  result_input base output ofs run uid -> (n <= 161)%nat -> exists mid,
  library_steps result_ge cell (live (result_initial output ofs kind stage detail entry Kstop base))
    (map original_event (repeat (source_step E0) n)) (live mid) /\
  library_steps result_ge cell (live (result_initial output ofs kind stage detail entry Kstop base))
    (map original_event (repeat (source_step E0) n ++ [loss_step])) (dead (memory_of mid)) /\
  result_preserved base output ofs (memory_of mid).
Proof.
  intros cell base output ofs kind stage detail entry uid run n INPUT BOUND.
  destruct (result_source_execution base output ofs kind stage detail entry uid run Kstop INPUT)
    as [final [PATH _]].
  destruct (store_path_loss_every_prefix _ cell _ _ _ _ n PATH BOUND)
    as [mid [BEFORE [LOSS GOOD]]]. exists mid; split.
  - apply original_runs_preserved; exact BEFORE.
  - split; [apply original_runs_preserved; exact LOSS|exact GOOD].
Qed.
