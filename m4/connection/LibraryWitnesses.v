(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-library.evidence: Actual owned cells; no whole-program initialization claim. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Slice Machine Library LibraryMachine LibraryControl Fault.
Import ListNotations.
Open Scope Z_scope.

Definition vacant_memory (next : block) : mem.
Proof.
  refine (Mem.mkmem (Mem.mem_contents Mem.empty) (Mem.mem_access Mem.empty) next _ _ _).
  - exact (Mem.access_max Mem.empty).
  - intros b ofs k UNUSED. cbn. rewrite PMap.gi. reflexivity.
  - exact (Mem.contents_default Mem.empty).
Defined.

Theorem any_owned_global_cell : forall b,
  exists base m, Mem.alloc base 0 8 = (m, b) /\ Mem.valid_access m Mint64 b 0 Writable.
Proof.
  intros b. destruct (Mem.alloc (vacant_memory b) 0 8) as [m fresh] eqn:ALLOC.
  assert (SAME : fresh = b) by (exact (Mem.alloc_result _ _ _ _ _ ALLOC)); subst fresh.
  exists (vacant_memory b), m; split; [exact ALLOC|].
  eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
  eapply Mem.valid_access_alloc_same; [exact ALLOC|cbn; lia|cbn; lia|exists 0; reflexivity].
Qed.

Lemma strings_survive_mode_store : forall m after left right xs ys mb pointer,
  c_string m left xs -> c_string m right ys ->
  address_block left <> mb -> address_block right <> mb ->
  Mem.store Mint64 m mb 0 pointer = Some after ->
  c_string after left xs /\ c_string after right ys.
Proof.
  intros m after left right xs ys mb pointer [X [XB XL]] [Y [YB YL]] LX RY STORE.
  split; split; try assumption; split; try assumption;
    erewrite Mem.loadbytes_store_other; eauto.
Qed.

Theorem arbitrary_fault_inputs : forall (ge : genv) mb base xs ys,
  Genv.find_symbol ge _mode = Some mb -> Mem.valid_access base Mint64 mb 0 Writable ->
  Forall (fun b => b <> Byte.zero) xs -> Forall (fun b => b <> Byte.zero) ys ->
  Z.of_nat (length xs + length ys) <= 158 ->
  exists m mode name, fault_input ge m mode name xs ys.
Proof.
  intros ge mb base xs ys SYMBOL CELL X Y SIZE.
  destruct (allocated_comparison_spans base (xs ++ [Byte.zero]) (ys ++ [Byte.zero]))
    as [allocated [b [m [ALLOC [STORE [LEFT RIGHT]]]]]].
  { rewrite !app_length, !Nat2Z.inj_add in *; cbn; lia. }
  assert (NE : b <> mb).
  { intro SAME; subst b. apply (Mem.fresh_block_alloc _ _ _ _ _ ALLOC).
    eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies; [exact CELL|constructor]. }
  assert (ACCESS : Mem.valid_access m Mint64 mb 0 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact STORE|].
    eapply Mem.valid_access_alloc_other; eassumption. }
  destruct (Mem.valid_access_store _ _ _ _ (Vptr b Ptrofs.zero) ACCESS) as [after POINTER].
  set (mode := {|address_block := b; address_offset := 0|}).
  set (name := {|address_block := b; address_offset := Z.of_nat (length (xs ++ [Byte.zero]))|}).
  exists after, mode, name. split.
  - exists mb; split; [exact SYMBOL|]. unfold Mem.loadv; cbn.
    unfold address_value, mode; cbn. change (Ptrofs.repr 0) with Ptrofs.zero.
    pose proof (Mem.load_store_same _ _ _ _ _ _ POINTER) as LOAD. exact LOAD.
  - eapply strings_survive_mode_store; [split; eassumption|split; eassumption|exact NE|exact NE|exact POINTER].
Qed.

Definition normal_bytes := map Byte.repr [110;111;114;109;97;108].
Definition magic_bytes := map Byte.repr [76;67;51;82].

Theorem source_mode_symbol : Genv.find_symbol (Clight.globalenv Slice.prog) _mode = Some 75%positive.
Proof. vm_compute; reflexivity. Qed.

Theorem source_fault_inputs_inhabited : forall xs ys,
  Forall (fun b => b <> Byte.zero) xs -> Forall (fun b => b <> Byte.zero) ys ->
  Z.of_nat (length xs + length ys) <= 158 ->
  exists m mode name, fault_input (Clight.globalenv Slice.prog) m mode name xs ys.
Proof.
  intros xs ys X Y SIZE. destruct (any_owned_global_cell 75%positive) as [base [m [ALLOC CELL]]].
  eapply arbitrary_fault_inputs; [apply source_mode_symbol|exact CELL|exact X|exact Y|exact SIZE].
Qed.

Theorem equal_fault_source_witness : forall cell waits,
  exists m mode name events,
    fault_input (Clight.globalenv Slice.prog) m mode name normal_bytes normal_bytes /\
    library_steps (Clight.globalenv Slice.prog) cell (live (fault_initial name Kstop m)) events
      (live (Returnstate (Vint Int.one) Kstop m)) /\
    (length events = waits + 10)%nat /\ control_cost events = 10%nat.
Proof.
  intros cell waits. destruct (source_fault_inputs_inhabited normal_bytes normal_bytes) as [m [mode [name OWN]]].
  - repeat constructor; vm_compute; discriminate.
  - repeat constructor; vm_compute; discriminate.
  - cbn; lia.
  - destruct (fault_success_after_waits cell m mode name normal_bytes normal_bytes Kstop waits OWN)
      as [events RUN]. exists m, mode, name, events; split; [exact OWN|exact RUN].
Qed.

Theorem unequal_fault_source_witness : forall cell waits,
  exists m mode name events,
    fault_input (Clight.globalenv Slice.prog) m mode name normal_bytes magic_bytes /\
    library_steps (Clight.globalenv Slice.prog) cell (live (fault_initial name Kstop m)) events
      (live (Returnstate (Vint Int.zero) Kstop m)) /\
    (length events = waits + 10)%nat /\ control_cost events = 10%nat.
Proof.
  intros cell waits. destruct (source_fault_inputs_inhabited normal_bytes magic_bytes) as [m [mode [name OWN]]].
  - repeat constructor; vm_compute; discriminate.
  - repeat constructor; vm_compute; discriminate.
  - cbn; lia.
  - destruct (fault_success_after_waits cell m mode name normal_bytes magic_bytes Kstop waits OWN)
      as [events RUN]. exists m, mode, name, events; split; [exact OWN|exact RUN].
Qed.
