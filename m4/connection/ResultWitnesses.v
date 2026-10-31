(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-structures.result: Allocated source inputs for arbitrary field/global words. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Globalenvs Ctypes Clight.
Require Import Slice LibraryWitnesses ScalarMemory ResultLayout ResultSource ResultSafety.
Import ListNotations.
Open Scope Z_scope.

Theorem source_result_global_symbols :
  Genv.find_symbol result_ge _run_id = Some 74%positive /\
  Genv.find_symbol result_ge _run_uid = Some 77%positive.
Proof. split; vm_compute; reflexivity. Qed.

Theorem allocated_result_globals : forall run uid,
  exists m, result_globals m 74%positive 77%positive run uid.
Proof.
  intros run uid.
  destruct (Mem.alloc (vacant_memory 74%positive) 0 8) as [m1 b1] eqn:A1.
  assert (B1 : b1 = 74%positive) by (exact (Mem.alloc_result _ _ _ _ _ A1)); subst b1.
  destruct (Mem.alloc m1 0 0) as [m2 b2] eqn:A2.
  destruct (Mem.alloc m2 0 0) as [m3 b3] eqn:A3.
  destruct (Mem.alloc m3 0 4) as [m4 b4] eqn:A4.
  assert (B4 : b4 = 77%positive).
  { rewrite (Mem.alloc_result _ _ _ _ _ A4), (Mem.nextblock_alloc _ _ _ _ _ A3),
      (Mem.nextblock_alloc _ _ _ _ _ A2), (Mem.nextblock_alloc _ _ _ _ _ A1); reflexivity. }
  subst b4.
  assert (RUN : Mem.valid_access m4 Mint64 74%positive 0 Writable).
  { eapply Mem.valid_access_alloc_other; [exact A4|].
    eapply Mem.valid_access_alloc_other; [exact A3|].
    eapply Mem.valid_access_alloc_other; [exact A2|].
    eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact A1|cbn; lia|cbn; lia|exists 0; reflexivity]. }
  assert (UID : Mem.valid_access m4 Mint32 77%positive 0 Writable).
  { eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact A4|cbn; lia|cbn; lia|exists 0; reflexivity]. }
  destruct (Mem.valid_access_store _ _ _ _ (Vlong run) RUN) as [m5 RS].
  assert (UID5 : Mem.valid_access m5 Mint32 77%positive 0 Writable)
    by (eapply Mem.store_valid_access_1; eassumption).
  destruct (Mem.valid_access_store _ _ _ _ (Vint uid) UID5) as [m6 US].
  exists m6; split.
  - erewrite Mem.load_store_other; [|exact US|left; discriminate].
    erewrite Mem.load_store_same by exact RS; reflexivity.
  - erewrite Mem.load_store_same by exact US; reflexivity.
Qed.

Theorem arbitrary_result_source_input : forall run uid,
  exists m output, result_input m output 0 run uid.
Proof.
  intros run uid. destruct (allocated_result_globals run uid) as [base [RUN UID]].
  destruct (Mem.alloc base 0 144) as [m output] eqn:ALLOC.
  exists m, output; split.
  - split; [lia|]. split; [vm_compute; discriminate|]. split; [exists 0; reflexivity|].
    red; intros pos BOUND. eapply Mem.perm_implies; [eapply Mem.perm_alloc_2; eassumption|constructor].
  - exists 74%positive, 77%positive.
    destruct source_result_global_symbols as [R U]. split; [exact R|]. split; [exact U|].
    split; eapply Mem.load_alloc_other; eassumption.
Qed.

Theorem arbitrary_result_source_witness : forall cell kind stage detail entry run uid,
  exists m output final,
    result_input m output 0 run uid /\
    LibraryMachine.library_steps result_ge cell
      (Machine.live (result_initial output 0 kind stage detail entry Kstop m))
      (map LibraryMachine.original_event (repeat (Machine.source_step Events.E0) 161))
      (Machine.live (Returnstate Vundef Kstop final)) /\
    result_contents final output 0 kind stage detail entry uid run.
Proof.
  intros cell kind stage detail entry run uid.
  destruct (arbitrary_result_source_input run uid) as [m [output INPUT]].
  destruct (result_success_exists cell m output 0 kind stage detail entry uid run Kstop INPUT)
    as [final [RUN CONTENTS]]. exists m, output, final; auto.
Qed.
