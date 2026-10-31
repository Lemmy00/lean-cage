(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-callers.failure: Real eight-byte allocation and two complete writer calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Events Globalenvs Ctypes Clight.
Require Import Slice IO Machine WriteMemory WriteBytes Writers StoreSteps Library ProcessEffects
  FreshMemoryDraft FailureSourceDraft.
Import ListNotations.
Open Scope Z_scope.

Definition failure_packet stage error := map (fun x => Byte.repr (Int.unsigned x))
  (put32_values stage ++ put32_values error).
Lemma failure_packet_length : forall stage error, length (failure_packet stage error) = 8%nat.
Proof. intros; reflexivity. Qed.
Lemma failure_packet_encoding : forall stage error,
  map byte_encoding (put32_values stage ++ put32_values error) = map Byte (failure_packet stage error).
Proof. intros; reflexivity. Qed.

Theorem failure_preparation_symbols : exists pb fb,
  Genv.find_symbol failure_ge _put32 = Some pb /\
  Genv.find_funct failure_ge (Vptr pb Ptrofs.zero) = Some (Internal f_put32) /\
  Genv.find_symbol failure_ge _fault = Some fb /\
  Genv.find_funct failure_ge (Vptr fb Ptrofs.zero) = Some (Internal f_fault).
Proof. eexists; eexists. split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|]. split; vm_compute; reflexivity. Qed.

Theorem failure_prepare_execution : forall base fd stage error drop k,
  is_call_cont k -> Genv.find_symbol failure_ge ___stringlit_8 = Some drop ->
  exists local built,
    store_path failure_ge (old_memory base) (failure_initial fd stage error k base) 96
      (failure_drop_state local fd stage error drop k built) /\
    ~ Mem.valid_block base local /\ old_memory base built /\
    Mem.range_perm built local 0 8 Cur Freeable /\
    Mem.loadbytes built local 0 8 = Some (map Byte (failure_packet stage error)).
Proof.
  intros base fd stage error drop k CALL DROP.
  destruct (Mem.alloc base 0 8) as [allocated local] eqn:ALLOC.
  assert (FRESH : ~ Mem.valid_block base local) by (eapply Mem.fresh_block_alloc; exact ALLOC).
  assert (RANGE : Mem.range_perm allocated local 0 8 Cur Freeable).
  { intros pos BOUND; eapply Mem.perm_alloc_2; eassumption. }
  assert (PA : old_memory base allocated) by (eapply Mem.alloc_unchanged_on; exact ALLOC).
  destruct (byte_writes_exists (put32_values stage) allocated local 0) as [first FIRST].
  { intros pos BOUND; eapply Mem.perm_implies; [apply RANGE; cbn in *; lia|constructor]. }
  destruct (byte_writes_exists (put32_values error) first local 4) as [built SECOND].
  { intros pos BOUND. apply (byte_writes_permissions _ _ _ _ _ FIRST).
    eapply Mem.perm_implies; [apply RANGE; cbn in *; lia|constructor]. }
  assert (P1 : old_memory base first) by (eapply fresh_writes_preserve_old; eassumption).
  assert (P2 : old_memory base built) by (eapply fresh_writes_preserve_old; eassumption).
  assert (BOTH : byte_writes allocated local 0 (put32_values stage ++ put32_values error) built).
  { eapply byte_writes_append; [exact FIRST|exact SECOND]. }
  destruct failure_preparation_symbols as [pb [fb [PS [PF [FS FF]]]]].
  exists local, built. split.
  - eapply failure_prepare_source_path with (pb:=pb) (fb:=fb) (allocated:=allocated) (first:=first).
    + exact CALL.
    + exact PS.
    + exact PF.
    + exact FS.
    + exact FF.
    + exact DROP.
    + exact ALLOC.
    + exact FIRST.
    + exact SECOND.
    + apply Mem.unchanged_on_refl.
    + exact PA.
    + exact P1.
    + exact P2.
    + intros after PREFIX; exact (fresh_writer_prefix_preserves_old base allocated local 0 (put32_values stage) after FRESH PA PREFIX).
    + intros after PREFIX; exact (fresh_writer_prefix_preserves_old base first local 4 (put32_values error) after FRESH P1 PREFIX).
  - split; [exact FRESH|]. split; [exact P2|]. split.
    + intros pos BOUND. apply (byte_writes_permissions _ _ _ _ _ BOTH); apply RANGE; exact BOUND.
    + rewrite <- failure_packet_encoding. exact (byte_writes_content _ _ _ _ _ BOTH ltac:(discriminate)).
Qed.

Definition failure_request cell fd local count :=
  {| operation := writing; descriptor := fd; buffer_block := local; buffer_offset := 0;
     requested := count; errno_block := tls_block cell; errno_offset := tls_offset cell |}.

Theorem failure_packet_write_owned : forall base built local cell fd stage error count,
  tls_ready cell base -> ~ Mem.valid_block base local -> old_memory base built ->
  Mem.loadbytes built local 0 8 = Some (map Byte (failure_packet stage error)) ->
  (count <= 8)%nat ->
  write_owned (failure_request cell fd local (Z.of_nat count))
    (firstn count (failure_packet stage error)) built.
Proof.
  intros base built local cell fd stage error count TLS FRESH OLD LOAD BOUND.
  pose proof (old_memory_tls _ _ _ OLD TLS) as [LOW [HIGH ACCESS]].
  assert (NE : local <> tls_block cell).
  { intros SAME; subst; apply FRESH. destruct TLS as [_ [_ A]].
    eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies; [exact A|constructor]. }
  assert (LEN : length (firstn count (failure_packet stage error)) = count).
  { rewrite firstn_length, failure_packet_length, Nat.min_l by exact BOUND; reflexivity. }
  assert (PREFIX : Mem.loadbytes built local 0 (Z.of_nat count) =
    Some (map Byte (firstn count (failure_packet stage error)))).
  { replace (Z.of_nat count) with (Z.of_nat (length (firstn count (failure_packet stage error)))) by (rewrite LEN; reflexivity).
    apply load_first with (rest:=skipn count (failure_packet stage error)).
    rewrite firstn_skipn. exact LOAD. }
  unfold write_owned, failure_request; cbn. split; [reflexivity|]. split.
  - unfold owned; cbn. split; [lia|]. split; [change (0 <= 0 < 18446744073709551616); lia|].
    split; [change (Z.of_nat count <= 18446744073709551616); lia|].
    split; [exact LOW|]. split; [exact HIGH|]. split; [exact ACCESS|].
    split; [left; exact NE|]. exists (firstn count (failure_packet stage error)); auto.
  - split.
    + change (Z.of_nat (length (firstn count (failure_packet stage error))) = Z.of_nat count). rewrite LEN; reflexivity.
    + exact PREFIX.
Qed.
