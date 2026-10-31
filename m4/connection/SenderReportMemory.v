(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.memory: Retain all frame and result ownership across report I/O. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Require Import IO Machine WriteBytes WriteMemory WriteAll Library ProcessEffects FreshMemory FrameBytes
  FrameRecord SenderStorage WriteEffects.
Import ListNotations.
Open Scope Z_scope.
Definition sender_preserved cell base after := Mem.unchanged_on
  (fun b pos=>Mem.valid_block base b /\ outside_bytes (tls_block cell) (tls_offset cell) 4 b pos) base after.
Definition sender_live_memory cell base result_local bytes_local r digest bytes m :=
  sender_preserved cell base m /\ frame_result_owned m result_local 0 r digest /\
  readable_bytes m {|address_block:=bytes_local;address_offset:=0|} bytes /\
  Mem.range_perm m result_local 0 144 Cur Freeable /\ Mem.range_perm m bytes_local 0 160 Cur Freeable.
Lemma old_sender_preserved : forall cell base after,old_memory base after -> sender_preserved cell base after.
Proof. intros;eapply Mem.unchanged_on_implies;[exact H|intros;tauto]. Qed.
Lemma history_sender_preserved : forall cell base before after,
  sender_preserved cell base before -> tls_history cell before after -> sender_preserved cell base after.
Proof.
  intros;eapply Mem.unchanged_on_trans;[exact H|].
  eapply Mem.unchanged_on_implies;[eapply tls_history_outside;exact H0|intros;tauto].
Qed.
Lemma sender_storage_live : forall cell base result_local bytes_local r digest bytes m,
  sender_storage base result_local bytes_local r digest bytes m ->
  sender_live_memory cell base result_local bytes_local r digest bytes m.
Proof. intros cell base result_local bytes_local r digest bytes m [OLD REST];split;[apply old_sender_preserved;exact OLD|exact REST]. Qed.
Lemma fresh_tls_separate : forall cell base local,
  tls_ready cell base -> ~Mem.valid_block base local -> local<>tls_block cell.
Proof.
  intros cell base local [_ [_ [PERMS ALIGN]]] FRESH SAME;subst local;apply FRESH.
  eapply Mem.perm_valid_block with (ofs:=tls_offset cell);apply PERMS;cbn;lia.
Qed.

Theorem sender_live_history : forall cell base before after result_local bytes_local r digest bytes,
  result_local<>tls_block cell -> bytes_local<>tls_block cell ->
  sender_live_memory cell base result_local bytes_local r digest bytes before ->
  tls_history cell before after -> sender_live_memory cell base result_local bytes_local r digest bytes after.
Proof.
  intros cell base before after result_local bytes_local r digest bytes RNE BNE
    [OLD [OWN [[BOUNDS LOAD] [RFREE BFREE]]]] HISTORY.
  pose proof (tls_history_outside _ _ _ HISTORY) as OUTSIDE.
  split;[eapply history_sender_preserved;eassumption|]. split.
  - destruct OWN as [LOW [HIGH [ALIGN [PERMS [LEN [CONTENTS [DB DL]]]]]]].
    split;[exact LOW|]. split;[exact HIGH|]. split;[exact ALIGN|]. split.
    + intros pos RANGE;apply (tls_history_permissions _ _ _ HISTORY);apply PERMS;exact RANGE.
    + split;[exact LEN|]. split.
      * intros field IN;eapply Mem.load_unchanged_on;[exact OUTSIDE|intros;left;exact RNE|apply CONTENTS;exact IN].
      * split;[exact DB|]. eapply Mem.loadbytes_unchanged_on;[exact OUTSIDE|intros;left;exact RNE|exact DL].
  - split.
    + split;[exact BOUNDS|]. eapply Mem.loadbytes_unchanged_on;[exact OUTSIDE|intros;left;exact BNE|exact LOAD].
    + split;intros pos RANGE;apply (tls_history_permissions _ _ _ HISTORY);[apply RFREE|apply BFREE];exact RANGE.
Qed.

Definition sender_request cell fd bytes_local count :=
  {|operation:=writing;descriptor:=fd;buffer_block:=bytes_local;buffer_offset:=0;requested:=Z.of_nat count;
    errno_block:=tls_block cell;errno_offset:=tls_offset cell|}.
Lemma sender_request_cell : forall cell fd bytes_local count,cell_of (sender_request cell fd bytes_local count)=cell.
Proof. destruct cell;reflexivity. Qed.
Theorem sender_frame_write_owned : forall cell m fd bytes_local bytes count,
  tls_ready cell m -> bytes_local<>tls_block cell ->
  readable_bytes m {|address_block:=bytes_local;address_offset:=0|} bytes ->
  length bytes=160%nat -> (count<=160)%nat ->
  write_owned (sender_request cell fd bytes_local count) (firstn count bytes) m.
Proof.
  intros cell m fd bytes_local bytes count [EO [EW ACCESS]] NE READ LEN BOUND.
  assert (LENGTH : length (firstn count bytes)=count) by (rewrite firstn_length,LEN,Nat.min_l;lia).
  pose proof (readable_subspan m {|address_block:=bytes_local;address_offset:=0|} bytes 0 count READ
    ltac:(rewrite LEN;lia) ltac:(rewrite LEN;lia)) as SUB.
  destruct SUB as [SB LOAD];cbn [skipn offset_address address_block address_offset Z.add] in LOAD.
  rewrite LENGTH in LOAD. split;[reflexivity|]. split.
  - unfold owned,sender_request;cbn [operation descriptor buffer_block buffer_offset requested errno_block errno_offset].
    split;[lia|]. split;[change (0<=0<18446744073709551616);lia|].
    split;[change Ptrofs.modulus with 18446744073709551616;lia|].
    split;[exact EO|]. split;[exact EW|]. split;[exact ACCESS|].
    split;[left;exact NE|]. exists (firstn count bytes);split;[rewrite LENGTH;reflexivity|exact LOAD].
  - split;[rewrite LENGTH;reflexivity|exact LOAD].
Qed.
