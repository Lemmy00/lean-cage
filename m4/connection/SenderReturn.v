(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.memory: Every source return frees both actual local allocations. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Slice Machine StoreSteps LocalAccess CallAccess ResultLayout SenderSource SenderReportMemory.
Import ListNotations.
Open Scope Z_scope.
Lemma sender_environment_blocks : forall result_local bytes_local,
  blocks_of_env result_ge (sender_env result_local bytes_local)=
    [(bytes_local,0,160);(result_local,0,144)].
Proof. intros;reflexivity. Qed.
Lemma sender_local_free_preserved : forall cell base before after local lo hi,
  ~Mem.valid_block base local -> sender_preserved cell base before ->
  Mem.free before local lo hi=Some after -> sender_preserved cell base after.
Proof.
  intros cell base before after local lo hi FRESH OLD FREE.
  eapply Mem.unchanged_on_trans;[exact OLD|]. eapply Mem.free_unchanged_on;[exact FREE|].
  intros pos RANGE [VALID OUTSIDE];contradiction.
Qed.
Definition sender_freed base result_local bytes_local after :=
  ~Mem.valid_block base result_local /\ ~Mem.valid_block base bytes_local /\
  exists before middle,Mem.free before bytes_local 0 160=Some middle /\
    Mem.free middle result_local 0 144=Some after.
Theorem sender_free_exists : forall cell base m result_local bytes_local,
  ~Mem.valid_block base result_local -> ~Mem.valid_block base bytes_local -> result_local<>bytes_local ->
  sender_preserved cell base m -> Mem.range_perm m result_local 0 144 Cur Freeable ->
  Mem.range_perm m bytes_local 0 160 Cur Freeable ->
  exists after,Mem.free_list m (blocks_of_env result_ge (sender_env result_local bytes_local))=Some after /\
    sender_preserved cell base after /\ sender_freed base result_local bytes_local after.
Proof.
  intros cell base m result_local bytes_local FR FB NE OLD RFREE BFREE.
  destruct (Mem.range_perm_free _ _ _ _ BFREE) as [middle FREEB].
  assert (RR : Mem.range_perm middle result_local 0 144 Cur Freeable).
  { intros pos RANGE;eapply Mem.perm_free_1;[exact FREEB|left;exact NE|apply RFREE;exact RANGE]. }
  destruct (Mem.range_perm_free _ _ _ _ RR) as [after FREER].
  exists after;split.
  - rewrite sender_environment_blocks;cbn [Mem.free_list];rewrite FREEB,FREER;reflexivity.
  - split.
    + eapply sender_local_free_preserved;[exact FR| |exact FREER].
      eapply sender_local_free_preserved;[exact FB|exact OLD|exact FREEB].
    + split;[exact FR|]. split;[exact FB|]. exists m,middle;auto.
Qed.
Theorem sender_source_return : forall a k le m result_local bytes_local v w after,
  expression_value result_ge (sender_env result_local bytes_local) le m a v ->
  sem_cast v (typeof a) tint m=Some w ->
  Mem.free_list m (blocks_of_env result_ge (sender_env result_local bytes_local))=Some after ->
  store_edge result_ge (State f_send_frame (Sreturn (Some a)) k (sender_env result_local bytes_local) le m)
    (Returnstate w (call_cont k) after).
Proof. intros;eapply certified_local_return_edge;[exact H|exact H0|exact H1]. Qed.
Theorem sender_freed_permissions : forall base result_local bytes_local after,
  sender_freed base result_local bytes_local after ->
  (forall pos kind permission,0<=pos<144 -> ~Mem.perm after result_local pos kind permission) /\
  (forall pos kind permission,0<=pos<160 -> ~Mem.perm after bytes_local pos kind permission).
Proof.
  intros base result_local bytes_local after [_ [_ [before [middle [FREEB FREER]]]]];split;intros pos kind permission BOUND.
  - eapply Mem.perm_free_2;[exact FREER|exact BOUND].
  - intros PERM. apply (Mem.perm_free_2 _ _ _ _ _ FREEB pos kind permission BOUND).
    eapply Mem.perm_free_3;[exact FREER|exact PERM].
Qed.
