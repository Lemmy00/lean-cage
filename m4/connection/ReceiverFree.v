(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.memory: All seven actual receiver locals are freed in environment order. *)
From Coq Require Import ZArith List Lia Sorting.Permutation.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Slice Machine StoreSteps LocalAccess CallAccess ResultLayout ReceiverSource
  ReceiverAllocation ReceiverPreparation.
Import ListNotations.
Open Scope Z_scope.
Definition local_free_blocks(objects : list(block*Z)):=map(fun obj=>(fst obj,0,snd obj))objects.
Definition receiver_free_objects b :=
  [(rb_setup b,144);(rb_signal b,144);(rb_unknown b,144);(rb_exit b,144);
   (rb_pipe b,4);(rb_result b,144);(rb_bytes b,9)].
Lemma receiver_environment_blocks : forall b,
  blocks_of_env result_ge(receiver_env b)=local_free_blocks(receiver_free_objects b).
Proof. intros;reflexivity. Qed.
Lemma receiver_free_permutation : forall b,Permutation(receiver_free_objects b)(receiver_objects b).
Proof.
  intros b;unfold receiver_free_objects,receiver_objects.
  apply(@Permutation_cons_app (block*Z) _ [(rb_pipe b,4);(rb_result b,144);(rb_bytes b,9);(rb_unknown b,144);(rb_signal b,144);(rb_exit b,144)][] _).
  cbn;apply(@Permutation_cons_app (block*Z) _ [(rb_pipe b,4);(rb_result b,144);(rb_bytes b,9);(rb_unknown b,144)][(rb_exit b,144)] _).
  cbn;apply(@Permutation_cons_app (block*Z) _ [(rb_pipe b,4);(rb_result b,144);(rb_bytes b,9)][(rb_exit b,144)] _).
  cbn;apply(@Permutation_cons_app (block*Z) _ [(rb_pipe b,4);(rb_result b,144);(rb_bytes b,9)][] _).
  apply Permutation_refl.
Qed.
Theorem local_frees_exist : forall base m objects,
  NoDup(map fst objects) ->
  Forall(fun obj=>~Mem.valid_block base(fst obj) /\ Mem.range_perm m(fst obj)0(snd obj)Cur Freeable)objects ->
  exists after,Mem.free_list m(local_free_blocks objects)=Some after /\
    Mem.unchanged_on(fun b _=>Mem.valid_block base b)m after.
Proof.
  intros base m objects;revert m;induction objects as[|[local size]rest IH];intros m DISTINCT OWN.
  - exists m;split;[reflexivity|apply Mem.unchanged_on_refl].
  - inversion DISTINCT as[|? ? NOTIN NODUP];subst.
    inversion OWN as[|? ? [FRESH PERMS] REST];subst;cbn in *.
    destruct(Mem.range_perm_free _ _ _ _ PERMS)as[mid FREE].
    assert(REST' : Forall(fun obj=>~Mem.valid_block base(fst obj) /\
      Mem.range_perm mid(fst obj)0(snd obj)Cur Freeable)rest).
    { rewrite Forall_forall in *;intros [other limit]IN;destruct(REST _ IN)as[FR RP];split;[exact FR|].
      intros pos RANGE;eapply Mem.perm_free_1;[exact FREE| |apply RP;exact RANGE].
      left;cbn;intro EQ;subst other;apply NOTIN;apply in_map_iff;exists(local,limit);auto. }
    destruct(IH mid NODUP REST')as[after[TAIL KEEP]].
    exists after;split.
    + cbn [local_free_blocks map Mem.free_list fst snd];rewrite FREE;exact TAIL.
    + eapply Mem.unchanged_on_trans;[|exact KEEP].
      eapply Mem.free_unchanged_on;[exact FREE|]. intros pos RANGE VALID;contradiction.
Qed.
Theorem receiver_free_exists : forall base b m,
  receiver_slots_owned base b m ->
  exists after,Mem.free_list m(blocks_of_env result_ge(receiver_env b))=Some after /\
    Mem.unchanged_on(fun local _=>Mem.valid_block base local)m after.
Proof.
  intros base b m [DISTINCT OWN];rewrite receiver_environment_blocks.
  apply(local_frees_exist base m).
  - eapply Permutation_NoDup;[apply Permutation_map;symmetry;apply receiver_free_permutation|exact DISTINCT].
  - eapply Permutation_Forall;[symmetry;apply receiver_free_permutation|exact OWN].
Qed.
Theorem receiver_source_free : forall b k le m after,
  Mem.free_list m(blocks_of_env result_ge(receiver_env b))=Some after ->
  store_edge result_ge(State f_m4_collect_failure(Sreturn None)k(receiver_env b)le m)
    (Returnstate Vundef(call_cont k)after).
Proof. intros;apply local_void_return_edge;exact H. Qed.
Definition receiver_freed b after := forall local size,
  In(local,size)(receiver_objects b) ->
  forall pos pk permission,0<=pos<size -> ~Mem.perm after local pos pk permission.
Theorem receiver_free_permissions : forall b m after,
  Mem.free_list m(blocks_of_env result_ge(receiver_env b))=Some after -> receiver_freed b after.
Proof.
  intros b m after FREE local size IN pos pk permission RANGE PERM.
  destruct(Mem.perm_free_list _ _ _ _ _ _ _ FREE PERM)as[_ ABSURD].
  apply(ABSURD 0 size);[|exact RANGE]. rewrite receiver_environment_blocks.
  unfold local_free_blocks;apply in_map_iff;exists(local,size);split;[reflexivity|].
  eapply Permutation_in;[symmetry;apply receiver_free_permutation|exact IN].
Qed.
