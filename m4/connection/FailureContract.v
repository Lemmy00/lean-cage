(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-callers.failure: Independent stable inputs for every child-failure mode. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Globalenvs Clight.
Require Import Slice Machine Library ProcessEffects Fault FreshMemoryDraft FailureSourceDraft.
Import ListNotations.
Open Scope Z_scope.

Definition error_drop_bytes := map Byte.repr [101;114;114;111;114;95;100;114;111;112].
Definition error_short_bytes := map Byte.repr [101;114;114;111;114;95;115;104;111;114;116].
Definition global_address b := {|address_block:=b; address_offset:=0|}.
Definition failure_input cell m mode mode_bytes drop short :=
  tls_ready cell m /\ mode_pointer failure_ge m mode /\ c_string m mode mode_bytes /\
  Genv.find_symbol failure_ge ___stringlit_8 = Some drop /\
  Genv.find_symbol failure_ge ___stringlit_9 = Some short /\
  c_string m (global_address drop) error_drop_bytes /\
  c_string m (global_address short) error_short_bytes.
Definition matches_mode xs ys := match compare_bytes xs ys with Eq => true | _ => false end.
Lemma fault_value_matches : forall xs ys, fault_value xs ys = Val.of_bool (matches_mode xs ys).
Proof. intros; unfold fault_value, matches_mode; destruct (compare_bytes xs ys); reflexivity. Qed.

Lemma old_mode_pointer : forall base after mode,
  old_memory base after -> mode_pointer failure_ge base mode -> mode_pointer failure_ge after mode.
Proof.
  intros base after mode OLD [mb [SYMBOL LOAD]]. exists mb; split; [exact SYMBOL|].
  change (Mem.load Mint64 after mb 0 = Some (address_value mode)).
  change (Mem.load Mint64 base mb 0 = Some (address_value mode)) in LOAD.
  eapply old_memory_load; eassumption.
Qed.

Lemma failure_input_preserved : forall cell base after mode mode_bytes drop short,
  failure_input cell base mode mode_bytes drop short -> old_memory base after ->
  failure_input cell after mode mode_bytes drop short.
Proof.
  intros cell base after mode mode_bytes drop short [TLS [MODE [BYTES [DS [SS [DROP SHORT]]]]]] OLD.
  split; [eapply old_memory_tls; eassumption|].
  split; [eapply old_mode_pointer; eassumption|].
  split; [eapply old_memory_string; eassumption|].
  split; [exact DS|]. split; [exact SS|].
  split; eapply old_memory_string; eassumption.
Qed.

Lemma failure_drop_input : forall cell m mode mode_bytes drop short,
  failure_input cell m mode mode_bytes drop short ->
  fault_input failure_ge m mode (global_address drop) mode_bytes error_drop_bytes.
Proof. intros cell m mode mode_bytes drop short [TLS [MODE [BYTES [DS [SS [DROP SHORT]]]]]]; exact (conj MODE (conj BYTES DROP)). Qed.
Lemma failure_short_input : forall cell m mode mode_bytes drop short,
  failure_input cell m mode mode_bytes drop short ->
  fault_input failure_ge m mode (global_address short) mode_bytes error_short_bytes.
Proof. intros cell m mode mode_bytes drop short [TLS [MODE [BYTES [DS [SS [DROP SHORT]]]]]]; exact (conj MODE (conj BYTES SHORT)). Qed.
