(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.source: Finite source branches with explicit boundary postconditions. *)
From Coq Require Import List.
From compcert Require Import Values Memory Clight.
Require Import Machine StoreSteps SourcePaths.
Definition source_reaches ge (P : mem -> Prop) (Q : Clight.state -> Prop) s :=
  exists count last, store_path ge P s count last /\ Q last.
Lemma source_reaches_done : forall ge P Q s,
  P (memory_of s) -> Q s -> source_reaches ge P Q s.
Proof. intros; exists 0,s; split; [constructor|]; assumption. Qed.
Lemma source_reaches_prepend : forall ge P Q s next,
  P (memory_of s) -> store_edge ge s next -> source_reaches ge P Q next -> source_reaches ge P Q s.
Proof.
  intros ge P Q s next GOOD EDGE [n [last [PATH POST]]].
  exists (S n),last; split; [econstructor; eassumption|exact POST].
Qed.
Lemma source_reaches_path : forall ge P Q s n next,
  store_path ge P s n next -> source_reaches ge P Q next -> source_reaches ge P Q s.
Proof.
  intros ge P Q s n next PATH [count [last [REST POST]]].
  exists (n+count),last; split; [eapply store_path_trans; eassumption|exact POST].
Qed.
Theorem source_reaches_returns : forall ge P Q R s,
  source_reaches ge P Q s -> (forall last, Q last -> source_returns ge P R last) ->
  source_returns ge P R s.
Proof.
  intros ge P Q R s [n [last [PATH POST]]] RETURN.
  eapply source_returns_path; [exact PATH|apply RETURN; exact POST].
Qed.
