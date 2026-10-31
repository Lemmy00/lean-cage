(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-callers.control: Finite actual source paths with branch-dependent lengths. *)
From Coq Require Import List.
From compcert Require Import Values Memory Clight.
Require Import Machine StoreSteps LibraryMachine LibraryPreservation.

Definition source_returns ge (P : mem -> Prop) (R : val -> mem -> Prop) s :=
  exists count value after, store_path ge P s count (Returnstate value Kstop after) /\ R value after.
Lemma source_returns_done : forall ge P R value m,
  P m -> R value m -> source_returns ge P R (Returnstate value Kstop m).
Proof. intros; exists 0, value, m; split; [constructor|]; assumption. Qed.
Lemma source_returns_prepend : forall ge P R s next,
  P (memory_of s) -> store_edge ge s next -> source_returns ge P R next -> source_returns ge P R s.
Proof.
  intros ge P R s next GOOD EDGE [n [value [after [PATH POST]]]].
  exists (S n), value, after; split; [econstructor; eassumption|exact POST].
Qed.
Lemma source_returns_path : forall ge P R s count next,
  store_path ge P s count next -> source_returns ge P R next -> source_returns ge P R s.
Proof.
  intros ge P R s count next PATH [n [value [after [REST POST]]]].
  exists (count+n), value, after; split; [eapply store_path_trans; eassumption|exact POST].
Qed.
Theorem source_returns_exact : forall ge cell P R s events value after,
  source_returns ge P R s ->
  library_steps ge cell (live s) events (live (Returnstate value Kstop after)) -> R value after.
Proof.
  intros ge cell P R s events value after [n [expected [final [PATH POST]]]] RUN.
  destruct (store_path_library_projection _ _ _ _ _ _ _ PATH _ _ RUN) as [old [ES OLD]].
  destruct (store_path_return_exact _ _ _ _ _ _ _ _ _ _ PATH OLD) as [VALUE [MEM _]]; subst; exact POST.
Qed.
