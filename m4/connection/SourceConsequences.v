(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.source: Preserve actual source paths while composing postconditions. *)
From compcert Require Import Values Memory Clight.
Require Import StoreSteps CallPaths SourcePaths SourceReach.
Lemma source_reaches_consequence : forall ge (P Q : mem -> Prop) A B s,
  source_reaches ge P A s -> (forall m, P m -> Q m) -> (forall last, A last -> B last) ->
  source_reaches ge Q B s.
Proof.
  intros ge P Q A B s [n [last [PATH POST]]] MEMORY RESULT.
  exists n,last;split; [eapply store_path_consequence; eassumption|auto].
Qed.
Lemma source_returns_consequence : forall ge (P Q : mem -> Prop) A B s,
  source_returns ge P A s -> (forall m, P m -> Q m) ->
  (forall value after, A value after -> B value after) -> source_returns ge Q B s.
Proof.
  intros ge P Q A B s [n [value [after [PATH POST]]]] MEMORY RESULT.
  exists n,value,after;split; [eapply store_path_consequence; eassumption|auto].
Qed.
