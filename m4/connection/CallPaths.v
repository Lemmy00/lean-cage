(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-callers.control: Compose actual internal reader paths into callers. *)
From Coq Require Import List Lia.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine ClightSteps Deterministic StoreSteps Readers.
Import ListNotations.

Lemma certain_source_edge : forall ge cell s next,
  certain_step ge cell s (source_step E0) next -> edge ge s next.
Proof.
  intros ge cell s next [ORD [REAL [MEM CASES]]]. inversion REAL; subst.
  split; [assumption|]. split; [assumption|]. split; [exact MEM|].
  intros t other STEP.
  assert (EXT : Machine.step ge cell (live s) (source_step t) (live other))
    by (apply internal; assumption).
  destruct (CASES _ _ EXT) as [[EV TARGET]|[EV TARGET]]; [inversion EV; inversion TARGET; subst; auto|discriminate].
Qed.

Theorem pure_execution_store_path : forall ge cell count s last P,
  execution ge cell s (repeat (source_step E0) count) last -> P (memory_of s) ->
  store_path ge P s count last.
Proof.
  intros ge cell count; induction count; intros s last P RUN GOOD; inversion RUN; subst.
  - constructor; exact GOOD.
  - eapply store_next; [exact GOOD|apply unchanged_store_edge; eapply certain_source_edge; eassumption|].
    eapply IHcount; [eassumption|].
    match goal with C : certain_step _ _ _ _ _ |- _ => destruct C as [_ [_ [MEM _]]] end.
    rewrite MEM; exact GOOD.
Qed.

Theorem reader_caller_path : forall ge (cell : Machine.tls) m b ofs f value count k P,
  reader_input m b ofs f value count -> P m ->
  store_path ge P (Readers.initial f b ofs k m) count
    (Returnstate value (call_cont k) m).
Proof.
  intros ge cell m b ofs f value count k P INPUT GOOD.
  eapply pure_execution_store_path; [apply (reader_execution ge cell); exact INPUT|exact GOOD].
Qed.

Lemma store_path_consequence : forall ge (P Q : mem -> Prop) start count last,
  store_path ge P start count last -> (forall m, P m -> Q m) ->
  store_path ge Q start count last.
Proof.
  intros ge P Q start count last PATH IMPLIES; induction PATH;
    [constructor; auto|econstructor; eauto].
Qed.

Require Import WriteBytes Writers.
Theorem writer_caller_path : forall ge m b ofs f value values count k (P : mem -> Prop),
  writer_input m b ofs f value values count -> is_call_cont k ->
  (forall after, writer_prefix m b (Integers.Ptrofs.unsigned ofs) values after -> P after) ->
  exists after, byte_writes m b (Integers.Ptrofs.unsigned ofs) values after /\
    store_path ge P (writer_initial f b ofs value k m) count (Returnstate Values.Vundef k after).
Proof.
  intros ge m b ofs f value values count k P INPUT CALL PRESERVE.
  destruct (writer_execution ge m b ofs f value values count k INPUT CALL) as [after [WRITES PATH]].
  exists after; split; [exact WRITES|]. eapply store_path_consequence; eassumption.
Qed.

Require Import LibraryMachine LibraryPreservation.
Theorem source_path_caller_prefix : forall ge cell P start count last,
  store_path ge P start count last ->
  forall events target, library_steps ge cell (live start) events target ->
  (exists n current remaining, count = (n + remaining)%nat /\
    events = map original_event (repeat (source_step E0) n) /\ target = live current /\
    store_path ge P current remaining last) \/
  (exists n m, (n < count)%nat /\
    events = map original_event (repeat (source_step E0) n) ++ [original_event loss_step] /\
    target = dead m /\ P m) \/
  (exists rest, events = map original_event (repeat (source_step E0) count) ++ rest /\
    library_steps ge cell (live last) rest target).
Proof.
  intros ge cell P start count last PATH; induction PATH as [start GOOD|start next n last GOOD EDGE TAIL IH];
    intros events target RUN.
  - right; right; exists events; cbn; auto.
  - inversion RUN; subst.
    + left; exists 0%nat, start, (S n). cbn. repeat split; auto. econstructor; eassumption.
    + pose proof EDGE as [IN _].
      match goal with STEP : library_step _ _ _ _ _ |- _ =>
        destruct (internal_boundary_unchanged _ _ _ _ _ IN STEP) as [old [EV OLD]] end.
      subst. destruct (store_edge_cases _ _ _ _ _ _ EDGE OLD) as [[EV TARGET]|[EV TARGET]]; subst.
      * match goal with REST : library_steps _ _ (live next) _ _ |- _ =>
          destruct (IH _ _ REST) as [[j [current [remaining [COUNT [ES [TARGET PATH']]]]]]|
            [[j [m [BOUND [ES [TARGET PRESERVED]]]]]|[remainder [ES AFTER]]]] end; subst.
        -- left; exists (S j), current, remaining; cbn; auto.
        -- right; left; exists (S j), m; cbn. split; [lia|auto].
        -- right; right; exists remainder; cbn; auto.
      * match goal with REST : library_steps _ _ (dead _) _ _ |- _ =>
          destruct (library_dead_steps _ _ _ _ _ REST) as [ES TARGET] end; subst.
        right; left; exists 0%nat, (memory_of start); cbn; auto with arith.
Qed.
