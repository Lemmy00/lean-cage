(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Finite source regions retain image replacement as an explicit boundary. *)
(* Adapted from the accepted m4/validation/StringRegion.v; Apache-2.0 notice retained. *)
From Stdlib Require Import List Lia Bool.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine StoreSteps LibraryMachine.
From EntryNative Require Import NativeHandoffMachine.
Import ListNotations.
Open Scope nat_scope.

Definition handoff_waiting event :=
  match event with
  | entry_primitive_wait | entry_library library_wait | entry_library (original_event wait_step) => true
  | _ => false
  end.
Definition handoff_image event :=
  match event with entry_image _ _ _ => true | _ => false end.
Definition handoff_cost events := length (filter (fun event => negb (handoff_waiting event)) events).
Definition handoff_memory state := match state with live state => memory_of state | dead m => m end.
Definition handoff_no_images events := Forall (fun event => handoff_image event = false) events.

Inductive handoff_region ge cell (P : mem -> Prop) (R : Clight.state -> Prop) :
    nat -> Clight.state -> Prop :=
| handoff_region_stop : forall n state,
    P (memory_of state) -> R state -> handoff_region ge cell P R n state
| handoff_region_next : forall n state,
    P (memory_of state) ->
    (exists event next, handoff_waiting event = false /\ handoff_image event = false /\
      entry_handoff_step ge cell (live state) event (live next)) ->
    (forall event target, entry_handoff_step ge cell (live state) event target ->
      (handoff_waiting event = true /\ target = live state) \/
      (exists after, target = dead after /\ P after /\ handoff_image event = false) \/
      (exists next, target = live next /\ handoff_waiting event = false /\
        handoff_image event = false /\ handoff_region ge cell P R n next)) ->
    handoff_region ge cell P R (S n) state.

Lemma handoff_region_memory ge cell P R n state :
  handoff_region ge cell P R n state -> P (memory_of state).
Proof. intros CERT; inversion CERT; assumption. Qed.

Lemma handoff_wait_is_not_image event : handoff_waiting event = true -> handoff_image event = false.
Proof.
  destruct event; cbn; try discriminate; try reflexivity.
Qed.

Lemma handoff_region_weaken ge cell P R n state : handoff_region ge cell P R n state ->
  forall larger, n <= larger -> handoff_region ge cell P R larger state.
Proof.
  revert state; induction n as [|n IH]; intros state CERT larger BOUND.
  - inversion CERT; subst; constructor; assumption.
  - inversion CERT as [count current GOOD RESULT|count current GOOD PROGRESS CASES]; subst.
    + constructor; assumption.
    + destruct larger; [lia|]; eapply handoff_region_next; [exact GOOD|exact PROGRESS|].
      intros event target STEP; destruct (CASES _ _ STEP)
        as [WAIT|[DEAD|[next [TARGET [ADV [IMAGE TAIL]]]]]]; auto.
      right; right; exists next; repeat split; try assumption.
      apply IH with (state:=next); [exact TAIL|lia].
Qed.

Theorem handoff_region_execution_split ge cell P R n start :
  handoff_region ge cell P R n start ->
  forall events target, entry_handoff_steps ge cell (live start) events target ->
  (P (handoff_memory target) /\ handoff_cost events <= S n /\ handoff_no_images events /\
    (forall state, target = live state -> exists remaining, handoff_region ge cell P R remaining state)) \/
  (exists prefix endpoint rest, events = prefix ++ rest /\ handoff_cost prefix <= n /\
    handoff_no_images prefix /\ entry_handoff_steps ge cell (live start) prefix (live endpoint) /\
    P (memory_of endpoint) /\ R endpoint /\ entry_handoff_steps ge cell (live endpoint) rest target).
Proof.
  intros CERT events target RUN; remember (live start) as initial eqn:INITIAL.
  revert start n INITIAL CERT.
  induction RUN as [initial|initial event middle events target STEP RUN IH];
    intros start n INITIAL CERT; subst initial.
  - left; split; [exact (handoff_region_memory _ _ _ _ _ _ CERT)|].
    split; [cbn; lia|]; split; [constructor|].
    intros state SAME; inversion SAME; subst; eauto.
  - inversion CERT as [count current GOOD RESULT|count current GOOD PROGRESS CASES]; subst.
    + right; exists [], start, (event::events); split; [reflexivity|].
      split; [cbn; lia|]; split; [constructor|].
      split; [constructor|]; split; [exact GOOD|]; split; [exact RESULT|econstructor; eassumption].
    + destruct (CASES _ _ STEP) as [[WAIT TARGET]|[[after [TARGET [PRESERVED IMAGE]]]|
        [next [TARGET [ADV [IMAGE TAIL]]]]]]; subst middle.
      * destruct (IH _ _ eq_refl CERT)
          as [[MEM [BOUND [IMAGES LIVE]]]|[prefix [endpoint [rest [EVENTS [COST [IMAGES [PRE [MEM [RESULT POST]]]]]]]]]].
        -- left; split; [exact MEM|]; split.
           ++ unfold handoff_cost; cbn; rewrite WAIT; exact BOUND.
           ++ split; [constructor; [apply handoff_wait_is_not_image; exact WAIT|exact IMAGES]|exact LIVE].
        -- right; exists (event::prefix), endpoint, rest; subst events; split; [reflexivity|].
           split; [unfold handoff_cost; cbn; rewrite WAIT; exact COST|].
           split; [constructor; [apply handoff_wait_is_not_image; exact WAIT|exact IMAGES]|].
           split; [econstructor; eassumption|auto].
      * destruct (entry_handoff_dead_steps _ _ _ _ _ RUN) as [EVENTS TARGET]; subst.
        left; split; [exact PRESERVED|]; split.
        -- unfold handoff_cost; cbn; destruct (handoff_waiting event); cbn; lia.
        -- split; [constructor; [exact IMAGE|constructor]|intros; discriminate].
      * destruct (IH _ _ eq_refl TAIL)
          as [[MEM [BOUND [IMAGES LIVE]]]|[prefix [endpoint [rest [EVENTS [COST [IMAGES [PRE [MEM [RESULT POST]]]]]]]]]].
        -- left; split; [exact MEM|]; split.
           ++ unfold handoff_cost; cbn; rewrite ADV; cbn; unfold handoff_cost in BOUND; lia.
           ++ split; [constructor; assumption|exact LIVE].
        -- right; exists (event::prefix), endpoint, rest; subst events; split; [reflexivity|].
           split; [unfold handoff_cost; cbn; rewrite ADV; cbn; unfold handoff_cost in COST; lia|].
           split; [constructor; assumption|].
           split; [econstructor; eassumption|auto].
Qed.

Theorem handoff_region_image_requires_leaf ge cell P R n start events target path arguments environment :
  handoff_region ge cell P R n start ->
  entry_handoff_steps ge cell (live start) events target ->
  In (entry_image path arguments environment) events ->
  exists prefix endpoint rest, events = prefix ++ rest /\ handoff_no_images prefix /\
    entry_handoff_steps ge cell (live start) prefix (live endpoint) /\
    P (memory_of endpoint) /\ R endpoint /\ entry_handoff_steps ge cell (live endpoint) rest target.
Proof.
  intros CERT RUN IMAGE.
  destruct (handoff_region_execution_split _ _ _ _ _ _ CERT _ _ RUN)
    as [[MEM [COST [IMAGES LIVE]]]|[prefix [endpoint [rest [EVENTS [COST REST]]]]]].
  - unfold handoff_no_images in IMAGES; rewrite Forall_forall in IMAGES.
    specialize (IMAGES _ IMAGE); discriminate.
  - exists prefix, endpoint, rest; auto.
Qed.

Lemma handoff_region_source_prepend ge cell P R state next n :
  P (memory_of state) -> store_edge ge state next -> handoff_region ge cell P R n next ->
  handoff_region ge cell P R (S n) state.
Proof.
  intros GOOD EDGE CERT; eapply handoff_region_next; [exact GOOD| |].
  - exists (entry_library (original_event (source_step E0))), next.
    split; [reflexivity|]; split; [reflexivity|].
    apply entry_library_step; apply original_step.
    destruct EDGE as [IN [REAL _]]; apply internal; assumption.
  - intros event target STEP.
    destruct (entry_store_edge_cases _ _ _ _ _ _ EDGE STEP) as [[EVENT TARGET]|[EVENT TARGET]]; subst.
    + right; right; exists next; auto.
    + right; left; exists (memory_of state); auto.
Qed.

Lemma handoff_region_store_path ge cell P R start count last remaining :
  store_path ge P start count last -> handoff_region ge cell P R remaining last ->
  handoff_region ge cell P R (count + remaining) start.
Proof.
  intros PATH CERT; induction PATH; cbn; auto; eapply handoff_region_source_prepend; eauto.
Qed.

Lemma handoff_region_bind ge cell P R Q n start extra :
  handoff_region ge cell P R n start ->
  (forall endpoint, R endpoint -> handoff_region ge cell P Q extra endpoint) ->
  handoff_region ge cell P Q (n + extra) start.
Proof.
  revert start; induction n as [|n IH]; intros start CERT NEXT;
    inversion CERT as [count current GOOD RESULT|count current GOOD PROGRESS CASES]; subst; cbn.
  - apply NEXT; exact RESULT.
  - apply handoff_region_weaken with (n:=extra); [apply NEXT; exact RESULT|lia].
  - eapply handoff_region_next; [exact GOOD|exact PROGRESS|].
    intros event target STEP; destruct (CASES _ _ STEP) as [WAIT|[DEAD|[next [TARGET [ADV [IMAGE TAIL]]]]]]; auto.
    right; right; exists next; repeat split; try assumption; apply IH; assumption.
Qed.

Theorem handoff_region_actual ge cell P R n start : handoff_region ge cell P R n start ->
  exists events endpoint, entry_handoff_steps ge cell (live start) events (live endpoint) /\
    handoff_cost events <= n /\ handoff_no_images events /\ P (memory_of endpoint) /\ R endpoint.
Proof.
  revert start; induction n as [|n IH]; intros start CERT;
    inversion CERT as [count current GOOD RESULT|count current GOOD PROGRESS CASES]; subst.
  - exists [], start; split; [constructor|]; split; [cbn; lia|].
    split; [constructor|auto].
  - exists [], start; split; [constructor|]; split; [cbn; lia|].
    split; [constructor|auto].
  - destruct PROGRESS as [event [next [ADV [IMAGE STEP]]]].
    destruct (CASES _ _ STEP) as [[WAIT SAME]|[[after [SAME MEM]]|[state [SAME [ORD [NOIMAGE TAIL]]]]]];
      try congruence; try discriminate.
    inversion SAME; subst state.
    destruct (IH _ TAIL) as [events [endpoint [RUN [COST [IMAGES [MEM RESULT]]]]]].
    exists (event::events), endpoint; split; [econstructor; eassumption|].
    split; [unfold handoff_cost in *; cbn; rewrite ADV; cbn; lia|].
    split; [constructor; assumption|auto].
Qed.
