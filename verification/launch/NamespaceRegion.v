(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Finite namespace regions retain arbitrary waits, loss and explicit image boundaries. *)
(* Adapted from the accepted m4/validation/StringRegion.v; Apache-2.0 notice retained. *)
From Stdlib Require Import List Lia Bool.
From compcert Require Import Integers AST Values Memory Events Clight.
Require Import Machine StoreSteps LibraryMachine.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine.
Import ListNotations.
Open Scope nat_scope.

Definition namespace_event_waiting event :=
  match event with
  | NamespaceMachine.namespace_waiting | namespace_process process_waiting |
    namespace_process (process_entry entry_primitive_wait) |
    namespace_process (process_entry (entry_library library_wait)) |
    namespace_process (process_entry (entry_library (original_event wait_step))) => true
  | _ => false
  end.
Definition namespace_image event :=
  match event with namespace_process (process_entry (entry_image _ _ _)) => true | _ => false end.
Definition namespace_cost events := length (filter (fun event => negb (namespace_event_waiting event)) events).
Definition namespace_memory state := match state with live state => memory_of state | dead m => m end.
Definition namespace_no_images events := Forall (fun event => namespace_image event = false) events.

Inductive namespace_region ge cell (P : mem -> Prop) (R : Clight.state -> Prop) :
    nat -> Clight.state -> Prop :=
| namespace_region_stop : forall n state,
    P (memory_of state) -> R state -> namespace_region ge cell P R n state
| namespace_region_next : forall n state,
    P (memory_of state) ->
    (exists event next, namespace_event_waiting event = false /\ namespace_image event = false /\
      namespace_step ge cell (live state) event (live next)) ->
    (forall event target, namespace_step ge cell (live state) event target ->
      (namespace_event_waiting event = true /\ target = live state) \/
      (exists after, target = dead after /\ P after /\ namespace_image event = false) \/
      (exists next, target = live next /\ namespace_event_waiting event = false /\
        namespace_image event = false /\ namespace_region ge cell P R n next)) ->
    namespace_region ge cell P R (S n) state.

Lemma namespace_region_memory ge cell P R n state :
  namespace_region ge cell P R n state -> P (memory_of state).
Proof. intros CERT; inversion CERT; assumption. Qed.

Lemma namespace_wait_is_not_image event : namespace_event_waiting event = true -> namespace_image event = false.
Proof.
  destruct event; cbn; try discriminate; try reflexivity.
  repeat match goal with
  | event : process_event |- _ => destruct event; cbn; try discriminate; try reflexivity
  | event : entry_handoff_event |- _ => destruct event; cbn; try discriminate; try reflexivity
  | event : library_event |- _ => destruct event; cbn; try discriminate; try reflexivity
  | event : Machine.event |- _ => destruct event; cbn; try discriminate; try reflexivity
  end.
Qed.

From EntryNamespace Require Import NamespaceEffects.

Lemma namespace_errno_partial_refl cell before : entry_errno_partial cell before before.
Proof. constructor; [apply Mem.unchanged_on_refl|intros; reflexivity]. Qed.

Theorem namespace_duplicate_region ge cell P R remaining descriptor minimum k before :
  P before -> entry_errno_ready cell before ->
  (forall after, entry_errno_partial cell before after -> P after) ->
  (forall returned after, entry_errno_partial cell before after -> entry_errno_ready cell after ->
    namespace_region ge cell P R remaining (Returnstate (Vint returned) k after)) ->
  namespace_region ge cell P R (S remaining)
    (Callstate namespace_duplicate_definition [Vint descriptor;Vint minimum] k before).
Proof.
  intros GOOD ERRNO PARTIAL RETURN; eapply namespace_region_next; [exact GOOD| |].
  - exists (namespace_duplicated descriptor minimum Int.mone),(Returnstate (Vint Int.mone) k before).
    split; [reflexivity|]. split; [reflexivity|].
    apply namespace_duplicate_step; [apply namespace_errno_partial_refl|exact ERRNO].
  - intros event target STEP; destruct (namespace_duplicate_cases _ _ _ _ _ _ _ _ STEP)
      as [[returned [after [FRAME [READY [EVENT TARGET]]]]]|
        [[EVENT TARGET]|[[after [FRAME [EVENT TARGET]]]|[EVENT TARGET]]]]; subst.
    + right; right; exists (Returnstate (Vint returned) k after).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|apply RETURN; assumption].
    + left; auto.
    + right; left; exists after; split; [reflexivity|]. split; [apply PARTIAL; exact FRAME|reflexivity].
    + right; left; exists before; auto.
Qed.

Theorem namespace_mask_region ge cell P R remaining mask k before :
  P before -> entry_errno_ready cell before ->
  (forall after, entry_errno_partial cell before after -> P after) ->
  (forall returned after, entry_errno_partial cell before after -> entry_errno_ready cell after ->
    namespace_region ge cell P R remaining (Returnstate (Vlong returned) k after)) ->
  namespace_region ge cell P R (S remaining) (Callstate namespace_mask_definition [Vlong mask] k before).
Proof.
  intros GOOD ERRNO PARTIAL RETURN; eapply namespace_region_next; [exact GOOD| |].
  - exists (namespace_masked mask Int64.mone),(Returnstate (Vlong Int64.mone) k before).
    split; [reflexivity|]. split; [reflexivity|].
    apply namespace_mask_step; [apply namespace_errno_partial_refl|exact ERRNO].
  - intros event target STEP; destruct (namespace_mask_cases _ _ _ _ _ _ _ STEP)
      as [[returned [after [FRAME [READY [EVENT TARGET]]]]]|
        [[EVENT TARGET]|[[after [FRAME [EVENT TARGET]]]|[EVENT TARGET]]]]; subst.
    + right; right; exists (Returnstate (Vlong returned) k after).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|apply RETURN; assumption].
    + left; auto.
    + right; left; exists after; split; [reflexivity|]. split; [apply PARTIAL; exact FRAME|reflexivity].
    + right; left; exists before; auto.
Qed.

Theorem namespace_fork_region ge cell P R remaining k before :
  P before -> entry_errno_ready cell before ->
  (forall after, entry_errno_partial cell before after -> P after) ->
  (forall returned after, entry_errno_partial cell before after -> entry_errno_ready cell after ->
    namespace_region ge cell P R remaining (Returnstate (Vint returned) k after)) ->
  namespace_region ge cell P R (S remaining) (Callstate namespace_fork_definition [] k before).
Proof.
  intros GOOD ERRNO PARTIAL RETURN; eapply namespace_region_next; [exact GOOD| |].
  - exists (namespace_forked Int.mone),(Returnstate (Vint Int.mone) k before).
    split; [reflexivity|]. split; [reflexivity|].
    apply namespace_fork_step; [apply namespace_errno_partial_refl|exact ERRNO].
  - intros event target STEP; destruct (namespace_fork_cases _ _ _ _ _ _ STEP)
      as [[returned [after [FRAME [READY [EVENT TARGET]]]]]|
        [[EVENT TARGET]|[[after [FRAME [EVENT TARGET]]]|[EVENT TARGET]]]]; subst.
    + right; right; exists (Returnstate (Vint returned) k after).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|apply RETURN; assumption].
    + left; auto.
    + right; left; exists after; split; [reflexivity|]. split; [apply PARTIAL; exact FRAME|reflexivity].
    + right; left; exists before; auto.
Qed.

Theorem namespace_pair_region ge cell P R remaining domain kind protocol output offset k before :
  P before -> namespace_pair_owned before output offset -> entry_errno_ready cell before ->
  (forall after, namespace_pair_partial cell output offset before after -> P after) ->
  (forall returned first second after,
    namespace_pair_effect cell output offset before returned first second after -> entry_errno_ready cell after ->
    namespace_region ge cell P R remaining (Returnstate (Vint returned) k after)) ->
  namespace_region ge cell P R (S remaining)
    (Callstate namespace_pair_definition [Vint domain;Vint kind;Vint protocol;Vptr output offset] k before).
Proof.
  intros GOOD OWN ERRNO PARTIAL RETURN; eapply namespace_region_next; [exact GOOD| |].
  - exists (namespace_paired domain kind protocol output offset Int.mone Int.zero Int.zero),
      (Returnstate (Vint Int.mone) k before).
    split; [reflexivity|]. split; [reflexivity|].
    apply namespace_pair_step; [exact OWN| |exact ERRNO].
    apply namespace_pair_failed; [discriminate|apply namespace_errno_partial_refl].
  - intros event target STEP; destruct (namespace_pair_cases _ _ _ _ _ _ _ _ _ _ _ STEP)
      as [[returned [first [second [after [OWNED [FRAME [READY [EVENT TARGET]]]]]]]]|
        [[EVENT TARGET]|[[after [FRAME [EVENT TARGET]]]|[EVENT TARGET]]]]; subst.
    + right; right; exists (Returnstate (Vint returned) k after).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|eapply RETURN; eassumption].
    + left; auto.
    + right; left; exists after; split; [reflexivity|]. split; [apply PARTIAL; exact FRAME|reflexivity].
    + right; left; exists before; auto.
Qed.

Lemma namespace_region_weaken ge cell P R n state : namespace_region ge cell P R n state ->
  forall larger, n <= larger -> namespace_region ge cell P R larger state.
Proof.
  revert state; induction n as [|n IH]; intros state CERT larger BOUND.
  - inversion CERT; subst; constructor; assumption.
  - inversion CERT as [count current GOOD RESULT|count current GOOD PROGRESS CASES]; subst.
    + constructor; assumption.
    + destruct larger; [lia|]; eapply namespace_region_next; [exact GOOD|exact PROGRESS|].
      intros event target STEP; destruct (CASES _ _ STEP)
        as [WAIT|[DEAD|[next [TARGET [ADV [IMAGE TAIL]]]]]]; auto.
      right; right; exists next; repeat split; try assumption.
      apply IH with (state:=next); [exact TAIL|lia].
Qed.

Theorem namespace_region_execution_split ge cell P R n start :
  namespace_region ge cell P R n start ->
  forall events target, namespace_steps ge cell (live start) events target ->
  (P (namespace_memory target) /\ namespace_cost events <= S n /\ namespace_no_images events /\
    (forall state, target = live state -> exists remaining, namespace_region ge cell P R remaining state)) \/
  (exists prefix endpoint rest, events = prefix ++ rest /\ namespace_cost prefix <= n /\
    namespace_no_images prefix /\ namespace_steps ge cell (live start) prefix (live endpoint) /\
    P (memory_of endpoint) /\ R endpoint /\ namespace_steps ge cell (live endpoint) rest target).
Proof.
  intros CERT events target RUN; remember (live start) as initial eqn:INITIAL.
  revert start n INITIAL CERT.
  induction RUN as [initial|initial event middle events target STEP RUN IH];
    intros start n INITIAL CERT; subst initial.
  - left; split; [exact (namespace_region_memory _ _ _ _ _ _ CERT)|].
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
           ++ unfold namespace_cost; cbn; rewrite WAIT; exact BOUND.
           ++ split; [constructor; [apply namespace_wait_is_not_image; exact WAIT|exact IMAGES]|exact LIVE].
        -- right; exists (event::prefix), endpoint, rest; subst events; split; [reflexivity|].
           split; [unfold namespace_cost; cbn; rewrite WAIT; exact COST|].
           split; [constructor; [apply namespace_wait_is_not_image; exact WAIT|exact IMAGES]|].
           split; [econstructor; eassumption|auto].
      * destruct (NamespaceMachine.namespace_dead_steps _ _ _ _ _ RUN) as [EVENTS TARGET]; subst.
        left; split; [exact PRESERVED|]; split.
        -- unfold namespace_cost; cbn; destruct (namespace_event_waiting event); cbn; lia.
        -- split; [constructor; [exact IMAGE|constructor]|intros; discriminate].
      * destruct (IH _ _ eq_refl TAIL)
          as [[MEM [BOUND [IMAGES LIVE]]]|[prefix [endpoint [rest [EVENTS [COST [IMAGES [PRE [MEM [RESULT POST]]]]]]]]]].
        -- left; split; [exact MEM|]; split.
           ++ unfold namespace_cost; cbn; rewrite ADV; cbn; unfold namespace_cost in BOUND; lia.
           ++ split; [constructor; assumption|exact LIVE].
        -- right; exists (event::prefix), endpoint, rest; subst events; split; [reflexivity|].
           split; [unfold namespace_cost; cbn; rewrite ADV; cbn; unfold namespace_cost in COST; lia|].
           split; [constructor; assumption|].
           split; [econstructor; eassumption|auto].
Qed.

Theorem namespace_region_image_requires_leaf ge cell P R n start events target path arguments environment :
  namespace_region ge cell P R n start ->
  namespace_steps ge cell (live start) events target ->
  In (namespace_process (process_entry (entry_image path arguments environment))) events ->
  exists prefix endpoint rest, events = prefix ++ rest /\ namespace_no_images prefix /\
    namespace_steps ge cell (live start) prefix (live endpoint) /\
    P (memory_of endpoint) /\ R endpoint /\ namespace_steps ge cell (live endpoint) rest target.
Proof.
  intros CERT RUN IMAGE.
  destruct (namespace_region_execution_split _ _ _ _ _ _ CERT _ _ RUN)
    as [[MEM [COST [IMAGES LIVE]]]|[prefix [endpoint [rest [EVENTS [COST REST]]]]]].
  - unfold namespace_no_images in IMAGES; rewrite Forall_forall in IMAGES.
    specialize (IMAGES _ IMAGE); discriminate.
  - exists prefix, endpoint, rest; auto.
Qed.

Lemma namespace_region_source_prepend ge cell P R state next n :
  P (memory_of state) -> store_edge ge state next -> namespace_region ge cell P R n next ->
  namespace_region ge cell P R (S n) state.
Proof.
  intros GOOD EDGE CERT; eapply namespace_region_next; [exact GOOD| |].
  - exists (namespace_process (process_entry (entry_library (original_event (source_step E0))))), next.
    split; [reflexivity|]; split; [reflexivity|].
    apply namespace_process_step,process_entry_step,entry_library_step,original_step.
    destruct EDGE as [IN [REAL _]]; apply internal; assumption.
  - intros event target STEP.
    destruct (namespace_store_edge_cases _ _ _ _ _ _ EDGE STEP) as [[EVENT TARGET]|[EVENT TARGET]]; subst.
    + right; right; exists next; auto.
    + right; left; exists (memory_of state); auto.
Qed.

Lemma namespace_region_store_path ge cell P R start count last remaining :
  store_path ge P start count last -> namespace_region ge cell P R remaining last ->
  namespace_region ge cell P R (count + remaining) start.
Proof.
  intros PATH CERT; induction PATH; cbn; auto; eapply namespace_region_source_prepend; eauto.
Qed.

Lemma namespace_region_bind ge cell P R Q n start extra :
  namespace_region ge cell P R n start ->
  (forall endpoint, R endpoint -> namespace_region ge cell P Q extra endpoint) ->
  namespace_region ge cell P Q (n + extra) start.
Proof.
  revert start; induction n as [|n IH]; intros start CERT NEXT;
    inversion CERT as [count current GOOD RESULT|count current GOOD PROGRESS CASES]; subst; cbn.
  - apply NEXT; exact RESULT.
  - apply namespace_region_weaken with (n:=extra); [apply NEXT; exact RESULT|lia].
  - eapply namespace_region_next; [exact GOOD|exact PROGRESS|].
    intros event target STEP; destruct (CASES _ _ STEP) as [WAIT|[DEAD|[next [TARGET [ADV [IMAGE TAIL]]]]]]; auto.
    right; right; exists next; repeat split; try assumption; apply IH; assumption.
Qed.

Theorem namespace_region_actual ge cell P R n start : namespace_region ge cell P R n start ->
  exists events endpoint, namespace_steps ge cell (live start) events (live endpoint) /\
    namespace_cost events <= n /\ namespace_no_images events /\ P (memory_of endpoint) /\ R endpoint.
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
    split; [unfold namespace_cost in *; cbn; rewrite ADV; cbn; lia|].
    split; [constructor; assumption|auto].
Qed.
