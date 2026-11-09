(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Retain each actual descriptor/process event through finite source regions. *)
From Stdlib Require Import List Lia Bool.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine StoreSteps LibraryMachine.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine NamespaceRegion.
Import ListNotations.
Open Scope nat_scope.

Definition namespace_fd_event event :=
  match event with
  | namespace_paired _ _ _ _ _ _ _ _ | namespace_duplicated _ _ _ |
    namespace_masked _ _ | namespace_defaulted _ _ | namespace_forked _ |
    namespace_pair_lost _ _ _ _ _ | namespace_duplicate_lost _ _ | namespace_mask_lost _ |
    namespace_default_lost _ | namespace_fork_lost |
    namespace_process (process_waited _ _ _ _ _) | namespace_process (process_traced _ _ _ _ _) |
    namespace_process (process_entry (entry_library (original_event (io_step _ _)))) |
    namespace_process (process_entry (entry_library (close_returned _ _))) |
    namespace_process (process_entry (entry_flags_returned _ _ _)) |
    namespace_process (process_entry (entry_flags_lost _ _)) |
    namespace_process (process_entry (entry_library (exit_requested _))) |
    namespace_process (process_entry (entry_image _ _ _)) => true
  | _ => false
  end.
Definition namespace_fd_events := filter namespace_fd_event.
Definition namespace_advance log event :=
  if namespace_fd_event event then log++[event] else log.

Lemma namespace_advance_cons log event rest :
  namespace_advance log event ++ namespace_fd_events rest =
    log ++ namespace_fd_events (event::rest).
Proof.
  unfold namespace_advance,namespace_fd_events; cbn; destruct (namespace_fd_event event);
    [rewrite <- app_assoc; reflexivity|reflexivity].
Qed.

Lemma namespace_wait_has_no_fd event : namespace_event_waiting event = true -> namespace_fd_event event = false.
Proof.
  destruct event; cbn; try discriminate; try reflexivity.
  repeat match goal with
  | event : process_event |- _ => destruct event; cbn; try discriminate; try reflexivity
  | event : entry_handoff_event |- _ => destruct event; cbn; try discriminate; try reflexivity
  | event : library_event |- _ => destruct event; cbn; try discriminate; try reflexivity
  | event : Machine.event |- _ => destruct event; cbn; try discriminate; try reflexivity
  end.
Qed.

Inductive namespace_trace_region ge cell (R : list namespace_event -> Clight.state -> Prop) :
    nat -> list namespace_event -> Clight.state -> Prop :=
| namespace_trace_stop : forall n log state,
    R log state -> namespace_trace_region ge cell R n log state
| namespace_trace_next : forall n log state,
    (exists event next, namespace_event_waiting event = false /\ namespace_image event = false /\
      namespace_step ge cell (live state) event (live next)) ->
    (forall event target, namespace_step ge cell (live state) event target ->
      (namespace_event_waiting event = true /\ target = live state) \/
      (exists after, target = dead after /\ namespace_image event = false) \/
      (exists next, target = live next /\ namespace_event_waiting event = false /\
        namespace_image event = false /\ namespace_trace_region ge cell R n (namespace_advance log event) next)) ->
    namespace_trace_region ge cell R (S n) log state.

Theorem namespace_trace_weaken ge cell R n log state :
  namespace_trace_region ge cell R n log state ->
  forall larger, n <= larger -> namespace_trace_region ge cell R larger log state.
Proof.
  revert log state; induction n as [|n IH]; intros log state CERT larger BOUND.
  - inversion CERT; subst; constructor; assumption.
  - inversion CERT as [count history current RESULT|count history current PROGRESS CASES]; subst.
    + constructor; assumption.
    + destruct larger; [lia|]. eapply namespace_trace_next; [exact PROGRESS|].
      intros event target STEP; destruct (CASES _ _ STEP)
        as [WAIT|[DEAD|[next [TARGET [ADV [IMAGE TAIL]]]]]]; auto.
      right; right; exists next; split; [exact TARGET|]. split; [exact ADV|]. split; [exact IMAGE|].
      eapply IH; [exact TAIL|lia].
Qed.

Theorem namespace_trace_execution_split ge cell R n log start :
  namespace_trace_region ge cell R n log start ->
  forall events target, namespace_steps ge cell (live start) events target ->
  (namespace_cost events <= S n /\ namespace_no_images events /\
    (forall state, target = live state -> exists remaining,
      namespace_trace_region ge cell R remaining (log++namespace_fd_events events) state)) \/
  (exists prefix endpoint rest, events=prefix++rest /\ namespace_cost prefix<=n /\
    namespace_no_images prefix /\ namespace_steps ge cell (live start) prefix (live endpoint) /\
    R (log++namespace_fd_events prefix) endpoint /\ namespace_steps ge cell (live endpoint) rest target).
Proof.
  intros CERT events target RUN; remember (live start) as initial eqn:INITIAL.
  revert start n log INITIAL CERT.
  induction RUN as [initial|initial event middle events target STEP RUN IH];
    intros start n log INITIAL CERT; subst initial.
  - left; split; [cbn; lia|]. split; [constructor|].
    intros state SAME; inversion SAME; subst; cbn; rewrite app_nil_r; eauto.
  - inversion CERT as [count history current RESULT|count history current PROGRESS CASES]; subst.
    + right; exists [],start,(event::events); cbn; rewrite app_nil_r.
      split; [reflexivity|]. split; [lia|]. split; [constructor|].
      split; [constructor|]. split; [exact RESULT|econstructor; eassumption].
    + destruct (CASES _ _ STEP) as [[WAIT TARGET]|[[after [TARGET IMAGE]]|
        [next [TARGET [ADV [IMAGE TAIL]]]]]]; subst middle.
      * pose proof (namespace_wait_has_no_fd _ WAIT) as UNOBSERVED.
        destruct (IH _ _ _ eq_refl CERT) as [[COST [IMAGES LIVE]]|
          [prefix [endpoint [rest [EVENTS [COST [IMAGES [PRE [RESULT POST]]]]]]]]].
        -- left; split.
           ++ unfold namespace_cost; cbn; rewrite WAIT; exact COST.
           ++ split; [constructor; [apply namespace_wait_is_not_image; exact WAIT|exact IMAGES]|].
              unfold namespace_fd_events; cbn; rewrite UNOBSERVED; exact LIVE.
        -- right; exists (event::prefix),endpoint,rest; subst events; split; [reflexivity|].
           split; [unfold namespace_cost; cbn; rewrite WAIT; exact COST|].
           split; [constructor; [apply namespace_wait_is_not_image; exact WAIT|exact IMAGES]|].
           split; [econstructor; eassumption|].
           split; [unfold namespace_fd_events; cbn; rewrite UNOBSERVED; exact RESULT|exact POST].
      * destruct (namespace_dead_steps _ _ _ _ _ RUN) as [EVENTS TARGET]; subst.
        left; split.
        -- unfold namespace_cost; cbn; destruct (namespace_event_waiting event); cbn; lia.
        -- split; [constructor; [exact IMAGE|constructor]|intros; discriminate].
      * destruct (IH _ _ _ eq_refl TAIL) as [[COST [IMAGES LIVE]]|
          [prefix [endpoint [rest [EVENTS [COST [IMAGES [PRE [RESULT POST]]]]]]]]].
        -- left; split.
           ++ unfold namespace_cost; cbn; rewrite ADV; cbn; unfold namespace_cost in COST; lia.
           ++ split; [constructor; assumption|].
              rewrite <- namespace_advance_cons; exact LIVE.
        -- right; exists (event::prefix),endpoint,rest; subst events; split; [reflexivity|].
           split; [unfold namespace_cost; cbn; rewrite ADV; cbn; unfold namespace_cost in COST; lia|].
           split; [constructor; assumption|]. split; [econstructor; eassumption|].
           split; [rewrite <- namespace_advance_cons; exact RESULT|exact POST].
Qed.

Lemma namespace_trace_source_prepend ge cell R log state next n :
  store_edge ge state next -> namespace_trace_region ge cell R n log next ->
  namespace_trace_region ge cell R (S n) log state.
Proof.
  intros EDGE CERT; eapply namespace_trace_next.
  - exists (namespace_process (process_entry (entry_library (original_event (source_step E0))))),next.
    split; [reflexivity|]. split; [reflexivity|].
    apply namespace_process_step,process_entry_step,entry_library_step,original_step.
    apply internal; destruct EDGE as [IN [REAL UNIQUE]]; assumption.
  - intros event target STEP.
    destruct (namespace_store_edge_cases _ _ _ _ _ _ EDGE STEP) as [[EVENT TARGET]|[EVENT TARGET]]; subst.
    + right; right; exists next; split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|exact CERT].
    + right; left; exists (memory_of state); auto.
Qed.

Theorem namespace_trace_store_path ge cell R log (P : mem -> Prop) start count last remaining :
  store_path ge P start count last -> namespace_trace_region ge cell R remaining log last ->
  namespace_trace_region ge cell R (count+remaining) log start.
Proof.
  intros PATH CERT; induction PATH; cbn; auto; eapply namespace_trace_source_prepend; eauto.
Qed.

Theorem namespace_trace_actual ge cell R n log start :
  namespace_trace_region ge cell R n log start ->
  exists events endpoint, namespace_steps ge cell (live start) events (live endpoint) /\
    namespace_cost events<=n /\ namespace_no_images events /\ R (log++namespace_fd_events events) endpoint.
Proof.
  revert log start; induction n as [|n IH]; intros log start CERT;
    inversion CERT as [count history current RESULT|count history current PROGRESS CASES]; subst.
  - exists [],start; split; [constructor|]. split; [cbn; lia|].
    split; [constructor|]. cbn; rewrite app_nil_r; exact RESULT.
  - exists [],start; split; [constructor|]. split; [cbn; lia|].
    split; [constructor|]. cbn; rewrite app_nil_r; exact RESULT.
  - destruct PROGRESS as [event [next [ADV [IMAGE STEP]]]].
    destruct (CASES _ _ STEP) as [[WAIT SAME]|[[after [SAME NOIMAGE]]|
      [state [SAME [ORD [NOIMAGE TAIL]]]]]]; try congruence; try discriminate.
    inversion SAME; subst state.
    destruct (IH _ _ TAIL) as [events [endpoint [RUN [COST [IMAGES RESULT]]]]].
    exists (event::events),endpoint; split; [econstructor; eassumption|].
    split; [unfold namespace_cost in *; cbn; rewrite ADV; cbn; lia|].
    split; [constructor; assumption|]. rewrite <- namespace_advance_cons; exact RESULT.
Qed.
