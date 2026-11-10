(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual ordered stores establish vectors before a selected spawn call. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine StoreSteps ClightSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayMemoryPrefixes GatewayFramedRuntime
  GatewaySpawnVectors GatewaySpawnVectorStores GatewaySpawnVectorMemory GatewayVectorCells.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_firstn_selected {A : Type} (values : list A) index value :
  nth_error values index = Some value -> firstn (S index) values = firstn index values ++ [value].
Proof.
  revert values; induction index as [|index IH]; intros [|first rest] SELECTED; cbn in *; try discriminate.
  - inversion SELECTED; reflexivity.
  - f_equal; apply IH; exact SELECTED.
Qed.

Lemma actual_spawn_vectors_sequence index : (index < 6)%nat ->
  spawn_vector_after index = Ssequence (spawn_vector_assignment index) (spawn_vector_after (S index)).
Proof. destruct index as [|[|[|[|[|[|index]]]]]]; intro BOUND; try lia; reflexivity. Qed.

Section VectorPrefix.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
  (environment : env) (temporaries : temp_env) (blocks : gateway_spawn_vector_blocks) (symbols : gateway_spawn_vector_symbols).
Variable base : mem -> World -> Prop.
Local Definition cells := gateway_spawn_cell_plan blocks symbols.
Hypothesis LOCATIONS : gateway_spawn_vector_locations ge environment blocks symbols.
Hypothesis DISTINCT : gateway_spawn_blocks_distinct blocks.
(* These obligations concern one actual memory instruction or interference
   edge. The SDK/caller consumer proves them from its native regions and actual
   struct-footprint separation; they assert no vector/helper result. *)
Hypothesis AMBIENT : forall before world after next, base before world ->
  gateway_interference backend before world after next ->
  base after next /\ Mem.unchanged_on (gateway_vector_span cells) before after.
Hypothesis STORE_BASE : forall before world after cell,
  base before world -> In cell cells ->
  Mem.store (vector_cell_chunk cell) before (vector_cell_block cell) (vector_cell_offset cell)
    (vector_cell_value cell) = Some after -> base after world.

Definition gateway_spawn_vector_progress index memory world : Prop :=
  base memory world /\ Forall (gateway_vector_writable memory) cells /\
  Forall (gateway_vector_loaded memory) (firstn index cells).

Lemma gateway_spawn_progress_ambient index : gateway_ambient_closed backend (gateway_spawn_vector_progress index).
Proof.
  intros before world after next [BASE [ACCESS LOADED]] INTERFERENCE.
  destruct (AMBIENT _ _ _ _ BASE INTERFERENCE) as [NEXT FRAME].
  split; [exact NEXT |]. split; [eapply gateway_vector_access_frame; eassumption |].
  rewrite Forall_forall in *; intros cell MEMBER.
  assert (INCLUDED : In cell cells).
  { rewrite <- (firstn_skipn index cells); apply in_or_app; left; exact MEMBER. }
  eapply Mem.load_unchanged_on; [exact FRAME | |apply LOADED; exact MEMBER].
  intros position INSIDE; exists cell; split; [exact INCLUDED |]. split; [reflexivity |exact INSIDE].
Qed.

Lemma gateway_spawn_progress_store index before world :
  (index < 6)%nat -> gateway_spawn_vector_progress index before world ->
  exists cell after, nth_error cells index = Some cell /\
    Mem.store (vector_cell_chunk cell) before (vector_cell_block cell) (vector_cell_offset cell)
      (vector_cell_value cell) = Some after /\ gateway_spawn_vector_progress (S index) after world.
Proof.
  intros BOUND [BASE [ACCESS LOADED]].
  destruct (nth_error cells index) as [cell |] eqn:SELECTED.
  2: { apply nth_error_None in SELECTED; change (6 <= index)%nat in SELECTED; lia. }
  assert (MEMBER : In cell cells) by (eapply nth_error_In; exact SELECTED).
  assert (WRITABLE : gateway_vector_writable before cell).
  { eapply Forall_forall; eassumption. }
  assert (TYPED : gateway_vector_typed cell).
  { pose proof (gateway_spawn_vector_typed blocks symbols) as ALL.
    eapply Forall_forall; eassumption. }
  destruct (gateway_vector_store before cell cells (firstn index cells) WRITABLE TYPED ACCESS
    (gateway_spawn_vector_before_separate blocks symbols index cell DISTINCT SELECTED) LOADED)
    as [after [STORE [NEXT_ACCESS NEXT_LOADED]]].
  exists cell, after; split; [reflexivity |]. split; [exact STORE |].
  split; [eapply STORE_BASE; eassumption |]. split; [exact NEXT_ACCESS |].
  rewrite (gateway_firstn_selected _ _ _ SELECTED); exact NEXT_LOADED.
Qed.

Lemma gateway_spawn_one_store_script target post index continuation template :
  (index < 6)%nat ->
  gateway_memory_prefix backend ge target post (gateway_spawn_vector_progress (S index))
    (State f_host_exchange (spawn_vector_after (S index)) continuation environment temporaries template) ->
  gateway_memory_prefix backend ge target post (gateway_spawn_vector_progress index)
    (State f_host_exchange (spawn_vector_after index) continuation environment temporaries template).
Proof.
  intros BOUND REST; rewrite (actual_spawn_vectors_sequence index BOUND).
  eapply gateway_memory_same with (following := State f_host_exchange (spawn_vector_assignment index)
    (Kseq (spawn_vector_after (S index)) continuation) environment temporaries template).
  - apply gateway_spawn_progress_ambient.
  - cbn; tauto.
  - intros before world READY; apply unchanged_store_edge, edge_seq.
  - eapply gateway_memory_next with (following := State f_host_exchange Sskip
      (Kseq (spawn_vector_after (S index)) continuation) environment temporaries template)
      (middle := gateway_spawn_vector_progress (S index)).
    + apply gateway_spawn_progress_ambient.
    + destruct index as [|[|[|[|[|[|index]]]]]]; try lia; cbn; tauto.
    + intros before world READY.
      destruct (gateway_spawn_progress_store index before world BOUND READY) as [cell [after [SELECTED [STORE NEXT]]]].
      exists after; split; [|exact NEXT].
      eapply actual_spawn_vector_store; [exact LOCATIONS |exact SELECTED |exact STORE].
    + eapply gateway_memory_same with (following := State f_host_exchange (spawn_vector_after (S index))
        continuation environment temporaries template).
      * apply gateway_spawn_progress_ambient.
      * cbn; tauto.
      * intros before world READY; apply unchanged_store_edge, edge_skip_seq.
      * exact REST.
Qed.

Theorem gateway_spawn_vectors_script continuation template :
  gateway_memory_prefix backend ge
    (State f_host_exchange (spawn_vector_after 6) continuation environment temporaries template)
    (gateway_spawn_vector_progress 6) (gateway_spawn_vector_progress 0)
    (State f_host_exchange spawn_vector_start continuation environment temporaries template).
Proof.
  assert (SCRIPT : forall remaining index, (index + remaining = 6)%nat ->
    gateway_memory_prefix backend ge
      (State f_host_exchange (spawn_vector_after 6) continuation environment temporaries template)
      (gateway_spawn_vector_progress 6) (gateway_spawn_vector_progress index)
      (State f_host_exchange (spawn_vector_after index) continuation environment temporaries template)).
  { intro remaining; induction remaining as [|remaining IH]; intros index TOTAL.
    - assert (index = 6)%nat by lia; subst index; apply gateway_memory_identity.
    - apply gateway_spawn_one_store_script; [lia |apply IH; lia]. }
  exact (SCRIPT 6%nat 0%nat eq_refl).
Qed.

Theorem gateway_actual_spawn_vectors continuation before world events terminal next :
  gateway_instruction_boundary terminal -> base before world -> Forall (gateway_vector_writable before) cells ->
  gateway_steps backend ge (gateway_live (State f_host_exchange spawn_vector_start continuation environment temporaries before) world)
    events (gateway_live terminal next) ->
  exists prefix suffix memory current,
    events = prefix ++ suffix /\ Forall GatewayReadonly.gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live (State f_host_exchange spawn_vector_start continuation environment temporaries before) world)
      prefix (gateway_live (State f_host_exchange (spawn_vector_after 6) continuation environment temporaries memory) current) /\
    base memory current /\ Forall (gateway_vector_writable memory) cells /\ Forall (gateway_vector_loaded memory) cells /\
    gateway_steps backend ge
      (gateway_live (State f_host_exchange (spawn_vector_after 6) continuation environment temporaries memory) current)
      suffix (gateway_live terminal next).
Proof.
  intros BOUNDARY BASE ACCESS RUN.
  destruct (gateway_memory_prefix_cut backend ge _ _ _ _ before world events terminal next
    (gateway_spawn_vectors_script continuation before) BOUNDARY
    ltac:(split; [exact BASE |split; [exact ACCESS |constructor]]) RUN)
    as (prefix & suffix & memory & current & EVENTS & QUIET & PREFIX & [FINAL [WRITABLE LOADED]] & SUFFIX).
  change (Forall (gateway_vector_loaded memory) cells) in LOADED.
  exists prefix, suffix, memory, current; repeat split; assumption.
Qed.
End VectorPrefix.
