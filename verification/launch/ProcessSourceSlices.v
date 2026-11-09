(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Cut the same physical history at an actual consumed source cursor. *)
From Stdlib Require Import Arith List Lia.
From EntryProcess Require Import ProcessJournal ProcessSourceRecording ProcessSourceTables ProcessSourceWorlds.
Import ListNotations.

Lemma source_cursor_step_single before tick after:
  SourceCursorStep before tick after ->forall program,(before program<=after program<=S(before program))%nat.
Proof.
  intro STEP;destruct STEP as[before tick SOURCE|before tick selected SOURCE];intro program;[lia|].
  unfold source_cursor_next;destruct(Nat.eqb program selected)eqn:SAME;
    [apply Nat.eqb_eq in SAME;subst program|];lia.
Qed.

Lemma source_process_step_cursor operation groups child runs tracked other cursor worlds before tick
    middle middle_worlds after:
  SourceProcessStep operation groups child runs tracked other cursor worlds before tick middle middle_worlds after ->
  SourceCursorStep cursor tick middle.
Proof.
  intro STEP;destruct STEP.
  - eapply source_cursor_advance;exact H1.
  - destruct H;[eapply source_cursor_external|eapply source_cursor_advance];eassumption.
Qed.

Theorem source_process_schedule_cut operation groups child runs tracked other cursor worlds before ticks
    final final_worlds after boundary:
  SourceProcessSchedule operation groups child runs tracked other cursor worlds before ticks final final_worlds after ->
  (cursor tracked<=boundary<=final tracked)%nat ->
  exists prefix suffix middle middle_worlds boundary_world,
    ticks=prefix++suffix /\
    SourceProcessSchedule operation groups child runs tracked other cursor worlds before prefix
      middle middle_worlds boundary_world /\
    SourceProcessSchedule operation groups child runs tracked other middle middle_worlds boundary_world suffix
      final final_worlds after /\middle tracked=boundary.
Proof.
  intro RUN;induction RUN;intro BOUNDS.
  - assert(SAME:cursor tracked=boundary)by lia.
    exists[],[],cursor,worlds,world;split;[reflexivity|]. split;[constructor|]. split;[constructor|exact SAME].
  - destruct(Nat.eq_dec(cursor tracked)boundary)as[SAME|DIFFERENT].
    + exists[],(tick::ticks),cursor,worlds,before;split;[reflexivity|]. split;[constructor|].
      split;[econstructor;eassumption|exact SAME].
    + pose proof(source_cursor_step_single _ _ _(source_process_step_cursor _ _ _ _ _ _ _ _ _ _ _ _ _ H)tracked)
        as PROGRESS.
      assert(NEXT:(middle tracked<=boundary<=final tracked)%nat)by lia.
      destruct(IHRUN NEXT)as[prefix[suffix[next[next_worlds[boundary_world[EVENTS[PREFIX[SUFFIX CUT]]]]]]]].
      exists(tick::prefix),suffix,next,next_worlds,boundary_world;split;[cbn;rewrite EVENTS;reflexivity|].
      split;[econstructor;eassumption|]. split;assumption.
Qed.
