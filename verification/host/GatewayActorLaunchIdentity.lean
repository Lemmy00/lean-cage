import GatewayWriterActorAlignment

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}

-- §FS-host-boundary.ownership: Actor lifetime identity is not a PID or a
-- selected equal transcript. Its one actual launch fixes the inherited table.
theorem source_launch_absent (tick : ActorTick runtime) (actor : ActorId)
    (references : UInt64 → Option Handle) (flags : UInt64 → Bool) (cwd : ObjectId)
    (action : tick.action = .launch actor references flags cwd) : tick.before.actors actor = none := by
  cases tick with
  | mk action before after actual =>
    cases actual <;> cases action
    assumption

theorem selected_after_before {first last : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime first ticks last) {left right : Nat} {beforeTick afterTick : ActorTick runtime}
    (beforeSelected : ticks[left]? = some beforeTick) (afterSelected : ticks[right]? = some afterTick)
    (ordered : left < right) : ∃ interval, ActorJournal runtime beforeTick.after interval afterTick.before := by
  obtain ⟨leading, rest, length, shape⟩ := selected_tick_exact_split beforeSelected
  rw [shape] at journal
  obtain ⟨middle, _, suffix⟩ := actor_journal_split leading _ journal
  cases suffix with
  | cons tail =>
    have atLast : rest[right - (left + 1)]? = some afterTick := by
      have selected : (leading ++ beforeTick :: rest)[right]? = some afterTick :=
        (congrArg (fun items : List (ActorTick runtime) => items[right]?) shape).symm.trans afterSelected
      have index : right - leading.length = (right - (left + 1)) + 1 := by omega
      rw [List.getElem?_append_right (by omega), index, List.getElem?_cons_succ] at selected
      exact selected
    exact journal_to_selected tail atLast

theorem selected_launch_position {initial : World} {ticks : List (ActorTick runtime)}
    {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    (history : SelectedActorHistory runtime initial ticks tick actor engine) :
    ticks[history.launch.leading.length]? = some history.launch.tick := by
  have first := congrArg (fun items : List (ActorTick runtime) => items[history.launch.leading.length]?) history.shape
  have second := congrArg (fun items : List (ActorTick runtime) =>
    (items ++ tick :: history.following)[history.launch.leading.length]?) history.launch.shape
  exact first.trans (second.trans (by simp [List.append_assoc]))

theorem selected_launch_references_unique {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {firstTick lastTick : ActorTick runtime} {actor : ActorId} {firstEngine lastEngine : EngineState}
    (first : SelectedActorHistory runtime initial ticks firstTick actor firstEngine)
    (last : SelectedActorHistory runtime initial ticks lastTick actor lastEngine) :
    first.launch.references = last.launch.references := by
  rcases Nat.lt_trichotomy first.launch.leading.length last.launch.leading.length with before | same | after
  · obtain ⟨interval, run⟩ := selected_after_before journal (selected_launch_position first) (selected_launch_position last) before
    obtain ⟨engine, present, ordered⟩ := actor_journal_keeps_actor run actor _ (handoff_engine_present first.launch)
    rw [source_launch_absent last.launch.tick actor _ _ _ last.launch.action] at present
    cases present
  · have tickIdentity := Option.some.inj ((selected_launch_position first).symm.trans (same ▸ (selected_launch_position last)))
    have actions : ActorAction.launch actor first.launch.references first.launch.closeExec first.launch.workingDirectory =
        .launch actor last.launch.references last.launch.closeExec last.launch.workingDirectory :=
      first.launch.action.symm.trans ((congrArg ActorTick.action tickIdentity).trans last.launch.action)
    exact (ActorAction.launch.inj actions).2.1
  · obtain ⟨interval, run⟩ := selected_after_before journal (selected_launch_position last) (selected_launch_position first) after
    obtain ⟨engine, present, ordered⟩ := actor_journal_keeps_actor run actor _ (handoff_engine_present last.launch)
    rw [source_launch_absent first.launch.tick actor _ _ _ first.launch.action] at present
    cases present

end LeanCage.Host.PrivateStreams
