import FilesystemHandoff

namespace LeanCage.Host.Kernel

-- §FS-host-boundary.caller: A running actor has its actual handoff and completed history
-- even when the selected global tick belongs to a peer receiving its still-pending output.
theorem actual_running_actor_history {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    (selected : ticks[position]? = some tick) (present : tick.before.actors actor = some engine)
    (alive : engine.running = true) :
    Nonempty (SelectedActorHistory runtime initial ticks tick actor engine) := by
  obtain ⟨leading, trailing, shape⟩ := selected_tick_split selected
  have leadingJournal : ActorJournal runtime (Population.empty initial) leading tick.before := by
    have arranged := journal
    rw [shape] at arranged
    obtain ⟨middle, preceding, rest⟩ := actor_journal_split leading _ arranged
    cases rest with
    | cons tail => exact preceding
  obtain ⟨cut⟩ := actual_actor_handoff leadingJournal actor rfl engine present
  have included : ∀ other ∈ cut.trailing, other ∈ ticks := by
    intro other member
    have inLeading : other ∈ leading := by rw [cut.shape]; simp [member]
    rw [shape]
    simp [inLeading]
  have cutMember : cut.tick ∈ ticks := by
    have inLeading : cut.tick ∈ leading :=
      Eq.mpr (congrArg (fun items => cut.tick ∈ items) cut.shape) (by simp)
    rw [shape]
    simp [inLeading]
  have startConsistent := (actor_journal_consistent descriptors lifetimes references journal
    (empty_population_consistent initial)).2 cut.tick cutMember |>.2
  let first := EngineState.initialFrom sourceProgram cut.references cut.closeExec cut.workingDirectory
  have firstPresent : cut.tick.after.actors actor = some first := handoff_engine_present cut
  obtain ⟨events, eventsShape, residual, history⟩ := actor_journal_recorded_projection descriptors lifetimes
    references environment ticks cut.last included startConsistent actor first engine firstPresent rfl present alive
  have same : engine.events = events := by
    simpa only [first, EngineState.initialFrom, List.nil_append] using eventsShape
  change ActorHistoryWith runtime actor (SourceReturnAt runtime ticks actor) 0
    (cut.tick.after.project first) events (tick.before.project engine) at history
  rw [← same] at history
  exact ⟨⟨leading, trailing, shape, cut, cutMember, history⟩⟩

end LeanCage.Host.Kernel
