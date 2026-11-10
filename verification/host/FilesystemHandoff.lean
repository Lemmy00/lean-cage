import FilesystemExecFlags

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

private theorem absent_step {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {action : ActorAction} (actual : ActorStep runtime action before after)
    (actor : ActorId) (absent : before.actors actor = none) :
    after.actors actor = none ∨ ∃ references closeExec workingDirectory,
      action = .launch actor references closeExec workingDirectory ∧
      after = before.launch actor (.initialFrom sourceProgram references closeExec workingDirectory) ∧
      runtime.initialReferences actor before.shared references closeExec workingDirectory := by
  cases actual with
  | @launch population owner references closeExec workingDirectory fresh vacant inherited =>
    by_cases same : actor = owner
    · subst owner
      exact .inr ⟨references, closeExec, workingDirectory, rfl, rfl, inherited⟩
    · left
      simpa only [Population.launch, Population.install, ite_eq_right same] using absent
  | @returned β population owner engine effect next reply world present alive head operation =>
    have different : actor ≠ owner := by intro same; subst owner; rw [absent] at present; cases present
    left
    simpa only [Population.advance, Population.install, ite_eq_right different] using absent
  | @lost β population owner engine effect next world present alive head operation =>
    have different : actor ≠ owner := by intro same; subst owner; rw [absent] at present; cases present
    left
    simpa only [Population.advance, Population.install, ite_eq_right different] using absent
  | foreign operation | nativeRetire operation => exact .inl absent
  | @retire population owner engine observation world present operation =>
    have different : actor ≠ owner := by intro same; subst owner; rw [absent] at present; cases present
    left
    simpa only [Population.advance, Population.install, ite_eq_right different] using absent

structure HandoffCut {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) (actor : ActorId)
    (before after : Population) (ticks : List (ActorTick runtime)) where
  leading : List (ActorTick runtime)
  tick : ActorTick runtime
  trailing : List (ActorTick runtime)
  shape : ticks = leading ++ tick :: trailing
  first : ActorJournal runtime before leading tick.before
  last : ActorJournal runtime tick.after trailing after
  references : UInt64 → Option Handle
  closeExec : UInt64 → Bool
  workingDirectory : ObjectId
  action : tick.action = .launch actor references closeExec workingDirectory
  afterLaunch : tick.after = tick.before.launch actor (.initialFrom sourceProgram references closeExec workingDirectory)
  inherited : runtime.initialReferences actor tick.before.shared references closeExec workingDirectory

-- §FS-host-boundary.caller: A live actor's handoff is extracted from this one actual journal.
theorem actual_actor_handoff {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) (actor : ActorId)
    (absent : before.actors actor = none) (engine : EngineState) (present : after.actors actor = some engine) :
    Nonempty (HandoffCut runtime actor before after ticks) := by
  induction journal with
  | nil => rw [absent] at present; cases present
  | @cons tick ticks after tail ih =>
    rcases absent_step tick.operation actor absent with stillAbsent |
        ⟨references, closeExec, workingDirectory, action, afterLaunch, inherited⟩
    · obtain ⟨cut⟩ := ih stillAbsent present
      exact ⟨{
        cut with
        leading := tick :: cut.leading
        shape := by simp only [cut.shape, List.cons_append]
        first := .cons cut.first }⟩
    · exact ⟨{
        leading := []
        tick
        trailing := ticks
        shape := rfl
        first := .nil _
        last := tail
        references
        closeExec
        workingDirectory
        action
        afterLaunch
        inherited }⟩

theorem handoff_engine_present {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId}
    {before after : Population} {ticks : List (ActorTick runtime)} (cut : HandoffCut runtime actor before after ticks) :
    cut.tick.after.actors actor = some (.initialFrom sourceProgram cut.references cut.closeExec cut.workingDirectory) := by
  rw [cut.afterLaunch]
  simp [Population.launch, Population.install]

theorem selected_event_alive {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} (tick : ActorTick runtime)
    {actor : ActorId} {engine : EngineState} {event : Program.Event}
    (action : tick.action.eventFor actor = some event) (present : tick.before.actors actor = some engine) :
    engine.running = true := by
  rcases tick with ⟨kind, before, after, actual⟩
  cases actual with
  | launch => cases action
  | @returned β population owner current effect next reply world currentPresent alive head operation =>
    dsimp only [ActorAction.eventFor] at action
    split at action
    · rename_i same
      subst owner
      have sameEngine := Option.some.inj (present.symm.trans currentPresent)
      subst engine
      exact alive
    · cases action
  | @lost β population owner current effect next world currentPresent alive head operation =>
    dsimp only [ActorAction.eventFor] at action
    split at action
    · rename_i same
      subst owner
      have sameEngine := Option.some.inj (present.symm.trans currentPresent)
      subst engine
      exact alive
    · cases action
  | foreign | retire | nativeRetire => cases action

-- §FS-host-boundary.caller: This interface is supplied by the actual native pair/spawn producer.
def NativeChannelProducer {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) (ipc : ObjectId → Prop) : Prop :=
  ∀ actor world references closeExec workingDirectory,
    runtime.initialReferences actor world references closeExec workingDirectory →
    Nonempty (InitialEngineBinding ipc references closeExec)

structure SelectedActorHistory {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) (initial : World)
    (ticks : List (ActorTick runtime)) (tick : ActorTick runtime) (actor : ActorId) (engine : EngineState) where
  preceding : List (ActorTick runtime)
  following : List (ActorTick runtime)
  shape : ticks = preceding ++ tick :: following
  launch : HandoffCut runtime actor (Population.empty initial) tick.before preceding
  launchedHere : launch.tick ∈ ticks
  history : ActorHistoryWith runtime actor (SourceReturnAt runtime ticks actor) 0
    (launch.tick.after.project (.initialFrom sourceProgram launch.references launch.closeExec launch.workingDirectory))
    engine.events (tick.before.project engine)

-- §FS-host-boundary.acceptance: Every selected actor call has its actual complete ordered prefix.
theorem actual_selected_actor_history {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {event : Program.Event}
    (selected : ticks[position]? = some tick) (action : tick.action.eventFor actor = some event)
    (present : tick.before.actors actor = some engine) :
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
  have alive := selected_event_alive tick action present
  obtain ⟨events, eventsShape, residual, history⟩ := actor_journal_recorded_projection descriptors lifetimes
    references environment ticks cut.last included startConsistent actor first engine firstPresent rfl present alive
  have same : engine.events = events := by
    simpa only [first, EngineState.initialFrom, List.nil_append] using eventsShape
  change ActorHistoryWith runtime actor (SourceReturnAt runtime ticks actor) 0
    (cut.tick.after.project first) events (tick.before.project engine) at history
  rw [← same] at history
  exact ⟨⟨leading, trailing, shape, cut, cutMember, history⟩⟩

-- §FS-host-boundary.ownership: Startup, its handoff and the selected spawn share the same journal.
theorem actual_source_spawn_raw_closed {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : CloseExecContract kernel) (descriptors : DescriptorContract kernel)
    (runtimeReferences : RuntimeDescriptorContract runtime) (runtimeLaws : RuntimeCloseExecContract runtime)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (environment : InterferenceContract kernel) {ipc : ObjectId → Prop}
    (fromNative : NativeChannelProducer runtime ipc)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {arguments : IO.Process.SpawnArgs} {event : Program.Event}
    (selected : ticks[position]? = some tick) (action : tick.action.eventFor actor = some event)
    (present : tick.before.actors actor = some engine) (spawn : SpawnUse arguments event) :
    RawClosedOnExec (tick.before.project engine) := by
  obtain ⟨captured⟩ := actual_selected_actor_history descriptors lifetimes references environment
    journal selected action present
  obtain ⟨binding⟩ := fromNative actor captured.launch.tick.before.shared captured.launch.references
    captured.launch.closeExec captured.launch.workingDirectory captured.launch.inherited
  have raw := runtimeReferences.initial_raw actor captured.launch.tick.before.shared captured.launch.references
    captured.launch.closeExec captured.launch.workingDirectory captured.launch.inherited
  exact actual_selected_spawn_raw_closed laws descriptors runtimeReferences runtimeLaws journal
    selected action present spawn binding raw captured.history

end LeanCage.Host.Kernel
