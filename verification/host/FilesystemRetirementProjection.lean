import FilesystemRecording
import FilesystemRetirement

namespace LeanCage.Host.Kernel

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.ownership: A stopped source never appends another effect after an actual
-- exit observation. Resource release may still continue in later retirement rows.
theorem actor_step_stopped_source {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {action : ActorAction} (actual : ActorStep runtime action before after)
    {actor : ActorId} {initial : EngineState} (present : before.actors actor = some initial)
    (stopped : initial.running = false) :
    ∃ final, after.actors actor = some final ∧ final.running = false ∧
      final.events = initial.events ∧ final.current = initial.current := by
  cases actual with
  | @launch population owner references closeExec directory fresh absent inherited =>
    have different : actor ≠ owner := by intro same; subst actor; rw [absent] at present; cases present
    exact ⟨initial, by simpa only [Population.launch, Population.install, ite_eq_right different] using present,
      stopped, rfl, rfl⟩
  | @returned β population owner current effect next reply world currentPresent alive head operation =>
    have different : actor ≠ owner := by
      intro same
      subst actor
      have identity := Option.some.inj (present.symm.trans currentPresent)
      subst current
      rw [stopped] at alive
      cases alive
    exact ⟨initial, by simpa only [Population.advance, Population.install, ite_eq_right different] using present,
      stopped, rfl, rfl⟩
  | @lost β population owner current effect next world currentPresent alive head operation =>
    have different : actor ≠ owner := by
      intro same
      subst actor
      have identity := Option.some.inj (present.symm.trans currentPresent)
      subst current
      rw [stopped] at alive
      cases alive
    exact ⟨initial, by simpa only [Population.advance, Population.install, ite_eq_right different] using present,
      stopped, rfl, rfl⟩
  | foreign | nativeRetire => exact ⟨initial, present, stopped, rfl, rfl⟩
  | @retire population owner current observation world currentPresent operation =>
    by_cases same : actor = owner
    · subst actor
      have identity := Option.some.inj (present.symm.trans currentPresent)
      subst current
      exact ⟨initial.retired observation world, by simp [Population.advance, Population.install], rfl, rfl, rfl⟩
    · exact ⟨initial, by simpa only [Population.advance, Population.install, ite_eq_right same] using present,
        stopped, rfl, rfl⟩

theorem actor_journal_stopped_source {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) {actor : ActorId} {initial : EngineState}
    (present : before.actors actor = some initial) (stopped : initial.running = false) :
    ∃ final, after.actors actor = some final ∧ final.running = false ∧
      final.events = initial.events ∧ final.current = initial.current := by
  induction journal generalizing initial with
  | nil => exact ⟨initial, present, stopped, rfl, rfl⟩
  | @cons tick ticks after tail ih =>
    obtain ⟨middle, middlePresent, middleStopped, sameEvents, sameCurrent⟩ :=
      actor_step_stopped_source tick.operation present stopped
    obtain ⟨final, finalPresent, finalStopped, finalEvents, finalCurrent⟩ := ih middlePresent middleStopped
    exact ⟨final, finalPresent, finalStopped, finalEvents.trans sameEvents, finalCurrent.trans sameCurrent⟩

-- §FS-host-boundary.acceptance: Completion releases only this process's observed raw refs/CWD;
-- no statement about controller or VM descendants follows from this certificate.
theorem retired_engine_resources_complete {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : RetirementContract runtime) {before after : Population} {actor : ActorId}
    {observation : EngineRetirement} (actual : ActorStep runtime (.retire actor observation) before after)
    (complete : observation.finished = true) :
    ∃ engine, after.actors actor = some engine ∧ engine.references = (fun _ => none) ∧
      engine.directory = none ∧ engine.running = false := by
  cases actual with
  | @retire population actor current observation world present operation =>
    obtain ⟨handles, directory⟩ := laws.engine_complete _ _ _ _ _ operation complete
    exact ⟨current.retired observation world, by simp [Population.advance, Population.install], handles, directory, rfl⟩

end LeanCage.Host.Kernel
