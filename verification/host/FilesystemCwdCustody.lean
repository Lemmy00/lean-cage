import FilesystemNativeNamespace
import FilesystemNativeHandoff
import FilesystemRuntime

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

def EngineDirectoriesPublic (population : Population) (family : Family) : Prop :=
  ∀ actor engine, population.actors actor = some engine → family engine.workingDirectory = none

def EngineDirectoriesLive (population : Population) : Prop :=
  ∀ actor engine, population.actors actor = some engine → population.shared.allocated engine.workingDirectory = true

private theorem operation_directory {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : RuntimeDescriptorContract runtime) {β : Type} {actor : ActorId} {effect : Effect β}
    {observed : Option β} {before after : World} (actual : ActorOperation runtime actor effect observed before after) :
    after.workingDirectory = before.workingDirectory := by
  cases effect with
  | filesystem request => exact kernel.step_directory _ _ _ _ actual
  | spawn | read | wait | terminate | tryWait | descriptor => exact laws.parent_directory _ _ _ _ _ actual

-- §FS-host-boundary.ownership: The maintained engine never changes its inherited CWD.
-- Native callers' chdir/fchdir operations instead update their separate actual native tables.
theorem nonlaunch_directories_from {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : RuntimeDescriptorContract runtime) {action : ActorAction} {before after : Population}
    (actual : ActorStep runtime action before after)
    (notLaunch : ∀ actor references closeExec directory, action ≠ .launch actor references closeExec directory) :
    ∀ actor engine, after.actors actor = some engine →
      ∃ prior, before.actors actor = some prior ∧ engine.workingDirectory = prior.workingDirectory := by
  cases actual with
  | launch => exact False.elim (notLaunch _ _ _ _ rfl)
  | @returned β population owner current effect next reply world present alive head operation =>
    intro actor engine afterPresent
    by_cases same : actor = owner
    · subst actor
      simp only [Population.advance, Population.install, ite_eq_left] at afterPresent
      have identity := Option.some.inj afterPresent
      subst engine
      exact ⟨current, present, operation_directory laws operation⟩
    · exact ⟨engine, by
        simpa only [Population.advance, Population.install, ite_eq_right same] using afterPresent, rfl⟩
  | @lost β population owner current effect next world present alive head operation =>
    intro actor engine afterPresent
    by_cases same : actor = owner
    · subst actor
      simp only [Population.advance, Population.install, ite_eq_left] at afterPresent
      have identity := Option.some.inj afterPresent
      subst engine
      exact ⟨current, present, operation_directory laws operation⟩
    · exact ⟨engine, by
        simpa only [Population.advance, Population.install, ite_eq_right same] using afterPresent, rfl⟩
  | foreign | nativeRetire => exact fun actor engine present => ⟨engine, present, rfl⟩
  | @retire population owner current observation world present operation =>
    intro actor engine afterPresent
    by_cases same : actor = owner
    · subst actor
      simp only [Population.advance, Population.install, ite_eq_left] at afterPresent
      have identity := Option.some.inj afterPresent
      subst engine
      exact ⟨current, present, rfl⟩
    · exact ⟨engine, by
        simpa only [Population.advance, Population.install, ite_eq_right same] using afterPresent, rfl⟩

theorem nonlaunch_directories_custody {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : RuntimeDescriptorContract runtime) (lifetimes : LifetimeContract runtime)
    {action : ActorAction} {before after : Population} {first final : Family}
    (actual : ActorStep runtime action before after)
    (notLaunch : ∀ actor references closeExec directory, action ≠ .launch actor references closeExec directory)
    (live : EngineDirectoriesLive before) (publicDirectories : EngineDirectoriesPublic before first)
    (labels : ExistingLabels before.shared after.shared first final) :
    EngineDirectoriesLive after ∧ EngineDirectoriesPublic after final := by
  have previous := nonlaunch_directories_from laws actual notLaunch
  constructor
  · intro actor engine present
    obtain ⟨prior, earlier, directory⟩ := previous actor engine present
    rw [directory]
    exact actor_step_allocated lifetimes actual _ (live actor prior earlier)
  · intro actor engine present
    obtain ⟨prior, earlier, directory⟩ := previous actor engine present
    rw [directory]
    rcases labels prior.workingDirectory (live actor prior earlier) with same | released
    · exact same.trans (publicDirectories actor prior earlier)
    · exact released

private theorem launched_directories_custody {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {actor : ActorId} {references : UInt64 → Option Handle}
    {closeExec : UInt64 → Bool} {directory : ObjectId} {family : Family}
    (actual : ActorStep runtime (.launch actor references closeExec directory) before after)
    (live : EngineDirectoriesLive before) (publicDirectories : EngineDirectoriesPublic before family)
    (inheritedLive : before.shared.allocated directory = true) (inheritedPublic : family directory = none) :
    EngineDirectoriesLive after ∧ EngineDirectoriesPublic after family := by
  cases actual with
  | launch fresh absent inherited =>
    constructor
    · intro query engine present
      by_cases same : query = actor
      · subst query
        simp only [Population.launch, Population.install, ite_eq_left] at present
        have identity := Option.some.inj present
        subst engine
        exact inheritedLive
      · exact live query engine (by
          simpa only [Population.launch, Population.install, ite_eq_right same] using present)
    · intro query engine present
      by_cases same : query = actor
      · subst query
        simp only [Population.launch, Population.install, ite_eq_left] at present
        have identity := Option.some.inj present
        subst engine
        exact inheritedPublic
      · exact publicDirectories query engine (by
          simpa only [Population.launch, Population.install, ite_eq_right same] using present)

-- §FS-host-boundary.caller: CWD authority comes from the SAME current native exec snapshot.
-- No future source getcwd success or independent safe initial-directory premise is assumed.
theorem native_handoff_directories_custody {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before : NativeProcesses} {tick : ActorTick runtime} {family : Family}
    (handoff : NativeHandoffAt tick before) (nativeLive : NativeReferencesLive before tick.before.shared)
    (nativePublic : NativeReferencesPublic before family) (live : EngineDirectoriesLive tick.before)
    (publicDirectories : EngineDirectoriesPublic tick.before family) :
    EngineDirectoriesLive tick.after ∧ EngineDirectoriesPublic tick.after family := by
  have held : NativeHeld before handoff.execution.references.workingDirectory :=
    .inl ⟨handoff.actor, handoff.execution.references, handoff.current, .inr rfl⟩
  exact launched_directories_custody (handoff.action ▸ tick.operation) live publicDirectories
    (nativeLive _ held) (nativePublic _ held)

theorem empty_directories_custody (initial : World) (family : Family) :
    EngineDirectoriesLive (Population.empty initial) ∧ EngineDirectoriesPublic (Population.empty initial) family := by
  constructor <;> intro actor engine impossible <;> cases impossible

end LeanCage.Host.Kernel
