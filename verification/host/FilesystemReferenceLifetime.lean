import FilesystemRuntime
import FilesystemReferences

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §AR-host-boundary.primitives: The raw adapter has no dup operation. Every new open has a fresh
-- OFD lifetime; reusing an integer descriptor cannot resurrect its former reference.
structure RawReferenceLifetimeContract (kernel : Contract) : Prop where
  existing : ∀ before after request observed fd handle,
    kernel.step before request observed after → before.descriptionAllocated handle.description = true →
    after.handles fd = some handle → before.handles fd = some handle

-- §FS-host-boundary.ownership: Numeric FD reuse remains allowed with its genuinely fresh OFD.
theorem new_raw_reference_has_fresh_description {kernel : Contract}
    (raw : RawReferenceLifetimeContract kernel) {before after : World} {request : Request}
    {observed : Option Reply} {fd : UInt64} {handle : Handle}
    (actual : kernel.step before request observed after)
    (changed : before.handles fd ≠ some handle) (held : after.handles fd = some handle) :
    before.descriptionAllocated handle.description = false := by
  cases allocated : before.descriptionAllocated handle.description with
  | false => rfl
  | true => exact False.elim (changed (raw.existing _ _ _ _ _ _ actual allocated held))

theorem operation_reference_before {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (raw : RawReferenceLifetimeContract kernel) (sdk : RuntimeDescriptorContract runtime)
    {β : Type} {actor : ActorId} {effect : Effect β} {observed : Option β} {before after : World}
    {fd : UInt64} {handle : Handle} (actual : ActorOperation runtime actor effect observed before after)
    (old : before.descriptionAllocated handle.description = true) (held : after.handles fd = some handle) :
    before.handles fd = some handle := by
  cases effect with
  | filesystem request => exact raw.existing _ _ _ _ _ _ actual old held
  | spawn arguments => exact sdk.new_reference _ _ _ _ _ _ _ actual held
  | read stream amount => exact sdk.new_reference _ _ _ _ _ _ _ actual held
  | wait child => exact sdk.new_reference _ _ _ _ _ _ _ actual held
  | terminate child => exact sdk.new_reference _ _ _ _ _ _ _ actual held
  | tryWait child => exact sdk.new_reference _ _ _ _ _ _ _ actual held
  | descriptor stream => exact sdk.new_reference _ _ _ _ _ _ _ actual held

theorem actor_step_description_allocated {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (references : ReferenceContract runtime) {action : ActorAction} {before after : Population}
    (actual : ActorStep runtime action before after) (description : DescriptionId)
    (old : before.shared.descriptionAllocated description = true) :
    after.shared.descriptionAllocated description = true := by
  cases actual with
  | launch => exact old
  | returned present alive head operation => exact operation_description_allocated references operation description old
  | lost present alive head operation => exact operation_description_allocated references operation description old
  | foreign operation => exact references.foreign_description _ _ _ _ operation old
  | retire present operation => exact references.retire_description _ _ _ _ _ _ operation old
  | nativeRetire operation => exact references.native_retire_description _ _ _ _ _ _ _ operation old

theorem actor_step_presence {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {action : ActorAction} {before after : Population} {actor : ActorId} {engine : EngineState}
    (actual : ActorStep runtime action before after) (present : before.actors actor = some engine) :
    ∃ next, after.actors actor = some next := by
  cases actual with
  | @launch population owner owned closeExec cwd fresh absent inherited =>
    by_cases same : actor = owner
    · subst actor
      rw [absent] at present
      cases present
    · exact ⟨engine, by simpa only [Population.launch, Population.install, ite_eq_right same] using present⟩
  | @returned β population owner current effect next reply world ownerPresent alive head operation =>
    by_cases same : actor = owner
    · subst actor
      exact ⟨current.returned effect reply next world, by simp only [Population.advance, Population.install, ite_eq_left]⟩
    · exact ⟨engine, by simpa only [Population.advance, Population.install, ite_eq_right same] using present⟩
  | @lost β population owner current effect next world ownerPresent alive head operation =>
    by_cases same : actor = owner
    · subst actor
      exact ⟨current.lost effect world, by simp only [Population.advance, Population.install, ite_eq_left]⟩
    · exact ⟨engine, by simpa only [Population.advance, Population.install, ite_eq_right same] using present⟩
  | foreign operation => exact ⟨engine, present⟩
  | @retire population owner current observation world ownerPresent operation =>
    by_cases same : actor = owner
    · subst actor
      exact ⟨current.retired observation world, by simp only [Population.advance, Population.install, ite_eq_left]⟩
    · exact ⟨engine, by simpa only [Population.advance, Population.install, ite_eq_right same] using present⟩
  | nativeRetire operation => exact ⟨engine, present⟩

-- §FS-host-boundary.ownership: Only this actor's exact table can identify its old live reference.
theorem actor_step_reference_before {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (raw : RawReferenceLifetimeContract kernel) (sdk : RuntimeDescriptorContract runtime)
    {action : ActorAction} {before after : Population} {actor : ActorId} {engine nextEngine : EngineState}
    {fd : UInt64} {handle : Handle} (actual : ActorStep runtime action before after)
    (present : before.actors actor = some engine) (afterPresent : after.actors actor = some nextEngine)
    (old : before.shared.descriptionAllocated handle.description = true)
    (held : nextEngine.references fd = some handle) : engine.references fd = some handle := by
  cases actual with
  | @launch population owner owned closeExec cwd fresh absent inherited =>
    by_cases same : actor = owner
    · subst actor
      rw [absent] at present
      cases present
    · have unchanged : before.actors actor = some nextEngine := by
        simpa only [Population.launch, Population.install, ite_eq_right same] using afterPresent
      have engines := Option.some.inj (present.symm.trans unchanged)
      subst nextEngine
      exact held
  | @returned β population owner current effect next reply world ownerPresent alive head operation =>
    by_cases same : actor = owner
    · subst actor
      have engines := Option.some.inj (present.symm.trans ownerPresent)
      subst engine
      have afterSame : current.returned effect reply next world = nextEngine := by
        apply Option.some.inj
        simpa only [Population.advance, Population.install, ite_eq_left] using afterPresent
      subst nextEngine
      exact operation_reference_before raw sdk operation old held
    · have unchanged : before.actors actor = some nextEngine := by
        simpa only [Population.advance, Population.install, ite_eq_right same] using afterPresent
      have engines := Option.some.inj (present.symm.trans unchanged)
      subst nextEngine
      exact held
  | @lost β population owner current effect next world ownerPresent alive head operation =>
    by_cases same : actor = owner
    · subst actor
      have engines := Option.some.inj (present.symm.trans ownerPresent)
      subst engine
      have afterSame : current.lost effect world = nextEngine := by
        apply Option.some.inj
        simpa only [Population.advance, Population.install, ite_eq_left] using afterPresent
      subst nextEngine
      exact operation_reference_before raw sdk operation old held
    · have unchanged : before.actors actor = some nextEngine := by
        simpa only [Population.advance, Population.install, ite_eq_right same] using afterPresent
      have engines := Option.some.inj (present.symm.trans unchanged)
      subst nextEngine
      exact held
  | foreign operation =>
    have engines := Option.some.inj (present.symm.trans afterPresent)
    subst nextEngine
    exact held
  | @retire population owner current observation world ownerPresent operation =>
    by_cases same : actor = owner
    · subst actor
      have identity := Option.some.inj (present.symm.trans ownerPresent)
      subst engine
      have afterSame : current.retired observation world = nextEngine := by
        apply Option.some.inj
        simpa only [Population.advance, Population.install, ite_eq_left] using afterPresent
      subst nextEngine
      exact sdk.engine_subset _ _ _ _ _ _ _ operation held
    · have unchanged : before.actors actor = some nextEngine := by
        simpa only [Population.advance, Population.install, ite_eq_right same] using afterPresent
      have identity := Option.some.inj (present.symm.trans unchanged)
      subst nextEngine
      exact held
  | nativeRetire operation =>
    have identity := Option.some.inj (present.symm.trans afterPresent)
    subst nextEngine
    exact held

-- §FS-host-boundary.ownership: The same actual OFD supplies the live interval.
theorem actor_journal_reference_continuity {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (raw : RawReferenceLifetimeContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (references : ReferenceContract runtime) {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) {actor : ActorId} {engine final : EngineState}
    {fd : UInt64} {handle : Handle} (present : before.actors actor = some engine)
    (afterPresent : after.actors actor = some final)
    (old : before.shared.descriptionAllocated handle.description = true)
    (held : final.references fd = some handle) :
    engine.references fd = some handle ∧ ∀ tick ∈ ticks,
      (∃ prior, tick.before.actors actor = some prior ∧ prior.references fd = some handle) ∧
      ∃ next, tick.after.actors actor = some next ∧ next.references fd = some handle := by
  induction journal generalizing engine with
  | nil =>
    have same := Option.some.inj (present.symm.trans afterPresent)
    subst final
    exact ⟨held, by intro tick impossible; cases impossible⟩
  | @cons tick ticks after tail ih =>
    obtain ⟨middle, middlePresent⟩ := actor_step_presence tick.operation present
    have middleOld := actor_step_description_allocated references tick.operation handle.description old
    obtain ⟨middleHeld, later⟩ := ih middlePresent afterPresent middleOld
    have initialHeld := actor_step_reference_before raw sdk tick.operation present middlePresent old middleHeld
    refine ⟨initialHeld, ?_⟩
    intro selected member
    rcases List.mem_cons.mp member with rfl | laterMember
    · exact ⟨⟨engine, present, initialHeld⟩, middle, middlePresent, middleHeld⟩
    · exact later selected laterMember

end LeanCage.Host.Kernel
