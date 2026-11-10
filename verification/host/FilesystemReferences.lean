import FilesystemBirths

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §AR-host-boundary.primitives: These laws connect actual descriptor/OFD lifetime observations.
structure ReferenceContract {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) : Prop where
  initial : ∀ actor world references closeExec workingDirectory,
    runtime.initialReferences actor world references closeExec workingDirectory → ValidReferences world references
  other_table : ∀ {β : Type} actor (effect : Effect β) reply before after,
    runtime.other actor effect reply before after → ValidReferences after after.handles
  other_identity : ∀ {β : Type} actor (effect : Effect β) reply before after id description,
    runtime.other actor effect reply before after → before.descriptions id = some description →
    ∃ later, after.descriptions id = some later ∧ later.object = description.object
  other_description : ∀ {β : Type} actor (effect : Effect β) reply before after id,
    runtime.other actor effect reply before after → before.descriptionAllocated id = true →
    after.descriptionAllocated id = true
  foreign_identity : ∀ caller before after id description,
    runtime.foreign caller before after → before.descriptions id = some description →
    ∃ later, after.descriptions id = some later ∧ later.object = description.object
  foreign_description : ∀ caller before after id,
    runtime.foreign caller before after → before.descriptionAllocated id = true → after.descriptionAllocated id = true
  retire_table : ∀ actor observation directory before after,
    runtime.retire actor observation directory before after → ValidReferences after after.handles
  retire_identity : ∀ actor observation directory before after id description,
    runtime.retire actor observation directory before after → before.descriptions id = some description →
    ∃ later, after.descriptions id = some later ∧ later.object = description.object
  retire_description : ∀ actor observation directory before after id,
    runtime.retire actor observation directory before after → before.descriptionAllocated id = true →
    after.descriptionAllocated id = true
  native_retire_identity : ∀ actor observation beforeResources afterResources before after id description,
    runtime.nativeRetire actor observation beforeResources afterResources before after → before.descriptions id = some description →
    ∃ later, after.descriptions id = some later ∧ later.object = description.object
  native_retire_description : ∀ actor observation beforeResources afterResources before after id,
    runtime.nativeRetire actor observation beforeResources afterResources before after → before.descriptionAllocated id = true →
    after.descriptionAllocated id = true

private theorem retained_references {before after : World} {references : UInt64 → Option Handle}
    (valid : ValidReferences before references)
    (objects : ∀ object, before.allocated object = true → after.allocated object = true)
    (descriptions : ∀ id, before.descriptionAllocated id = true → after.descriptionAllocated id = true)
    (identity : ∀ id description, before.descriptions id = some description →
      ∃ later, after.descriptions id = some later ∧ later.object = description.object) :
    ValidReferences after references := by
  intro fd handle present
  obtain ⟨object, allocated, description, actual, same⟩ := valid fd handle present
  obtain ⟨later, actualLater, sameLater⟩ := identity handle.description description actual
  exact ⟨objects _ object, descriptions _ allocated, later, actualLater, sameLater.trans same⟩

private theorem operation_after_references {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel) (laws : ReferenceContract runtime)
    {β : Type} {actor : ActorId} {effect : Effect β} {reply : Option β} {before after : World}
    (actual : ActorOperation runtime actor effect reply before after) : ValidReferences after after.handles := by
  cases effect with
  | filesystem request => exact descriptors.after_references _ _ _ _ actual
  | spawn arguments => exact laws.other_table _ _ _ _ _ actual
  | read handle amount => exact laws.other_table _ _ _ _ _ actual
  | wait child => exact laws.other_table _ _ _ _ _ actual
  | terminate child => exact laws.other_table _ _ _ _ _ actual
  | tryWait child => exact laws.other_table _ _ _ _ _ actual
  | descriptor handle => exact laws.other_table _ _ _ _ _ actual

theorem operation_retains_references {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime) (laws : ReferenceContract runtime)
    {β : Type} {actor : ActorId} {effect : Effect β} {reply : Option β} {before after : World}
    {references : UInt64 → Option Handle} (actual : ActorOperation runtime actor effect reply before after)
    (valid : ValidReferences before references) : ValidReferences after references := by
  apply retained_references valid
  · cases effect with
    | filesystem request => exact fun object => kernel.allocation_monotone _ _ _ _ object actual
    | spawn arguments => exact fun object => lifetimes.other _ _ _ _ _ object actual
    | read handle amount => exact fun object => lifetimes.other _ _ _ _ _ object actual
    | wait child => exact fun object => lifetimes.other _ _ _ _ _ object actual
    | terminate child => exact fun object => lifetimes.other _ _ _ _ _ object actual
    | tryWait child => exact fun object => lifetimes.other _ _ _ _ _ object actual
    | descriptor handle => exact fun object => lifetimes.other _ _ _ _ _ object actual
  · cases effect with
    | filesystem request => exact fun id => kernel.description_allocation_monotone _ _ _ _ id actual
    | spawn arguments => exact fun id => laws.other_description _ _ _ _ _ id actual
    | read handle amount => exact fun id => laws.other_description _ _ _ _ _ id actual
    | wait child => exact fun id => laws.other_description _ _ _ _ _ id actual
    | terminate child => exact fun id => laws.other_description _ _ _ _ _ id actual
    | tryWait child => exact fun id => laws.other_description _ _ _ _ _ id actual
    | descriptor handle => exact fun id => laws.other_description _ _ _ _ _ id actual
  · cases effect with
    | filesystem request => exact fun id description => descriptors.description_identity _ _ _ _ id description actual
    | spawn arguments => exact fun id description => laws.other_identity _ _ _ _ _ id description actual
    | read handle amount => exact fun id description => laws.other_identity _ _ _ _ _ id description actual
    | wait child => exact fun id description => laws.other_identity _ _ _ _ _ id description actual
    | terminate child => exact fun id description => laws.other_identity _ _ _ _ _ id description actual
    | tryWait child => exact fun id description => laws.other_identity _ _ _ _ _ id description actual
    | descriptor handle => exact fun id description => laws.other_identity _ _ _ _ _ id description actual

theorem operation_description_allocated {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : ReferenceContract runtime) {β : Type} {actor : ActorId} {effect : Effect β}
    {reply : Option β} {before after : World} (actual : ActorOperation runtime actor effect reply before after)
    (id : DescriptionId) (allocated : before.descriptionAllocated id = true) : after.descriptionAllocated id = true := by
  cases effect with
  | filesystem request => exact kernel.description_allocation_monotone _ _ _ _ id actual allocated
  | spawn arguments => exact laws.other_description _ _ _ _ _ id actual allocated
  | read handle amount => exact laws.other_description _ _ _ _ _ id actual allocated
  | wait child => exact laws.other_description _ _ _ _ _ id actual allocated
  | terminate child => exact laws.other_description _ _ _ _ _ id actual allocated
  | tryWait child => exact laws.other_description _ _ _ _ _ id actual allocated
  | descriptor handle => exact laws.other_description _ _ _ _ _ id actual allocated

theorem empty_population_consistent (world : World) : (Population.empty world).Consistent := by
  intro actor engine present
  cases present

-- §FS-host-boundary.acceptance: Reference consistency is produced from individual operations.
theorem actor_step_consistent {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime) (laws : ReferenceContract runtime)
    {before after : Population} {action : ActorAction} (step : ActorStep runtime action before after)
    (valid : before.Consistent) : after.Consistent := by
  cases step with
  | @launch population actor references closeExec workingDirectory fresh absent inherited =>
    intro query engine present
    by_cases same : query = actor
    · subst query
      simp only [Population.launch, Population.install] at present
      cases present
      exact laws.initial _ _ _ _ _ inherited
    · exact valid query engine (by simpa only [Population.launch, Population.install, ite_eq_right same] using present)
  | @returned β population actor engine effect next reply world present alive head actual =>
    intro query afterEngine afterPresent
    by_cases same : query = actor
    · subst query
      simp [Population.advance, Population.install] at afterPresent
      cases afterPresent
      exact operation_after_references descriptors laws actual
    · apply operation_retains_references descriptors lifetimes laws actual
      apply valid query afterEngine
      simpa only [Population.advance, Population.install, ite_eq_right same] using afterPresent
  | @lost β population actor engine effect next world present alive head actual =>
    intro query afterEngine afterPresent
    by_cases same : query = actor
    · subst query
      simp [Population.advance, Population.install] at afterPresent
      cases afterPresent
      exact operation_after_references descriptors laws actual
    · apply operation_retains_references descriptors lifetimes laws actual
      apply valid query afterEngine
      simpa only [Population.advance, Population.install, ite_eq_right same] using afterPresent
  | @foreign population caller world actual =>
    intro query engine present
    exact retained_references (valid query engine present)
      (fun object => lifetimes.foreign _ _ _ object actual)
      (fun id => laws.foreign_description _ _ _ id actual)
      (fun id description => laws.foreign_identity _ _ _ id description actual)
  | @retire population actor current observation world present actual =>
    intro query engine afterPresent
    by_cases same : query = actor
    · subst query
      simp only [Population.advance, Population.install, ite_eq_left] at afterPresent
      have identity := Option.some.inj afterPresent
      subst engine
      exact laws.retire_table _ _ _ _ _ actual
    · apply retained_references
        (valid query engine (by simpa only [Population.advance, Population.install, ite_eq_right same] using afterPresent))
      · exact fun object => lifetimes.retire actor observation current.directory (before.project current) world object actual
      · exact fun id => laws.retire_description actor observation current.directory (before.project current) world id actual
      · exact fun id description => laws.retire_identity actor observation current.directory (before.project current) world id description actual
  | @nativeRetire population actor observation beforeResources afterResources world actual =>
    intro query engine present
    exact retained_references (valid query engine present)
      (fun object => lifetimes.nativeRetire _ _ _ _ _ _ object actual)
      (fun id => laws.native_retire_description _ _ _ _ _ _ id actual)
      (fun id description => laws.native_retire_identity _ _ _ _ _ _ id description actual)

def JournalConsistent {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} (ticks : List (ActorTick runtime)) : Prop :=
  ∀ tick ∈ ticks, tick.before.Consistent ∧ tick.after.Consistent

theorem actor_journal_consistent {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime) (laws : ReferenceContract runtime)
    {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) (valid : before.Consistent) :
    after.Consistent ∧ JournalConsistent ticks := by
  induction journal with
  | nil => exact ⟨valid, by intro tick impossible; cases impossible⟩
  | @cons tick ticks after tail ih =>
    have next := actor_step_consistent descriptors lifetimes laws tick.operation valid
    obtain ⟨final, rest⟩ := ih next
    refine ⟨final, ?_⟩
    intro selected member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨valid, next⟩
    · exact rest selected later

end LeanCage.Host.Kernel
