import FilesystemRetirement
import FilesystemBorrowing

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §AR-host-boundary.primitives: A raw FD has no IO.FS.Handle finalizer; runtime handles stay
-- separate.
structure RuntimeDescriptorContract {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram)
    : Prop extends RetirementContract runtime where
  initial_raw : ∀ actor world references closeExec workingDirectory,
    runtime.initialReferences actor world references closeExec workingDirectory → RawReferences references
  spawn : ∀ actor arguments reply before after fd handle,
    runtime.other actor (.spawn arguments) reply before after →
    before.handles fd = some handle → handle.rawOwned = true → after.handles fd = some handle
  read : ∀ actor stream amount reply before after fd handle,
    runtime.other actor (.read stream amount) reply before after →
    before.handles fd = some handle → handle.rawOwned = true → after.handles fd = some handle
  wait : ∀ {configuration : IO.Process.StdioConfig} actor (child : IO.Process.Child configuration)
    reply before after fd handle,
    runtime.other actor (.wait child) reply before after →
    before.handles fd = some handle → handle.rawOwned = true → after.handles fd = some handle
  terminate : ∀ {configuration : IO.Process.StdioConfig} actor (child : IO.Process.Child configuration)
    reply before after fd handle,
    runtime.other actor (.terminate child) reply before after →
    before.handles fd = some handle → handle.rawOwned = true → after.handles fd = some handle
  tryWait : ∀ {configuration : IO.Process.StdioConfig} actor (child : IO.Process.Child configuration)
    reply before after fd handle,
    runtime.other actor (.tryWait child) reply before after →
    before.handles fd = some handle → handle.rawOwned = true → after.handles fd = some handle
  descriptor : ∀ actor stream reply before after fd handle,
    runtime.other actor (.descriptor stream) reply before after →
    before.handles fd = some handle → handle.rawOwned = true → after.handles fd = some handle
  parent_directory : ∀ {β : Type} actor (effect : Effect β) reply before after,
    runtime.other actor effect reply before after → after.workingDirectory = before.workingDirectory
  new_reference : ∀ {β : Type} actor (effect : Effect β) reply before after fd handle,
    runtime.other actor effect reply before after → after.handles fd = some handle →
    before.handles fd = some handle

def RuntimeEffect {β : Type} (effect : Effect β) : Prop :=
  match effect with
  | .filesystem _ => False
  | _ => True

def Population.Raw (population : Population) : Prop :=
  ∀ actor engine, population.actors actor = some engine → RawReferences engine.references

private theorem operation_after_raw {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel) (laws : RuntimeDescriptorContract runtime)
    {β : Type} {actor : ActorId} {effect : Effect β} {reply : Option β} {before after : World}
    (actual : ActorOperation runtime actor effect reply before after) (raw : RawReferences before.handles) :
    RawReferences after.handles := by
  cases effect with
  | filesystem request => exact descriptors.after_raw _ _ _ _ actual
  | spawn arguments => exact fun fd handle live => raw fd handle (laws.new_reference _ _ _ _ _ _ _ actual live)
  | read stream amount => exact fun fd handle live => raw fd handle (laws.new_reference _ _ _ _ _ _ _ actual live)
  | wait child => exact fun fd handle live => raw fd handle (laws.new_reference _ _ _ _ _ _ _ actual live)
  | terminate child => exact fun fd handle live => raw fd handle (laws.new_reference _ _ _ _ _ _ _ actual live)
  | tryWait child => exact fun fd handle live => raw fd handle (laws.new_reference _ _ _ _ _ _ _ actual live)
  | descriptor stream => exact fun fd handle live => raw fd handle (laws.new_reference _ _ _ _ _ _ _ actual live)

theorem actor_operation_after_raw {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel) (laws : RuntimeDescriptorContract runtime)
    {β : Type} {actor : ActorId} {effect : Effect β} {reply : Option β} {before after : World}
    (actual : ActorOperation runtime actor effect reply before after) (raw : RawReferences before.handles) :
    RawReferences after.handles := operation_after_raw descriptors laws actual raw

-- §FS-host-boundary.ownership: The source journal never promotes an SDK integer into a raw lease.
theorem actor_step_raw {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel) (laws : RuntimeDescriptorContract runtime)
    {before after : Population} {action : ActorAction} (step : ActorStep runtime action before after)
    (raw : before.Raw) : after.Raw := by
  cases step with
  | @launch population actor references closeExec workingDirectory fresh absent inherited =>
    intro query engine present
    by_cases same : query = actor
    · subst query
      simp only [Population.launch, Population.install] at present
      cases present
      exact laws.initial_raw _ _ _ _ _ inherited
    · exact raw query engine (by simpa only [Population.launch, Population.install, ite_eq_right same] using present)
  | @returned β population actor engine effect next reply world present alive head actual =>
    intro query afterEngine afterPresent
    by_cases same : query = actor
    · subst query
      simp only [Population.advance, Population.install] at afterPresent
      cases afterPresent
      exact operation_after_raw descriptors laws actual (raw actor engine present)
    · exact raw query afterEngine
        (by simpa only [Population.advance, Population.install, ite_eq_right same] using afterPresent)
  | @lost β population actor engine effect next world present alive head actual =>
    intro query afterEngine afterPresent
    by_cases same : query = actor
    · subst query
      simp only [Population.advance, Population.install] at afterPresent
      cases afterPresent
      exact operation_after_raw descriptors laws actual (raw actor engine present)
    · exact raw query afterEngine
        (by simpa only [Population.advance, Population.install, ite_eq_right same] using afterPresent)
  | foreign actual => exact raw
  | @retire population actor current observation world present actual =>
    intro query engine afterPresent
    by_cases same : query = actor
    · subst query
      simp only [Population.advance, Population.install, ite_eq_left] at afterPresent
      have identity := Option.some.inj afterPresent
      subst engine
      exact fun fd handle live => raw actor current present fd handle
        (laws.engine_subset _ _ _ _ _ _ _ actual live)
    · exact raw query engine
        (by simpa only [Population.advance, Population.install, ite_eq_right same] using afterPresent)
  | nativeRetire actual => exact raw

theorem actor_journal_raw {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel) (laws : RuntimeDescriptorContract runtime)
    {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) (raw : before.Raw) :
    after.Raw ∧ ∀ tick ∈ ticks, tick.before.Raw ∧ tick.after.Raw := by
  induction journal with
  | nil => exact ⟨raw, by intro tick impossible; cases impossible⟩
  | @cons tick ticks after tail ih =>
    have next := actor_step_raw descriptors laws tick.operation raw
    obtain ⟨final, rest⟩ := ih next
    refine ⟨final, ?_⟩
    intro selected member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨raw, next⟩
    · exact rest selected later

theorem actual_journal_raw {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel) (laws : RuntimeDescriptorContract runtime)
    {initial : World} {after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks after) :
    after.Raw ∧ ∀ tick ∈ ticks, tick.before.Raw ∧ tick.after.Raw := by
  apply actor_journal_raw descriptors laws journal
  intro actor engine present
  cases present

theorem runtime_keeps_raw {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : RuntimeDescriptorContract runtime) {β : Type} (actor : ActorId) (effect : Effect β)
    {reply : Option β} {before after : World} {fd : UInt64} {handle : Handle}
    (actual : ActorOperation runtime actor effect reply before after) (kind : RuntimeEffect effect)
    (live : before.handles fd = some handle) (raw : handle.rawOwned = true) : after.handles fd = some handle := by
  cases effect with
  | filesystem request => exact False.elim kind
  | spawn arguments => exact laws.spawn _ _ _ _ _ _ _ actual live raw
  | read stream amount => exact laws.read _ _ _ _ _ _ _ _ actual live raw
  | wait child => exact laws.wait _ _ _ _ _ _ _ actual live raw
  | terminate child => exact laws.terminate _ _ _ _ _ _ _ actual live raw
  | tryWait child => exact laws.tryWait _ _ _ _ _ _ _ actual live raw
  | descriptor stream => exact laws.descriptor _ _ _ _ _ _ _ actual live raw

-- §FS-host-boundary.ownership: Each source call supplies its own actual primitive borrowing rule.
inductive ActorBorrowPost {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) (actor : ActorId)
    (fd : UInt64) (handle : Handle) {α : Type} (post : α → Prop) : Program α → Prop where
  | pure {value : α} (property : post value) : ActorBorrowPost runtime actor fd handle post (.pure value)
  | call {β : Type} {effect : Effect β} {next : β → Program α}
      (preserve : ∀ before after observed, ActorOperation runtime actor effect observed before after →
        before.handles fd = some handle → after.handles fd = some handle)
      (following : ∀ before after reply, ActorOperation runtime actor effect (some reply) before after →
        before.handles fd = some handle → ActorBorrowPost runtime actor fd handle post (next reply)) :
      ActorBorrowPost runtime actor fd handle post (.call effect next)

theorem actor_borrow_bind {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {actor : ActorId} {fd : UInt64} {handle : Handle} {α β : Type} {program : Program α} {next : α → Program β}
    {first : α → Prop} {post : β → Prop} (initial : ActorBorrowPost runtime actor fd handle first program)
    (final : ∀ value, first value → ActorBorrowPost runtime actor fd handle post (next value)) :
    ActorBorrowPost runtime actor fd handle post (program.bind next) := by
  induction initial with
  | pure property => exact final _ property
  | call preserve following ih => exact .call preserve ih

theorem actor_borrow_lift {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} (actor : ActorId)
    {fd : UInt64} {handle : Handle} {α : Type} {program : Filesystem.Program α} {post : α → Prop}
    (source : BorrowPost kernel fd handle post program) :
    ActorBorrowPost runtime actor fd handle post (Program.liftFilesystem program) := by
  induction source with
  | pure property => exact .pure property
  | call preserve following ih => exact .call preserve ih

theorem runtime_effect_borrow {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : RuntimeDescriptorContract runtime) (actor : ActorId) (fd : UInt64) (handle : Handle)
    {β : Type} (effect : Effect β) (kind : RuntimeEffect effect) (raw : handle.rawOwned = true) :
    ActorBorrowPost runtime actor fd handle (fun _ => True) (Program.effect effect) := by
  apply ActorBorrowPost.call
  · intro before after observed actual live
    exact runtime_keeps_raw laws actor effect actual kind live raw
  · intro before after reply actual live
    exact .pure True.intro

end LeanCage.Host.Kernel
