import FilesystemActors

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §AR-host-boundary.primitives: Logical allocation history does not depend on finite inode reuse.
structure LifetimeContract {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) : Prop where
  other : ∀ {β : Type} actor (effect : Effect β) reply before after object,
    runtime.other actor effect reply before after → before.allocated object = true → after.allocated object = true
  foreign : ∀ caller before after object,
    runtime.foreign caller before after → before.allocated object = true → after.allocated object = true
  retire : ∀ actor observation directory before after object,
    runtime.retire actor observation directory before after → before.allocated object = true → after.allocated object = true
  nativeRetire : ∀ actor observation beforeResources afterResources before after object,
    runtime.nativeRetire actor observation beforeResources afterResources before after →
    before.allocated object = true → after.allocated object = true

theorem operation_allocated {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : LifetimeContract runtime) {β : Type} {actor : ActorId} {effect : Effect β} {reply : Option β}
    {before after : World} (actual : ActorOperation runtime actor effect reply before after)
    (object : ObjectId) (allocated : before.allocated object = true) : after.allocated object = true := by
  cases effect with
  | filesystem request => exact kernel.allocation_monotone _ _ _ _ object actual allocated
  | spawn arguments => exact laws.other _ _ _ _ _ object actual allocated
  | read handle amount => exact laws.other _ _ _ _ _ object actual allocated
  | wait child => exact laws.other _ _ _ _ _ object actual allocated
  | terminate child => exact laws.other _ _ _ _ _ object actual allocated
  | tryWait child => exact laws.other _ _ _ _ _ object actual allocated
  | descriptor handle => exact laws.other _ _ _ _ _ object actual allocated

theorem actor_step_allocated {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : LifetimeContract runtime) {action : ActorAction} {before after : Population}
    (step : ActorStep runtime action before after) (object : ObjectId)
    (allocated : before.shared.allocated object = true) : after.shared.allocated object = true := by
  cases step with
  | launch => exact allocated
  | returned present alive head actual => exact operation_allocated laws actual object allocated
  | lost present alive head actual => exact operation_allocated laws actual object allocated
  | foreign actual => exact laws.foreign _ _ _ object actual allocated
  | retire present actual => exact laws.retire _ _ _ _ _ object actual allocated
  | nativeRetire actual => exact laws.nativeRetire _ _ _ _ _ _ object actual allocated

theorem actor_journal_allocated {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : LifetimeContract runtime) {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) (object : ObjectId)
    (allocated : before.shared.allocated object = true) : after.shared.allocated object = true := by
  induction journal with
  | nil => exact allocated
  | @cons tick ticks after tail ih => exact ih (actor_step_allocated laws tick.operation object allocated)

def FreshBirth {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} (tick : ActorTick runtime) (object : ObjectId) : Prop :=
  tick.before.shared.allocated object = false ∧ tick.after.shared.allocated object = true

-- §FS-host-boundary.ownership: Different successful births cannot reuse an earlier lifetime token.
theorem distinct_journal_births {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : LifetimeContract runtime) {before after : Population}
    {ticks leading between trailing : List (ActorTick runtime)} {first second : ActorTick runtime}
    {left right : ObjectId} (journal : ActorJournal runtime before ticks after)
    (positions : ticks = leading ++ first :: between ++ second :: trailing)
    (earlier : FreshBirth first left) (later : FreshBirth second right) : left ≠ right := by
  intro same
  subst right
  have normalized : ticks = leading ++ first :: (between ++ second :: trailing) := by
    simpa only [List.append_assoc, List.cons_append] using positions
  rw [normalized] at journal
  obtain ⟨atFirst, _, tail⟩ := actor_journal_split leading _ journal
  cases tail with
  | cons rest =>
    obtain ⟨atSecond, middle, final⟩ := actor_journal_split between _ rest
    cases final with
    | cons suffix =>
      have allocated := actor_journal_allocated laws middle left earlier.2
      rw [later.1] at allocated
      cases allocated

theorem journal_birth_not_initial {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : LifetimeContract runtime) {before after : Population}
    {ticks leading trailing : List (ActorTick runtime)} {tick : ActorTick runtime} {object : ObjectId}
    (journal : ActorJournal runtime before ticks after) (position : ticks = leading ++ tick :: trailing)
    (birth : FreshBirth tick object) : before.shared.allocated object = false := by
  cases initial : before.shared.allocated object with
  | false => rfl
  | true =>
    rw [position] at journal
    obtain ⟨middle, first, rest⟩ := actor_journal_split leading _ journal
    cases rest with
    | cons tail =>
      have allocated := actor_journal_allocated laws first object initial
      rw [birth.1] at allocated
      cases allocated

-- §FS-host-boundary.ownership: The born object comes from this exact actor's actual mkdir call.
theorem actor_mkdir_fresh_birth {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (tick : ActorTick runtime) (actor : ActorId) (fd : UInt64) (name : ByteArray) (reply : Reply)
    (action : tick.action = .returned actor (.filesystem {op := .mkdirAt, first := fd, second := 448, left := name}) reply)
    (component : Directories.component name = true) (acknowledged : reply.1 = 0) (empty : reply.2.isEmpty = true)
    (parentLive : ∃ engine parent, tick.before.actors actor = some engine ∧ engine.references fd = some parent) :
    ∃ object parent, FreshBirth tick object ∧
      tick.before.shared.entries parent.object name = none ∧
      tick.after.shared.entries parent.object name = some object ∧
      ∃ engine, tick.before.actors actor = some engine ∧ engine.references fd = some parent := by
  rcases tick with ⟨kind, before, after, operation⟩
  dsimp only at action parentLive ⊢
  subst kind
  cases operation with
  | @returned β population actualActor engine effect next actualReply world present alive head actual =>
    obtain ⟨original, parent, originalPresent, live⟩ := parentLive
    have sameEngine := Option.some.inj (originalPresent.symm.trans present)
    subst original
    obtain ⟨object, fresh, allocated, absent, created⟩ :=
      kernel.mkdir_fresh _ _ _ _ parent actual rfl live component acknowledged empty
    exact ⟨object, parent, ⟨fresh, allocated⟩, absent, created, engine, present, live⟩

end LeanCage.Host.Kernel
