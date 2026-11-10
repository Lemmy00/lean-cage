import FilesystemGlobalAuthority

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: Old logical lifetimes cannot reappear after actual retirement.
-- These are individual syscall/runtime observations, not stable pathname or private-region claims.
structure ObjectLifetimeContract {kernel : Contract} {sourceProgram : Program UInt32}
    (runtime : ActorRuntime kernel sourceProgram) : Prop where
  reference : ∀ before after request observed fd handle,
    kernel.step before request observed after → before.handles fd = some handle → ObjectAlive before handle.object
  filesystem : ∀ before after request observed object,
    kernel.step before request observed after → before.allocated object = true →
    ObjectAlive after object → ObjectAlive before object
  sdk : ∀ {β : Type} actor (effect : Effect β) observed before after object,
    runtime.other actor effect observed before after → before.allocated object = true →
    ObjectAlive after object → ObjectAlive before object
  foreign : ∀ caller before after object,
    runtime.foreign caller before after → before.allocated object = true →
    ObjectAlive after object → ObjectAlive before object
  retire : ∀ actor observation directory before after object,
    runtime.retire actor observation directory before after → before.allocated object = true →
    ObjectAlive after object → ObjectAlive before object
  nativeRetire : ∀ actor observation beforeResources afterResources before after object,
    runtime.nativeRetire actor observation beforeResources afterResources before after → before.allocated object = true →
    ObjectAlive after object → ObjectAlive before object

theorem operation_live_backward_for {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram}
    (laws : ObjectLifetimeContract runtime) {β : Type} {actor : ActorId} {effect : Effect β} {observed : Option β}
    {before after : World} {object : ObjectId} (actual : ActorOperation runtime actor effect observed before after)
    (old : before.allocated object = true) (alive : ObjectAlive after object) : ObjectAlive before object := by
  cases effect with
  | filesystem request => exact laws.filesystem _ _ _ _ _ actual old alive
  | spawn arguments => exact laws.sdk _ _ _ _ _ _ actual old alive
  | read stream amount => exact laws.sdk _ _ _ _ _ _ actual old alive
  | wait child => exact laws.sdk _ _ _ _ _ _ actual old alive
  | terminate child => exact laws.sdk _ _ _ _ _ _ actual old alive
  | tryWait child => exact laws.sdk _ _ _ _ _ _ actual old alive
  | descriptor stream => exact laws.sdk _ _ _ _ _ _ actual old alive

theorem operation_live_backward {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : ObjectLifetimeContract runtime) {β : Type} {actor : ActorId} {effect : Effect β} {observed : Option β}
    {before after : World} {object : ObjectId} (actual : ActorOperation runtime actor effect observed before after)
    (old : before.allocated object = true) (alive : ObjectAlive after object) : ObjectAlive before object :=
  operation_live_backward_for laws actual old alive

theorem actor_step_live_backward_for {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram}
    (laws : ObjectLifetimeContract runtime) {action : ActorAction} {before after : Population} {object : ObjectId}
    (actual : ActorStep runtime action before after) (old : before.shared.allocated object = true)
    (alive : ObjectAlive after.shared object) : ObjectAlive before.shared object := by
  cases actual with
  | launch => exact alive
  | returned present running head operation =>
    have survived := operation_live_backward_for laws operation old alive
    exact survived
  | lost present running head operation =>
    have survived := operation_live_backward_for laws operation old alive
    exact survived
  | foreign operation => exact laws.foreign _ _ _ _ operation old alive
  | retire present operation =>
    have survived := laws.retire _ _ _ _ _ _ operation old alive
    exact survived
  | nativeRetire operation => exact laws.nativeRetire _ _ _ _ _ _ _ operation old alive

theorem actor_step_live_backward {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : ObjectLifetimeContract runtime) {action : ActorAction} {before after : Population} {object : ObjectId}
    (actual : ActorStep runtime action before after) (old : before.shared.allocated object = true)
    (alive : ObjectAlive after.shared object) : ObjectAlive before.shared object :=
  actor_step_live_backward_for laws actual old alive

-- §FS-host-boundary.ownership: Existence at the actual late guard determines earlier liveness.
theorem actor_journal_live_backward_for {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram}
    (lifetimes : LifetimeContract runtime) (laws : ObjectLifetimeContract runtime)
    {before after : Population} {ticks : List (ActorTick runtime)} {object : ObjectId}
    (journal : ActorJournal runtime before ticks after) (old : before.shared.allocated object = true)
    (alive : ObjectAlive after.shared object) : ObjectAlive before.shared object := by
  induction journal with
  | nil => exact alive
  | @cons tick ticks after tail ih =>
    exact actor_step_live_backward_for laws tick.operation old
      (ih (actor_step_allocated lifetimes tick.operation object old) alive)

-- §AR-host-boundary.interfaces: Preserve the original logical-source specialization.
theorem actor_journal_live_backward {kernel : Contract} {runtime : ActorRuntime kernel}
    (lifetimes : LifetimeContract runtime) (laws : ObjectLifetimeContract runtime)
    {before after : Population} {ticks : List (ActorTick runtime)} {object : ObjectId}
    (journal : ActorJournal runtime before ticks after) (old : before.shared.allocated object = true)
    (alive : ObjectAlive after.shared object) : ObjectAlive before.shared object :=
  actor_journal_live_backward_for lifetimes laws journal old alive

theorem actor_journal_live_snapshots {kernel : Contract} {runtime : ActorRuntime kernel}
    (lifetimes : LifetimeContract runtime) (laws : ObjectLifetimeContract runtime)
    {before after : Population} {ticks : List (ActorTick runtime)} {object : ObjectId}
    (journal : ActorJournal runtime before ticks after) (old : before.shared.allocated object = true)
    (alive : ObjectAlive after.shared object) :
    ∀ tick ∈ ticks, ObjectAlive tick.before.shared object ∧ ObjectAlive tick.after.shared object := by
  induction journal with
  | nil => intro tick impossible; cases impossible
  | @cons tick ticks after tail ih =>
    have middleOld := actor_step_allocated lifetimes tick.operation object old
    have middleLive := actor_journal_live_backward lifetimes laws tail middleOld alive
    have firstLive := actor_step_live_backward laws tick.operation old middleLive
    intro selected member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨firstLive, middleLive⟩
    · exact ih middleOld alive selected later

end LeanCage.Host.Kernel
