import FilesystemSpawnSources

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

abbrev ProcessToken := Nat

structure ChildReferences where
  handles : UInt64 → Option Handle
  closeOnExec : UInt64 → Bool
  workingDirectory : ObjectId

-- §AR-host-boundary.primitives: Lifetime tokens are distinct from reusable observed Linux PIDs.
structure Processes where
  allocated : ProcessToken → Bool
  owner : ProcessToken → Option ActorId
  launchArguments : ProcessToken → Option IO.Process.SpawnArgs
  pid : ProcessToken → Option Nat
  references : ProcessToken → Option ChildReferences

def ChildReferences.project (references : ChildReferences) (shared : World) : World :=
  { shared with
    handles := references.handles
    closeOnExec := references.closeOnExec
    workingDirectory := references.workingDirectory }

-- §AR-host-boundary.primitives: Each observation concerns one actual spawn, never child lifetime.
structure ProcessContract {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) where
  step : ActorTick runtime → Processes → Processes → Prop
  monotone : ∀ tick before after token,
    step tick before after → before.allocated token = true → after.allocated token = true
  owner_frame : ∀ tick before after token owner,
    step tick before after → before.owner token = some owner → after.owner token = some owner
  arguments_frame : ∀ tick before after token arguments,
    step tick before after → before.launchArguments token = some arguments →
    after.launchArguments token = some arguments
  pid_frame : ∀ tick before after token pid,
    step tick before after → before.pid token = some pid → after.pid token = some pid
  fresh_source : ∀ tick before after token,
    step tick before after → before.allocated token = false → after.allocated token = true →
    ∃ actor arguments event, tick.action.eventFor actor = some event ∧ SpawnUse arguments event ∧
      after.owner token = some actor ∧ after.launchArguments token = some arguments
  spawn_success : ∀ tick before after actor arguments (child : IO.Process.Child arguments.toStdioConfig),
    step tick before after → tick.action = .returned actor (.spawn arguments) (.ok child) →
    ∃ token, before.allocated token = false ∧ after.allocated token = true ∧
      after.owner token = some actor ∧ after.launchArguments token = some arguments ∧
      after.pid token = some child.pid.toNat ∧ 0 < child.pid.toNat ∧ child.pid.toNat ≤ 2147483647

inductive ProcessJournal {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} (contract : ProcessContract runtime) :
    Processes → List (ActorTick runtime) → Processes → Prop where
  | nil (processes : Processes) : ProcessJournal contract processes [] processes
  | cons {before middle after : Processes} {tick : ActorTick runtime} {ticks : List (ActorTick runtime)}
      (actual : contract.step tick before middle) (tail : ProcessJournal contract middle ticks after) :
      ProcessJournal contract before (tick :: ticks) after

theorem process_journal_monotone {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} {contract : ProcessContract runtime}
    {before after : Processes} {ticks : List (ActorTick runtime)} (journal : ProcessJournal contract before ticks after)
    (token : ProcessToken) (allocated : before.allocated token = true) : after.allocated token = true := by
  induction journal with
  | nil => exact allocated
  | cons actual tail ih => exact ih (contract.monotone _ _ _ _ actual allocated)

theorem process_journal_selected {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} {contract : ProcessContract runtime}
    {before after : Processes} {ticks : List (ActorTick runtime)} (journal : ProcessJournal contract before ticks after)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick) :
    ∃ prior next, contract.step tick prior next := by
  induction journal generalizing position with
  | nil => cases selected
  | @cons before middle after first ticks actual tail ih =>
    cases position with
    | zero => have same := Option.some.inj selected; subst first; exact ⟨before, middle, actual⟩
    | succ position => exact ih selected

theorem tick_event_engine {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} (tick : ActorTick runtime)
    {actor : ActorId} {event : Program.Event} (action : tick.action.eventFor actor = some event) :
    ∃ engine, tick.before.actors actor = some engine := by
  rcases tick with ⟨kind, before, after, step⟩
  cases step with
  | launch => cases action
  | @returned β population owner engine effect next reply world present alive head actual =>
    dsimp only [ActorAction.eventFor] at action
    split at action
    · rename_i same; subst actor; exact ⟨engine, present⟩
    · cases action
  | @lost β population owner engine effect next world present alive head actual =>
    dsimp only [ActorAction.eventFor] at action
    split at action
    · rename_i same; subst actor; exact ⟨engine, present⟩
    · cases action
  | foreign | retire | nativeRetire => cases action

structure RecordedProcessBirth {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (contract : ProcessContract runtime) (ticks : List (ActorTick runtime)) (token : ProcessToken) where
  position : Nat
  tick : ActorTick runtime
  before : Processes
  after : Processes
  selected : ticks[position]? = some tick
  actual : contract.step tick before after
  fresh : before.allocated token = false
  allocated : after.allocated token = true

-- §FS-host-boundary.ownership: Backend authority starts at the same source/physical birth sample.
theorem recorded_process_source {kernel : Contract} {runtime : ActorRuntime kernel} {contract : ProcessContract runtime}
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final) {token : ProcessToken}
    (birth : RecordedProcessBirth contract ticks token) :
    ∃ actor arguments event engine,
      birth.tick.action.eventFor actor = some event ∧ SpawnUse arguments event ∧
      birth.tick.before.actors actor = some engine ∧ birth.after.owner token = some actor ∧
      birth.after.launchArguments token = some arguments ∧ Nonempty (EntrySpawn engine.events arguments event) := by
  obtain ⟨actor, arguments, event, action, spawn, owner, launched⟩ :=
    contract.fresh_source _ _ _ _ birth.actual birth.fresh birth.allocated
  obtain ⟨engine, present⟩ := tick_event_engine birth.tick action
  exact ⟨actor, arguments, event, engine, action, spawn, present, owner, launched,
    selected_spawn_source journal birth.selected action present spawn⟩

-- §FS-host-boundary.acceptance: A successful actual spawn has an owned token without PID
-- uniqueness.
theorem actual_spawn_has_recorded_birth {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {contract : ProcessContract runtime} {before after : Processes} {ticks : List (ActorTick runtime)}
    (journal : ProcessJournal contract before ticks after) {position : Nat} {tick : ActorTick runtime}
    (selected : ticks[position]? = some tick) (actor : ActorId) (arguments : IO.Process.SpawnArgs)
    (child : IO.Process.Child arguments.toStdioConfig)
    (source : tick.action = .returned actor (.spawn arguments) (.ok child)) :
    ∃ token, Nonempty (RecordedProcessBirth contract ticks token) := by
  obtain ⟨prior, next, actual⟩ := process_journal_selected journal selected
  obtain ⟨token, fresh, allocated, owner, launched, pid, positive, bounded⟩ :=
    contract.spawn_success _ _ _ _ _ _ actual source
  exact ⟨token, ⟨⟨position, tick, prior, next, selected, actual, fresh, allocated⟩⟩⟩

end LeanCage.Host.Kernel
