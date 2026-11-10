import FilesystemProcesses

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.ownership: This registry tracks owned children, not other existing OS tasks.
def Processes.empty : Processes :=
  ⟨fun _ => false, fun _ => none, fun _ => none, fun _ => none, fun _ => none⟩

theorem process_journal_split {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {contract : ProcessContract runtime} {before after : Processes}
    (leading trailing : List (ActorTick runtime)) (journal : ProcessJournal contract before (leading ++ trailing) after) :
    ∃ middle, ProcessJournal contract before leading middle ∧ ProcessJournal contract middle trailing after := by
  induction leading generalizing before with
  | nil => exact ⟨before, .nil _, journal⟩
  | cons tick rest ih =>
    cases journal with
    | cons actual tail =>
      obtain ⟨middle, first, last⟩ := ih tail
      exact ⟨middle, .cons actual first, last⟩

theorem process_journal_owner {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {contract : ProcessContract runtime} {before after : Processes} {ticks : List (ActorTick runtime)}
    (journal : ProcessJournal contract before ticks after) {token : ProcessToken} {owner : ActorId}
    (source : before.owner token = some owner) : after.owner token = some owner := by
  induction journal with
  | nil => exact source
  | cons actual tail ih => exact ih (contract.owner_frame _ _ _ _ _ actual source)

theorem process_journal_arguments {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {contract : ProcessContract runtime} {before after : Processes} {ticks : List (ActorTick runtime)}
    (journal : ProcessJournal contract before ticks after) {token : ProcessToken} {arguments : IO.Process.SpawnArgs}
    (source : before.launchArguments token = some arguments) : after.launchArguments token = some arguments := by
  induction journal with
  | nil => exact source
  | cons actual tail ih => exact ih (contract.arguments_frame _ _ _ _ _ actual source)

structure ProcessBirthCut {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} (contract : ProcessContract runtime)
    (before after : Processes) (ticks : List (ActorTick runtime)) (token : ProcessToken) where
  position : Nat
  tick : ActorTick runtime
  prior : Processes
  next : Processes
  selected : ticks[position]? = some tick
  bound : position < ticks.length
  leading : List (ActorTick runtime)
  trailing : List (ActorTick runtime)
  count : position = leading.length
  shape : ticks = leading ++ tick :: trailing
  first : ProcessJournal contract before leading prior
  current : contract.step tick prior next
  last : ProcessJournal contract next trailing after
  fresh : prior.allocated token = false
  born : next.allocated token = true

-- §FS-host-boundary.ownership: An active child token has a real earlier birth on this registry.
theorem process_first_birth {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {contract : ProcessContract runtime} {before after : Processes} {ticks : List (ActorTick runtime)}
    (journal : ProcessJournal contract before ticks after) {token : ProcessToken}
    (absent : before.allocated token = false) (present : after.allocated token = true) :
    Nonempty (ProcessBirthCut contract before after ticks token) := by
  induction journal with
  | nil => rw [absent] at present; cases present
  | @cons before middle after tick ticks actual tail ih =>
    cases allocation : middle.allocated token with
    | false =>
      obtain ⟨cut⟩ := ih allocation present
      exact ⟨{
        cut with
        position := cut.position + 1
        selected := by simpa using cut.selected
        bound := by simpa only [List.length_cons] using Nat.add_lt_add_right cut.bound 1
        leading := tick :: cut.leading
        count := by simp only [List.length_cons, cut.count, Nat.add_comm]
        shape := by simp only [cut.shape, List.cons_append]
        first := .cons actual cut.first }⟩
    | true =>
      exact ⟨{
        position := 0
        tick
        prior := before
        next := middle
        selected := rfl
        bound := by simp
        leading := []
        trailing := ticks
        count := rfl
        shape := rfl
        first := .nil _
        current := actual
        last := tail
        fresh := absent
        born := allocation }⟩

structure BackendSource {kernel : Contract} {runtime : ActorRuntime kernel}
    (contract : ProcessContract runtime) (ticks : List (ActorTick runtime)) (position : Nat)
    (processes : Processes) (token : ProcessToken) where
  birth : RecordedProcessBirth contract ticks token
  earlier : birth.position < position
  owner : ActorId
  arguments : IO.Process.SpawnArgs
  event : Program.Event
  engine : EngineState
  action : birth.tick.action.eventFor owner = some event
  spawned : SpawnUse arguments event
  present : birth.tick.before.actors owner = some engine
  ownerNow : processes.owner token = some owner
  argumentsNow : processes.launchArguments token = some arguments
  source : EntrySpawn engine.events arguments event

-- §FS-host-boundary.ownership: A backend's role comes from its actual owned spawn, not a label.
theorem actual_backend_source {kernel : Contract} {runtime : ActorRuntime kernel}
    {contract : ProcessContract runtime} {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (leading trailing : List (ActorTick runtime)) (tick : ActorTick runtime)
    (shape : ticks = leading ++ tick :: trailing) {processes : Processes}
    (registry : ProcessJournal contract Processes.empty leading processes) (token : ProcessToken)
    (active : processes.allocated token = true) :
    Nonempty (BackendSource contract ticks leading.length processes token) := by
  obtain ⟨cut⟩ := process_first_birth registry rfl active
  have selected : ticks[cut.position]? = some cut.tick := by
    rw [shape, List.getElem?_append_left cut.bound]
    exact cut.selected
  let birth : RecordedProcessBirth contract ticks token :=
    ⟨cut.position, cut.tick, cut.prior, cut.next, selected, cut.current, cut.fresh, cut.born⟩
  obtain ⟨owner, arguments, event, engine, action, spawned, present, owned, launched, ⟨source⟩⟩ :=
    recorded_process_source journal birth
  exact ⟨⟨birth, cut.bound, owner, arguments, event, engine, action, spawned, present,
    process_journal_owner cut.last owned, process_journal_arguments cut.last launched, source⟩⟩

end LeanCage.Host.Kernel
