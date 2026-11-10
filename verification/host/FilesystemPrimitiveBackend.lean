import FilesystemPrimitivePrefixPhases
import FilesystemSpawnSources
import FilesystemBackend

namespace LeanCage.Host.PrimitiveFilesystem
open Kernel

private def spawnEffect {α : Type} : Effect α → Bool
  | .spawn _ => true
  | _ => false

private def spawnEvent : Program.Event → Bool
  | .returned effect _ | .lost effect => spawnEffect effect

private theorem spawn_event_true {arguments : IO.Process.SpawnArgs} {event : Program.Event}
    (spawn : SpawnUse arguments event) : spawnEvent event = true := by cases spawn <;> rfl

private theorem filesystem_cannot_spawn {α : Type} (program : Filesystem.Program α)
    {before : List Program.Event} {event : Program.Event} {arguments : IO.Process.SpawnArgs}
    (active : Program.Prefix (Program.liftFilesystem program) (before ++ [event]))
    (spawn : SpawnUse arguments event) : False := by
  obtain ⟨events, source, shape⟩ := Program.lift_filesystem_prefix_source program active
  have member : event ∈ events.map Program.filesystemPrefixEvent := by rw [← shape]; simp
  obtain ⟨actual, member, same⟩ := List.mem_map.mp member
  subst event
  rcases actual with ⟨request, observed⟩
  have impossible := spawn_event_true spawn
  cases observed <;> cases impossible

private theorem effect_call_prefix {α β : Type} (effect : Effect β) (next : β → Program α)
    {before : List Program.Event} {event : Program.Event}
    (active : Program.Prefix (Program.effect effect) (before ++ [event])) :
    before = [] ∧ Program.Prefix (.call effect next) [event] := by
  generalize shape : before ++ [event] = events at active
  change Program.Prefix (.call effect (fun reply => .pure reply)) events at active
  cases active with
  | empty =>
    have length := congrArg List.length shape
    simp only [List.length_append, List.length_singleton, List.length_nil] at length
    omega
  | lost =>
    have length := congrArg List.length shape
    simp only [List.length_append, List.length_singleton] at length
    have empty : before = [] := List.length_eq_zero_iff.mp (by omega)
    subst before
    cases shape
    exact ⟨rfl, .lost effect next⟩
  | returned _ _ reply tail rest =>
    have noTail := Program.pure_prefix_empty reply rest
    subst tail
    have length := congrArg List.length shape
    simp only [List.length_append, List.length_cons, List.length_nil] at length
    have empty : before = [] := List.length_eq_zero_iff.mp (by omega)
    subst before
    cases shape
    exact ⟨rfl, .returned effect next reply [] (.empty _)⟩

-- §AR-host-boundary.interfaces: Runtime spawn is the exact same logical effect
-- in the expanded engine. Raw directory probes cannot create a child role.
theorem lowered_spawn_source {α : Type} (program : Program α)
    {before : List Program.Event} {event : Program.Event} {arguments : IO.Process.SpawnArgs}
    (active : Program.Prefix (lower program) (before ++ [event])) (spawn : SpawnUse arguments event) :
    ∃ logical, Program.Prefix program (logical ++ [event]) ∧ Chunks logical before := by
  obtain ⟨occurrence⟩ := lowered_last_source program active
  rcases occurrence with ⟨β, effect, next, logical, raw, inside, reached, adapter, trace⟩
  cases effect with
  | filesystem request => exact False.elim (filesystem_cannot_spawn (Filesystem.guardedCall request) adapter spawn)
  | spawn arguments | read stream limit | wait child | terminate child | tryWait child | descriptor stream =>
    obtain ⟨empty, same⟩ := effect_call_prefix _ next adapter
    exact ⟨logical, residual_prefix (reached_source reached) same,
      by simpa only [trace, empty, List.append_nil] using reached_chunks reached⟩

end LeanCage.Host.PrimitiveFilesystem

namespace LeanCage.Host.Kernel

structure PrimitiveSpawnSource (arguments : IO.Process.SpawnArgs) (before : List Program.Event) (event : Program.Event) where
  logicalBefore : List Program.Event
  source : EntrySpawn logicalBefore arguments event
  chunks : PrimitiveFilesystem.Chunks logicalBefore before

theorem selected_primitive_spawn_source {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {arguments : IO.Process.SpawnArgs} {event : Program.Event} (selected : all[position]? = some tick)
    (action : tick.action.eventFor actor = some event) (present : tick.before.actors actor = some engine)
    (spawn : SpawnUse arguments event) : Nonempty (PrimitiveSpawnSource arguments engine.events event) := by
  obtain ⟨logical, source, chunks⟩ := PrimitiveFilesystem.lowered_spawn_source Entrypoint.run
    (selected_source_prefix_for journal selected action present) spawn
  obtain ⟨role⟩ := entrypoint_spawn_source source spawn
  exact ⟨⟨logical, role, chunks⟩⟩

structure PrimitiveBackendSource {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (contract : ProcessContract runtime) (all : List (ActorTick runtime)) (position : Nat)
    (processes : Processes) (token : ProcessToken) where
  birth : RecordedProcessBirth contract all token
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
  source : PrimitiveSpawnSource arguments engine.events event

-- §FS-host-boundary.ownership: The child's actual earlier raw birth determines
-- its logical validator/QEMU source role and exact arguments. No future spawn
-- return or independent logical engine history supplies that role.
theorem actual_primitive_backend_source {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {contract : ProcessContract runtime} {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    (leading trailing : List (ActorTick runtime)) (tick : ActorTick runtime)
    (shape : all = leading ++ tick :: trailing) {processes : Processes}
    (registry : ProcessJournal contract Processes.empty leading processes) (token : ProcessToken)
    (active : processes.allocated token = true) :
    Nonempty (PrimitiveBackendSource contract all leading.length processes token) := by
  obtain ⟨cut⟩ := process_first_birth registry rfl active
  have selected : all[cut.position]? = some cut.tick := by
    rw [shape, List.getElem?_append_left cut.bound]
    exact cut.selected
  let birth : RecordedProcessBirth contract all token :=
    ⟨cut.position, cut.tick, cut.prior, cut.next, selected, cut.current, cut.fresh, cut.born⟩
  obtain ⟨owner, arguments, event, action, spawned, ownerAfter, argumentsAfter⟩ :=
    contract.fresh_source _ _ _ _ birth.actual birth.fresh birth.allocated
  obtain ⟨engine, present⟩ := tick_event_engine birth.tick action
  obtain ⟨source⟩ := selected_primitive_spawn_source journal birth.selected action present spawned
  exact ⟨⟨birth, cut.bound, owner, arguments, event, engine, action, spawned, present,
    process_journal_owner cut.last ownerAfter, process_journal_arguments cut.last argumentsAfter, source⟩⟩

end LeanCage.Host.Kernel
