import EntrypointWriterPrefix

namespace LeanCage.Host.EntrypointWriterPrefix
open Filesystem Kernel

-- §FS-host-boundary.caller: Pending IPC progress is sampled before any SDK reply.
-- The actual source residual and raw ordinal identify this call throughout partial commits.
structure PendingCut (engine : EngineState) (request : Request) where
  occurrence : PrimitiveFilesystem.FilesystemOccurrence Entrypoint.run engine.events request none
  primary : request = occurrence.primary
  origin : Cut occurrence.logicalBefore request none
  noGuards : occurrence.inside = []
  rawTrace : engine.events = occurrence.rawBefore

private theorem write_identity (request : Request) (writing : request.op = .write) :
    guardedCall request = .call request .pure := by
  rcases request with ⟨operation, first, second, third, left, right⟩
  cases writing
  rfl

private theorem call_cases {α : Type} {operation : Request} {next : Reply → Filesystem.Program α}
    {events : List (Request × Option Reply)} (source : Prefix (.call operation next) events) :
    events = [] ∨ events = [(operation, none)] ∨
      ∃ reply tail, events = (operation, some reply) :: tail ∧ Prefix (next reply) tail := by
  cases source with
  | empty => exact .inl rfl
  | lost => exact .inr (.inl rfl)
  | returned _ _ reply tail continued => exact .inr (.inr ⟨reply, tail, rfl, continued⟩)

-- §AR-host-boundary.primitives: No linearized result or later engine return is needed
-- to recover the exact original write selected by this actual raw source call.
theorem pending_write_source {engine : EngineState} {request : Request}
    {next : Reply → Program UInt32}
    (source : Residual (PrimitiveFilesystem.lower Entrypoint.run) engine.events engine.current)
    (head : engine.current = .call (.filesystem request) next) (writing : request.op = .write) :
    Nonempty (PendingCut engine request) := by
  have raw : Program.Prefix (PrimitiveFilesystem.lower Entrypoint.run)
      (engine.events ++ [Program.filesystemPrefixEvent (request, none)]) := by
    apply residual_prefix source
    rw [head]
    exact .lost _ _
  obtain ⟨occurrence⟩ := PrimitiveFilesystem.lowered_filesystem_source Entrypoint.run raw
  have primary := PrimitiveFilesystem.filesystem_occurrence_primary occurrence
    (by simp only [writing]; intro wrong; cases wrong)
    (by simp only [writing]; intro wrong; cases wrong)
    (by simp only [writing]; intro wrong; cases wrong)
  have logical := PrimitiveFilesystem.filesystem_occurrence_logical occurrence
  rw [← primary] at logical
  obtain ⟨origin⟩ := write_cut (observed := none) logical writing
  have noGuards : occurrence.inside = [] := by
    have active := occurrence.adapter
    rw [← primary, write_identity request writing] at active
    rcases call_cases active with empty | lost | ⟨reply, tail, shape, continued⟩
    · have impossible := congrArg List.length empty
      simp only [List.length_append, List.length_singleton, List.length_nil] at impossible
      omega
    · have length := congrArg List.length lost
      simp only [List.length_append, List.length_singleton] at length
      exact List.eq_nil_of_length_eq_zero (by omega)
    · have tailEmpty := Snapshot.prefix_pure_empty continued
      subst tail
      have length := congrArg List.length shape
      simp only [List.length_append, List.length_cons, List.length_nil] at length
      exact List.eq_nil_of_length_eq_zero (by omega)
  exact ⟨⟨occurrence, primary, origin, noGuards,
    by simpa only [noGuards, List.map_nil, List.append_nil] using occurrence.trace⟩⟩

-- §FS-host-boundary.acceptance: This may be the native receiving tick while the engine
-- remains in its write call. Its source prefix comes from this SAME global actor journal.
theorem pending_write_at {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {ticks : List (ActorTick runtime)} {final : Population}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick)
    {actor : ActorId} {engine : EngineState} (present : tick.before.actors actor = some engine)
    (running : engine.running = true) {request : Request} {next : Reply → Program UInt32}
    (head : engine.current = .call (.filesystem request) next) (writing : request.op = .write) :
    Nonempty (PendingCut engine request) := by
  obtain ⟨leading, trailing, shape⟩ := selected_tick_split selected
  exact pending_write_source (selected_actor_head_for journal leading trailing tick shape present running) head writing

end LeanCage.Host.EntrypointWriterPrefix
