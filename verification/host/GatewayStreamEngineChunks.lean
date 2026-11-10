import GatewayStreamGrouping

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

def Record.engineChunk (actor : ActorId) (record : Record) : Option (Nat × Bytes) :=
  match record.event with
  | .commit (.engine actual ordinal) _ =>
    if actual = actor then some (ordinal, record.bytesFor (.engine actor ordinal)) else none
  | _ => none

theorem Record.engine_chunk_source (actor : ActorId) (record : Record) (chunk : Nat × Bytes)
    (selected : record.engineChunk actor = some chunk) :
    ∃ extent, record.event = .commit (.engine actor chunk.1) extent ∧
      chunk.2 = record.bytesFor (.engine actor chunk.1) := by
  unfold Record.engineChunk at selected
  split at selected <;> try contradiction
  next actual ordinal extent event =>
    split at selected
    next same => subst actual; cases Option.some.inj selected; exact ⟨extent, event, rfl⟩
    next => cases selected

theorem engine_chunk_key_bytes (records : List Record) (actor : ActorId) (ordinal : Nat) :
    ((records.filterMap (Record.engineChunk actor)).filter (fun chunk => chunk.1 == ordinal)).flatMap Prod.snd =
      records.flatMap (Record.bytesFor (.engine actor ordinal)) := by
  induction records with
  | nil => rfl
  | cons head rest ih =>
    cases event : head.event with
    | commit key extent =>
      cases key with
      | native key primitiveEntry => simp [Record.engineChunk, Record.bytesFor, event, ih]
      | engine actual current =>
        by_cases same : actual = actor
        · subst actual
          by_cases key : current = ordinal
          · subst current; simp [Record.engineChunk, Record.bytesFor, event, ih]
          · simp [Record.engineChunk, Record.bytesFor, event, key, ih]
        · simp [Record.engineChunk, Record.bytesFor, event, same, ih]
    | begin | returned | lost | channel => simp [Record.engineChunk, Record.bytesFor, event, ih]

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

-- §FS-host-boundary.caller: Grouping uses the derived source order of actual
-- partial commits; it does not reorder an arbitrary physical transcript.
theorem actual_engine_chunks_ordered
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initialWorld : World} {population : Population}
    (source : ActorJournal runtime (Population.empty initialWorld) ticks population)
    {final : PhysicalState} {records : List Record}
    (physical : SynchronizedJournal primitive 0 ticks .unborn records final) (actor : ActorId) :
    (records.filterMap (Record.engineChunk actor)).Pairwise (fun first last => first.1 ≤ last.1) := by
  apply (actual_engine_commits_ordered source physical actor).filterMap (Record.engineChunk actor)
  intro first last ordered before firstSelected after lastSelected
  obtain ⟨firstExtent, firstEvent, firstBytes⟩ := first.engine_chunk_source actor before firstSelected
  obtain ⟨lastExtent, lastEvent, lastBytes⟩ := last.engine_chunk_source actor after lastSelected
  exact ordered before.1 after.1 firstExtent lastExtent firstEvent lastEvent

theorem actual_engine_bytes_grouped
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initialWorld : World} {population : Population}
    (source : ActorJournal runtime (Population.empty initialWorld) ticks population)
    {final : PhysicalState} {records : List Record}
    (physical : SynchronizedJournal primitive 0 ticks .unborn records final) (actor : ActorId)
    (base count : Nat)
    (bounds : ∀ record ∈ records, ∀ ordinal extent,
      record.event = .commit (.engine actor ordinal) extent → base ≤ ordinal ∧ ordinal < base + count) :
    (records.filterMap (Record.engineChunk actor)).flatMap Prod.snd =
      (List.range' base count).flatMap (fun ordinal => records.flatMap (Record.bytesFor (.engine actor ordinal))) := by
  have grouped := ordered_chunks_grouped (records.filterMap (Record.engineChunk actor)) base count
    (actual_engine_chunks_ordered source physical actor) (by
      intro item member
      obtain ⟨record, member, selected⟩ := List.mem_filterMap.mp member
      obtain ⟨extent, event, bytes⟩ := record.engine_chunk_source actor item selected
      exact bounds record member item.1 extent event)
  simpa only [engine_chunk_key_bytes] using grouped

end LeanCage.Host.PrivateStreams
