import FilesystemFamilyJournal
import FilesystemCwdFrames

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: Derive the selected base from the actual root/CWD source operations.
-- The family prefix is the application fold's already-established induction hypothesis.
theorem source_start_current_public {kernel : Contract} {runtime : ActorRuntime kernel}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (lookup : DataLookupContract kernel initialObjects dataObjects)
    (cwdLookup : WorkingDirectoryContract kernel initialObjects dataObjects)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    (selected : ticks[position]? = some tick) (present : tick.before.actors actor = some engine)
    {leading trailing : List (ActorTick runtime)} {first family : Family}
    (shape : ticks = leading ++ tick :: trailing) (count : leading.length = position)
    (prefixLabels : FamilyJournal runtime initialObjects dataObjects (Population.empty initial)
      first leading tick.before family)
    (path : ByteArray) (ordinal : Nat) {before : World} {events : List (Request × Reply)}
    {started : SourcePaths.Started}
    (run : RecordedRun kernel (fun index request reply =>
      SourceReturnAt runtime ticks actor index Reply (.filesystem request) reply)
      ordinal (SourcePaths.start path) before events (tick.before.project engine) (.ok started))
    (bound : ordinal + events.length ≤ engine.events.length) :
    ∃ handle, engine.references started.base = some handle ∧ family handle.object = none ∧
      SourcePaths.components path = .ok started.parts := by
  have bounded := recorded_history_source_bound run.2 (ordinal + events.length) (Nat.le_refl _)
  obtain ⟨handle, live, choice, components⟩ := source_start_handle_recorded descriptors
    (fun index request reply before after =>
      SourceReturnAt runtime ticks actor index Reply (.filesystem request) reply before after ∧
        index < ordinal + events.length) ordinal lookup path ⟨run.1, bounded⟩
  refine ⟨handle, live, ?_, components⟩
  rcases choice with ⟨absolute, initialized⟩ |
      ⟨relative, inherited, index, checking, checked, reply, lower, origin, actual, atCwd, sameCwd, spelled⟩
  · exact family_initial_public (family_journal_graph prefixLabels).2 handle.object initialized
  · obtain ⟨sourcePosition, sourceTick, sourceEngine, afterEngine, sourceAt, action, sourcePresent,
      afterPresent, sourceCount, beforeShape, afterShape⟩ := origin.1
    have beforeSource : sourceEngine.events.length < engine.events.length := by
      rw [sourceCount]
      exact Nat.lt_of_lt_of_le origin.2 bound
    have earlier := source_ordinal_orders_positions journal sourceAt selected actor sourceEngine engine
      sourcePresent present beforeSource
    have inLeading : sourcePosition < leading.length := by omega
    have selectedBefore : leading[sourcePosition]? = some sourceTick := by
      simpa only [shape, List.getElem?_append_left inLeading] using sourceAt
    obtain ⟨beforeFamily, remaining, graph, suffixLabels⟩ := family_journal_selected_suffix prefixLabels selectedBefore
    have graphChecking : FamilyGraph checking beforeFamily initialObjects dataObjects := by
      rw [beforeShape]
      exact ⟨graph.live, graph.young, graph.data, graph.border, graph.descendants⟩
    have publicCwd : beforeFamily handle.object = none := by
      have publicObject := working_directory_public cwdLookup graphChecking actual rfl spelled
      rw [sameCwd] at publicObject
      exact publicObject
    have allocated : sourceTick.before.shared.allocated handle.object = true := by
      have liveObject := descriptors.reference_allocated _ _ _ _ _ _ actual atCwd
      simpa only [beforeShape, Population.project] using liveObject
    exact family_journal_public lifetimes suffixLabels allocated publicCwd

end LeanCage.Host.Kernel
