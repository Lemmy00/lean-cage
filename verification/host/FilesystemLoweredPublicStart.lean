import FilesystemLookupNames
import FilesystemLoweredParentObservations
import FilesystemPublicStart

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

theorem source_open_actual_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal : Nat) (parent : UInt64) (name : ByteArray) (directory : Bool)
    {before after : World} {events : List (Request × Reply)} {fd : UInt64}
    (run : RecordedRun kernel origin ordinal (SourcePaths.openAt parent name directory).lower
      before events after (.ok fd)) :
    ∃ opening : RecordedOpen kernel origin
      {op := .openAt, first := parent, second := if directory then directoryFlags else readFlags, left := name} fd,
      after.handles fd = some opening.handle ∧ opening.before.workingDirectory = before.workingDirectory := by
  let request : Request := {
    op := .openAt, first := parent, second := if directory then directoryFlags else readFlags, left := name }
  let next (reply : Reply) : Filesystem.Program (Result UInt64) := match descriptor reply with
    | none => .pure (.error (failure "caller path openat" reply))
    | some opened => SourcePaths.publicHandle opened
  have stage : RecordedRun kernel origin ordinal
      ((guardedCall request).bind (fun reply => (next reply).lower)) before events after (.ok fd) := run
  obtain ⟨opening, reply, following, openedWorld, trace, opened, remaining⟩ := Kernel.recorded_run_bind_split _ _ stage
  unfold next at remaining
  split at remaining
  · cases remaining.1
  · rename_i openedFd recognized
    obtain ⟨actual, live, sameDirectory⟩ := guarded_open_recorded_directory laws opened rfl recognized
    obtain ⟨sameFd, finalLive⟩ := public_handle_same laws _ _ _ actual.handle remaining live
    subst openedFd
    exact ⟨actual, finalLive, sameDirectory⟩

-- §FS-host-boundary.ownership: The actual raw root/CWD open and getcwd observation select
-- the retained base. No byte-exact law for hostile public child lookups is assumed.
theorem source_start_handle_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal : Nat)
    {semantics : NameSemanticsView} {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (lookup : DynamicDataLookupContract kernel semantics initialObjects dataObjects) (path : ByteArray)
    {before after : World} {events : List (Request × Reply)} {selected : SourcePaths.Started}
    (run : RecordedRun kernel origin ordinal (SourcePaths.start path).lower before events after (.ok selected)) :
    ∃ handle, after.handles selected.base = some handle ∧
      SelectedBase (kernel := kernel) origin ordinal initialObjects path before selected.base handle ∧
      SourcePaths.components path = .ok selected.parts := by
  have source := run.1
  have history := run.2
  unfold SourcePaths.start at source
  split at source
  · cases source
  · rename_i parts components
    split at source
    · rename_i absolute
      have stage : RecordedRun kernel origin ordinal _ before events after
          (Except.ok selected : Result SourcePaths.Started) := ⟨source, history⟩
      obtain ⟨opening, result, last, openedAfter, shape, openedRun, finalRun⟩ := recorded_run_bind_split _ _ stage
      obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq finalRun.1
      cases result with
      | error error => cases same
      | ok base =>
        cases same
        obtain ⟨actual, live, sameDirectory⟩ := source_open_actual_recorded laws origin ordinal _ _ _ openedRun
        have root := lookup.root _ _ _ _ _ _ actual.actual rfl rfl rfl rfl actual.recognized actual.live
        refine ⟨actual.handle, ?_, .inl ⟨by simpa using absolute, root⟩, components⟩
        rw [empty_recorded_handles finalRun.2]
        exact live
    · rename_i relative
      have stage : RecordedRun kernel origin ordinal _ before events after
          (Except.ok selected : Result SourcePaths.Started) := ⟨source, history⟩
      obtain ⟨opening, result, last, openedAfter, shape, openedRun, finalRun⟩ := recorded_run_bind_split _ _ stage
      cases result with
      | error error => cases finalRun.1
      | ok base =>
        obtain ⟨actualOpen, baseLive, sameDirectory⟩ := source_open_actual_recorded laws origin ordinal _ _ _ openedRun
        have cwd := lookup.cwd _ _ _ _ _ _ actualOpen.actual rfl rfl rfl rfl actualOpen.recognized actualOpen.live
        have selectedCwd : actualOpen.handle.object = before.workingDirectory := cwd.trans sameDirectory
        have openCwd := history_directory (recorded_history_erase openedRun.2)
        obtain ⟨spelling, auditing, sourceShape, continued⟩ := Snapshot.returns_call_split finalRun.1
        have remaining := finalRun.2
        rw [sourceShape] at remaining
        obtain ⟨cwdBefore, cwdAfter, leadingCwd, observed, cwdOrigin, afterCwd⟩ := recorded_history_head remaining
        have cwdLive : cwdBefore.handles base = some actualOpen.handle := by
          rw [empty_recorded_handles leadingCwd]
          exact baseLive
        have auditLive : cwdAfter.handles base = some actualOpen.handle := by
          rw [laws.retained _ _ _ _ observed (by simp [RetainsDescriptors])]
          exact cwdLive
        change Returns (match SourcePaths.currentSpelling spelling with
          | .error error => closeResult base (.error error)
          | .ok () => (SourcePaths.checkAncestry base).bind (fun checked => match checked with
            | .error error => closeResult base (.error error)
            | .ok () => Filesystem.Program.pure (.ok (⟨base, parts⟩ : SourcePaths.Started)))).lower
          auditing (.ok selected) at continued
        split at continued
        · have impossible := (Snapshot.closeResult_provenance _ _ (close_result_identity _ _ ▸ continued)).1
          cases impossible
        · rename_i spelled
          have auditingRun : RecordedRun kernel origin (ordinal + opening.length + 1) _ cwdAfter auditing after
              (Except.ok selected : Result SourcePaths.Started) := ⟨continued, afterCwd⟩
          obtain ⟨checkingEvents, checkResult, lastEvents, checkAfter, checkedShape, checkRun, finish⟩ :=
            recorded_run_bind_split _ _ auditingRun
          cases checkResult with
          | error error =>
            have impossible := (Snapshot.closeResult_provenance _ _ (close_result_identity _ _ ▸ finish.1)).1
            cases impossible
          | ok checkedUnit =>
            cases checkedUnit
            obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq finish.1
            cases same
            have stillLive := (borrow_returns (checkAncestry_borrow laws base actualOpen.handle base)
              ⟨checkRun.1, recorded_history_erase checkRun.2⟩ auditLive).1
            refine ⟨actualOpen.handle, ?_, .inr ⟨by simpa using relative, selectedCwd,
              ordinal + opening.length, cwdBefore, cwdAfter, spelling, Nat.le_add_right _ _, cwdOrigin,
              observed, cwdLive, ?_, spelled⟩, components⟩
            · rw [empty_recorded_handles finish.2]
              exact stillLive
            · exact (history_directory (recorded_history_erase leadingCwd)).trans (openCwd.trans selectedCwd.symm)

-- §FS-host-boundary.ownership: The application fold's already-established prefix supplies
-- public labels. Relative selection uses its genuine getcwd position on that SAME raw journal.
theorem source_start_history_public {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram}
    {semantics : NameSemanticsView} {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (lookup : DynamicDataLookupContract kernel semantics initialObjects dataObjects)
    (cwdLookup : WorkingDirectoryContract kernel initialObjects dataObjects)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    (selected : ticks[position]? = some tick) (present : tick.before.actors actor = some engine)
    {leading trailing : List (ActorTick runtime)} {first family : Family}
    (shape : ticks = leading ++ tick :: trailing) (count : leading.length = position)
    (prefixLabels : FamilyJournal runtime initialObjects dataObjects (Population.empty initial)
      first leading tick.before family)
    (path : ByteArray) (ordinal : Nat) {before after : World} {events : List (Request × Reply)}
    {started : SourcePaths.Started}
    (run : RecordedRun kernel (fun index request reply =>
      SourceReturnAt runtime ticks actor index Reply (.filesystem request) reply)
      ordinal (SourcePaths.start path).lower before events after (.ok started))
    (bound : ordinal + events.length ≤ engine.events.length) :
    ∃ handle, after.handles started.base = some handle ∧ family handle.object = none ∧
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

end LeanCage.Host.Kernel.Lowered
