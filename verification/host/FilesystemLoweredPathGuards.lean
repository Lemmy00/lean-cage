import FilesystemLoweredGuards

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

-- §FS-host-boundary.ownership: The selected root/CWD keeps its actual earlier privacy guard.
theorem source_start_guard_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal : Nat) (path : ByteArray)
    {before after : World} {events : List (Request × Reply)} {selected : SourcePaths.Started}
    (run : RecordedRun kernel origin ordinal (SourcePaths.start path).lower before events after (.ok selected)) :
    Nonempty (GuardedHandle kernel origin (ordinal + events.length) after selected.base) := by
  have source := run.1
  unfold SourcePaths.start at source
  split at source
  · cases source
  · rename_i parts parsed
    split at source
    · have stage : RecordedRun kernel origin ordinal _ before events after
          (Except.ok selected : Result SourcePaths.Started) := ⟨source, run.2⟩
      obtain ⟨opening, result, last, openedAfter, shape, openedRun, finalRun⟩ := recorded_run_bind_split _ _ stage
      obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq finalRun.1
      cases result with
      | error error => cases same
      | ok base =>
        cases same
        obtain ⟨guarded⟩ := source_open_guard_recorded laws origin ordinal _ _ _ openedRun
        refine ⟨⟨guarded.handle, ?_, guarded.guard, ?_⟩⟩
        · rw [empty_recorded_handles finalRun.2]
          exact guarded.live
        · simpa only [shape, List.append_nil] using guarded.earlier
    · have stage : RecordedRun kernel origin ordinal _ before events after
          (Except.ok selected : Result SourcePaths.Started) := ⟨source, run.2⟩
      obtain ⟨opening, result, last, openedAfter, shape, openedRun, finalRun⟩ := recorded_run_bind_split _ _ stage
      cases result with
      | error error => cases finalRun.1
      | ok base =>
        obtain ⟨guarded⟩ := source_open_guard_recorded laws origin ordinal _ _ _ openedRun
        obtain ⟨spelling, auditing, sourceShape, continued⟩ := Snapshot.returns_call_split finalRun.1
        have remaining := finalRun.2
        rw [sourceShape] at remaining
        obtain ⟨cwdBefore, cwdAfter, leadingCwd, observed, cwdOrigin, afterCwd⟩ := recorded_history_head remaining
        have cwdLive : cwdBefore.handles base = some guarded.handle := by
          rw [empty_recorded_handles leadingCwd]
          exact guarded.live
        have auditLive : cwdAfter.handles base = some guarded.handle := by
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
        · have auditingRun : RecordedRun kernel origin (ordinal + opening.length + 1) _ cwdAfter auditing after
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
            have stillLive := (borrow_returns (checkAncestry_borrow laws base guarded.handle base)
              ⟨checkRun.1, recorded_history_erase checkRun.2⟩ auditLive).1
            refine ⟨⟨guarded.handle, ?_, guarded.guard, ?_⟩⟩
            · rw [empty_recorded_handles finish.2]
              exact stillLive
            · have early := guarded.earlier
              rw [shape, sourceShape]
              simp only [List.length_append, List.length_cons]
              omega

-- §FS-host-boundary.ownership: A retained walk result is still its own last guarded raw lease.
theorem source_walk_guard_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal : Nat) (parent : UInt64) (parts : List ByteArray) (directory : Bool)
    {before after : World} {events : List (Request × Reply)} {fd : UInt64}
    (initial : GuardedHandle kernel origin ordinal before parent)
    (run : RecordedRun kernel origin ordinal (SourcePaths.walk parent parts directory).lower before events after (.ok fd)) :
    Nonempty (GuardedHandle kernel origin (ordinal + events.length) after fd) := by
  induction parts generalizing ordinal parent before events with
  | nil =>
    obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq run.1
    cases same
    exact ⟨⟨initial.handle, by rw [empty_recorded_handles run.2]; exact initial.live,
      initial.guard, by simpa using initial.earlier⟩⟩
  | cons name rest ih =>
    have source := run.1
    unfold SourcePaths.walk at source
    have stage : RecordedRun kernel origin ordinal _ before events after (.ok fd : Result UInt64) := ⟨source, run.2⟩
    obtain ⟨opening, opened, last, openedAfter, shape, openedRun, afterOpen⟩ := recorded_run_bind_split _ _ stage
    have oldParent := (borrow_returns (sourceOpenAt_borrow laws parent initial.handle _ _ _)
      ⟨openedRun.1, recorded_history_erase openedRun.2⟩ initial.live).1
    obtain ⟨releasing, released, following, releasedAfter, releaseShape, releasedRun, remaining⟩ :=
      recorded_run_bind_split _ _ afterOpen
    cases released with
    | error => cases remaining.1
    | ok child =>
      cases opened with
      | error error =>
        obtain ⟨same, _⟩ := Snapshot.releaseParent_source parent (.error error) (release_parent_identity _ _ ▸ releasedRun.1)
        cases same
      | ok actualChild =>
        obtain ⟨same, closed⟩ := Snapshot.releaseParent_source parent (.ok actualChild) (release_parent_identity _ _ ▸ releasedRun.1)
        cases same
        obtain ⟨guarded⟩ := source_open_guard_recorded laws origin ordinal _ _ _ openedRun
        have different : parent ≠ child := Ne.symm (borrow_returns
          (sourceOpenAt_borrow laws parent initial.handle _ _ _)
          ⟨openedRun.1, recorded_history_erase openedRun.2⟩ initial.live).2
        have childLive := (borrow_returns
          (close_borrow laws parent child guarded.handle (.ok child) (Ne.symm different))
          ⟨(close_result_identity _ _).symm ▸ closed, recorded_history_erase releasedRun.2⟩ guarded.live).1
        have nextInitial : GuardedHandle kernel origin (ordinal + opening.length + releasing.length)
            releasedAfter child := ⟨guarded.handle, childLive, guarded.guard, by
              have early := guarded.earlier; omega⟩
        obtain ⟨result⟩ := ih _ _ nextInitial remaining
        refine ⟨⟨result.handle, result.live, result.guard, ?_⟩⟩
        simpa only [shape, releaseShape, List.length_append, Nat.add_assoc] using result.earlier

-- §FS-host-boundary.snapshot: Caller file lookup returns a live, historically guarded descriptor.
theorem source_path_guard_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal : Nat) (path : ByteArray) (directory : Bool)
    {before after : World} {events : List (Request × Reply)} {fd : UInt64}
    (run : RecordedRun kernel origin ordinal (SourcePaths.open path directory).lower before events after (.ok fd)) :
    Nonempty (GuardedHandle kernel origin (ordinal + events.length) after fd) := by
  have source := run.1
  unfold SourcePaths.open at source
  have stage : RecordedRun kernel origin ordinal _ before events after (.ok fd : Result UInt64) := ⟨source, run.2⟩
  obtain ⟨starting, selected, following, startAfter, shape, startRun, rest⟩ := recorded_run_bind_split _ _ stage
  cases selected with
  | error error => cases rest.1
  | ok selected =>
    obtain ⟨guarded⟩ := source_start_guard_recorded laws origin ordinal _ startRun
    obtain ⟨result⟩ := source_walk_guard_recorded laws origin (ordinal + starting.length)
      selected.base selected.parts directory guarded rest
    refine ⟨⟨result.handle, result.live, result.guard, ?_⟩⟩
    simpa only [shape, List.length_append, Nat.add_assoc] using result.earlier


end LeanCage.Host.Kernel.Lowered
