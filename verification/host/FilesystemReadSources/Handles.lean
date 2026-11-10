import FilesystemReadSources.Source

namespace LeanCage.Host.Kernel
open Filesystem

structure PublicGuard (kernel : Contract) (origin : FilesystemOrigin) (fd : UInt64) (handle : Handle) where
  ordinal : Nat
  before : World
  after : World
  reply : Reply
  actual : kernel.step before {op := .getAttribute, first := fd, second := 1, left := PrivateNames.attributeName}
    (some reply) after
  sampled : origin ordinal {op := .getAttribute, first := fd, second := 1, left := PrivateNames.attributeName}
    reply before after
  live : before.handles fd = some handle
  accepted : nativeError reply = true ∧ errorNumber reply = 61
  absent : before.attributes handle.object PrivateNames.attributeName = none

structure GuardedHandle (kernel : Contract) (origin : FilesystemOrigin) (limit : Nat) (world : World) (fd : UInt64) where
  handle : Handle
  live : world.handles fd = some handle
  guard : PublicGuard kernel origin fd handle
  earlier : guard.ordinal < limit

theorem source_open_guard_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal : Nat) (parent : UInt64) (name : ByteArray) (directory : Bool)
    {before after : World} {events : List (Request × Reply)} {fd : UInt64}
    (run : RecordedRun kernel origin ordinal (SourcePaths.openAt parent name directory) before events after (.ok fd)) :
    Nonempty (GuardedHandle kernel origin (ordinal + events.length) after fd) := by
  obtain ⟨openReply, guardReply, shape, recognized, failed, absent⟩ := Snapshot.sourceOpenAt_source _ _ _ run.1
  have history := run.2
  rw [shape] at history
  obtain ⟨actual, opened, leading, opening, openOrigin, rest⟩ := recorded_history_head history
  obtain ⟨_, handle, live⟩ := laws.allocated_fresh _ _ _ _ _ opening (.inl rfl) recognized
  obtain ⟨checking, checked, between, guard, guardOrigin, final⟩ := recorded_history_head rest
  have checkedLive : checking.handles fd = some handle := by
    rw [random_history_handles (recorded_history_erase between) (by intro event member; cases member)]
    exact live
  have missing := kernel.attribute_absent _ _ _ _ handle guard rfl rfl checkedLive failed absent
  have finalLive : after.handles fd = some handle := by
    rw [random_history_handles (recorded_history_erase final) (by intro event member; cases member),
      (kernel.attribute_frame _ _ _ _ guard rfl).1]
    exact checkedLive
  exact ⟨⟨handle, finalLive, ⟨ordinal + 1, checking, checked, guardReply,
    guard, guardOrigin, checkedLive, ⟨failed, absent⟩, missing⟩, by
      rw [shape]
      simp only [List.length_cons, List.length_nil]
      omega⟩⟩

theorem empty_recorded_handles {kernel : Contract} {origin : FilesystemOrigin} {ordinal : Nat}
    {before after : World} (history : RecordedHistory kernel origin ordinal before [] after) :
    after.handles = before.handles :=
  random_history_handles (recorded_history_erase history) (by intro event impossible; cases impossible)

-- §FS-host-boundary.ownership: The selected root/CWD keeps its actual earlier privacy guard.
theorem source_start_guard_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal : Nat) (path : ByteArray)
    {before after : World} {events : List (Request × Reply)} {selected : SourcePaths.Started}
    (run : RecordedRun kernel origin ordinal (SourcePaths.start path) before events after (.ok selected)) :
    Nonempty (GuardedHandle kernel origin (ordinal + events.length) after selected.base) := by
  have source := run.1
  unfold SourcePaths.start at source
  split at source
  · cases source
  · split at source
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
        dsimp only [Filesystem.Program.bind] at continued
        split at continued
        · have impossible := (Snapshot.closeResult_provenance _ _ continued).1
          cases impossible
        · have auditingRun : RecordedRun kernel origin (ordinal + opening.length + 1) _ cwdAfter auditing after
              (Except.ok selected : Result SourcePaths.Started) := ⟨continued, afterCwd⟩
          obtain ⟨checkingEvents, checkResult, lastEvents, checkAfter, checkedShape, checkRun, finish⟩ :=
            recorded_run_bind_split _ _ auditingRun
          cases checkResult with
          | error error =>
            have impossible := (Snapshot.closeResult_provenance _ _ finish.1).1
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
    (run : RecordedRun kernel origin ordinal (SourcePaths.walk parent parts directory) before events after (.ok fd)) :
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
        obtain ⟨same, _⟩ := Snapshot.releaseParent_source parent (.error error) releasedRun.1
        cases same
      | ok actualChild =>
        obtain ⟨same, closed⟩ := Snapshot.releaseParent_source parent (.ok actualChild) releasedRun.1
        cases same
        obtain ⟨guarded⟩ := source_open_guard_recorded laws origin ordinal _ _ _ openedRun
        obtain ⟨openReply, _, openShape, recognized, _, _⟩ := Snapshot.sourceOpenAt_source _ _ _ openedRun.1
        have openingHistory := openedRun.2
        rw [openShape] at openingHistory
        obtain ⟨actual, openedWorld, leading, operation, openOrigin, tail⟩ := recorded_history_head openingHistory
        have actualParent : actual.handles parent = some initial.handle := by
          rw [empty_recorded_handles leading]
          exact initial.live
        obtain ⟨vacant, allocated, live⟩ := laws.allocated_fresh _ _ _ _ _ operation (.inl rfl) recognized
        have different : parent ≠ child := by
          intro same
          subst child
          rw [actualParent] at vacant
          cases vacant
        have childLive := (borrow_returns
          (close_borrow laws parent child guarded.handle (.ok child) (Ne.symm different))
          ⟨closed, recorded_history_erase releasedRun.2⟩ guarded.live).1
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
    (run : RecordedRun kernel origin ordinal (SourcePaths.open path directory) before events after (.ok fd)) :
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

end LeanCage.Host.Kernel
