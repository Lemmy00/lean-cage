import FilesystemDirectoryHandles
import FilesystemReadSources

namespace LeanCage.Host.Kernel
open Filesystem

private theorem concurrent_bind_split {kernel : Contract} {α β : Type}
    (program : Filesystem.Program α) (next : α → Filesystem.Program β)
    {before after : World} {events : List (Request × Reply)} {result : β}
    (run : ConcurrentRun kernel (program.bind next) before events after result) :
    ∃ initial value final middle, events = initial ++ final ∧
      ConcurrentRun kernel program before initial middle value ∧
      ConcurrentRun kernel (next value) middle final after result := by
  obtain ⟨initial, value, final, first, last, shape⟩ := Snapshot.returns_bind_split _ _ run.1
  have history := run.2
  rw [shape] at history
  obtain ⟨middle, leading, ending⟩ := history_split initial final history
  exact ⟨initial, value, final, middle, shape, ⟨first, leading⟩, last, ending⟩

theorem ensured_directory_handle {kernel : Contract} (laws : DescriptorContract kernel)
    (uid : Nat) (parent : UInt64) (name : ByteArray) {before after : World}
    {events : List (Request × Reply)} {opened : Directories.Opened}
    (run : ConcurrentRun kernel (Directories.ensureAt uid parent name) before events after (.ok opened)) :
    ∃ handle, after.handles opened.fd = some handle ∧ handle.rawOwned = true := by
  obtain ⟨made, opening, shape, recognized, observation⟩ := Publication.ensureAt_source _ _ _ run.1
  have history := run.2
  rw [shape] at history
  obtain ⟨actual, created, leading, operation, final⟩ := history_head history
  exact directory_observation_handle laws uid parent name observation final

private theorem public_handle_keeps_self {kernel : Contract} (laws : DescriptorContract kernel)
    (fd : UInt64) (handle : Handle) {before after : World} {events : List (Request × Reply)} {value : UInt64}
    (run : ConcurrentRun kernel (SourcePaths.publicHandle fd) before events after (.ok value))
    (live : before.handles fd = some handle) : value = fd ∧ after.handles fd = some handle := by
  have source := run.1
  unfold SourcePaths.publicHandle at source
  obtain ⟨reply, last, shape, following⟩ := Snapshot.returns_call_split source
  split at following
  · obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq following
    cases same
    have history := run.2
    rw [shape] at history
    obtain ⟨actual, checked, initial, operation, final⟩ := history_head history
    refine ⟨rfl, ?_⟩
    rw [random_history_handles final (by intro event impossible; cases impossible),
      laws.retained _ _ _ _ operation (by simp [RetainsDescriptors]),
      random_history_handles initial (by intro event impossible; cases impossible)]
    exact live
  · have impossible := (Snapshot.closeResult_provenance _ _ following).1
    cases impossible

theorem public_at_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (parent : UInt64) (name : ByteArray) (create : Bool) :
    BorrowPost kernel held handle (Successful (fun opened : Directories.Opened => opened.fd ≠ held))
      (Directories.publicAt uid parent name create) := by
  cases create <;> unfold Directories.publicAt
  all_goals simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals
    apply borrow_bind
    · first | exact directoryOpen_borrow laws held handle _ _ _ | exact directoryEnsure_borrow laws held handle _ _ _
    · intro opened fresh
      cases opened with
      | error error => exact .pure True.intro
      | ok opened =>
        apply borrow_bind (publicHandle_borrow laws held handle opened.fd fresh)
        intro allowed permitted
        cases allowed with
        | error error => exact .pure True.intro
        | ok fd => exact .pure permitted

theorem public_at_handle {kernel : Contract} (laws : DescriptorContract kernel)
    (uid : Nat) (parent : UInt64) (name : ByteArray) (create : Bool)
    {before after : World} {events : List (Request × Reply)} {opened : Directories.Opened}
    (run : ConcurrentRun kernel (Directories.publicAt uid parent name create) before events after (.ok opened)) :
    ∃ handle, after.handles opened.fd = some handle ∧ handle.rawOwned = true := by
  have source := run
  cases create <;> unfold Directories.publicAt at source
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at source
  all_goals
    obtain ⟨opening, result, rest, middle, shape, openingRun, following⟩ := concurrent_bind_split _ _ source
    cases result with
    | error error => cases following.1
    | ok directory =>
      have openingHandle : ∃ handle, middle.handles directory.fd = some handle ∧ handle.rawOwned = true := by
        first
        | exact directory_observation_handle laws uid parent name (Retrieval.directoryOpening_source _ _ _ openingRun.1)
            openingRun.2
        | exact ensured_directory_handle laws uid parent name openingRun
      obtain ⟨handle, live, raw⟩ := openingHandle
      obtain ⟨checking, result, last, checked, _, checkedRun, final⟩ := concurrent_bind_split _ _ following
      cases result with
      | error error => cases final.1
      | ok fd =>
        obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final.1
        cases same
        obtain ⟨rfl, checkedLive⟩ := public_handle_keeps_self laws directory.fd handle checkedRun live
        refine ⟨handle, ?_, raw⟩
        rw [random_history_handles final.2 (by intro event impossible; cases impossible)]
        exact checkedLive

-- §FS-host-boundary.ownership: Parent traversal retains each next FD before closing the old one.
theorem descend_handle {kernel : Contract} (laws : DescriptorContract kernel)
    (uid : Nat) (create : Bool) (current : Directories.Opened) (names : List ByteArray)
    (handle : Handle) {before after : World} {events : List (Request × Reply)} {opened : Directories.Opened}
    (run : ConcurrentRun kernel (Directories.descend uid create current names) before events after (.ok opened))
    (live : before.handles current.fd = some handle) (raw : handle.rawOwned = true) :
    ∃ next, after.handles opened.fd = some next ∧ next.rawOwned = true := by
  induction names generalizing current before events handle with
  | nil =>
    obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq run.1
    cases same
    exact ⟨handle, by rw [random_history_handles run.2 (by intro event impossible; cases impossible)]; exact live, raw⟩
  | cons name rest ih =>
    have source := run
    unfold Directories.descend at source
    obtain ⟨opening, result, following, middle, shape, openedRun, afterOpen⟩ := concurrent_bind_split _ _ source
    obtain ⟨closing, closed, ending, closedWorld, closeShape, closedRun, afterClose⟩ := concurrent_bind_split _ _ afterOpen
    cases closed with
    | error error =>
      cases result with
      | error original => cases afterClose.1
      | ok next => have impossible := (Snapshot.closeResult_provenance _ _ afterClose.1).1; cases impossible
    | ok next =>
      have same := (Snapshot.closeResult_provenance _ _ closedRun.1).1
      cases same
      obtain ⟨childHandle, childLive, childRaw⟩ := public_at_handle laws uid current.fd name create openedRun
      have different := (borrow_returns (public_at_borrow laws current.fd handle uid current.fd name create)
        openedRun live).2
      have nextLive := (borrow_returns (close_borrow laws current.fd next.fd childHandle (.ok next)
        different) closedRun childLive).1
      exact ih next childHandle afterClose nextLive childRaw

private theorem history_recorded_true {kernel : Contract} {before after : World}
    {events : List (Request × Reply)} (history : History kernel before events after) (ordinal : Nat) :
    RecordedHistory kernel (fun _ _ _ _ _ => True) ordinal before events after := by
  induction history generalizing ordinal with
  | nil => exact .nil _ _
  | cons operation tail ih => exact .cons operation True.intro (ih (ordinal + 1))
  | environment interference tail ih => exact .environment interference (ih ordinal)

private theorem guarded_handle_raw {kernel : Contract} (laws : DescriptorContract kernel)
    {origin : FilesystemOrigin} {limit : Nat} {world : World} {fd : UInt64}
    (source : GuardedHandle kernel origin limit world fd) : source.handle.rawOwned = true := by
  apply laws.after_raw _ _ _ _ source.guard.actual fd source.handle
  rw [(kernel.attribute_frame _ _ _ _ source.guard.actual rfl).1]
  exact source.guard.live

theorem inspected_handle {kernel : Contract} (laws : DescriptorContract kernel) (uid : Nat) (fd : UInt64)
    (handle : Handle) {before after : World} {events : List (Request × Reply)} {opened : Directories.Opened}
    (run : ConcurrentRun kernel (Directories.inspect uid fd) before events after (.ok opened))
    (live : before.handles fd = some handle) : opened.fd = fd ∧ after.handles fd = some handle := by
  obtain ⟨same, reply, shape, parsed, trusted⟩ := Retrieval.directoryInspection_source _ _ run.1
  have history := run.2
  rw [shape] at history
  obtain ⟨actual, checked, initial, operation, final⟩ := history_head history
  refine ⟨same, ?_⟩
  rw [random_history_handles final (by intro event impossible; cases impossible),
    laws.retained _ _ _ _ operation (by simp [RetainsDescriptors]),
    random_history_handles initial (by intro event impossible; cases impossible)]
  exact live

-- §FS-host-boundary.ownership: The actual public parent result carries a genuine retained raw FD.
theorem parent_handle {kernel : Contract} (laws : DescriptorContract kernel) (path : ByteArray) (create : Bool)
    {before after : World} {events : List (Request × Reply)} {parent : Directories.Parent}
    (run : ConcurrentRun kernel (Directories.parent path create) before events after (.ok parent)) :
    ∃ handle, after.handles parent.directory.fd = some handle ∧ handle.rawOwned = true := by
  have source := run.1
  unfold Directories.parent at source
  obtain ⟨selecting, result, rest, selectedSource, afterSelect, shape⟩ := Snapshot.returns_bind_split _ _ source
  have history := run.2
  rw [shape] at history
  obtain ⟨selectedWorld, selectingHistory, remaining⟩ := history_split selecting rest history
  cases result with
  | error error => cases afterSelect
  | ok selected =>
    obtain ⟨base⟩ := source_start_guard_recorded laws (fun _ _ _ _ _ => True) 0 path
      ⟨selectedSource, history_recorded_true selectingHistory 0⟩
    have baseRaw := guarded_handle_raw laws base
    dsimp only at afterSelect
    split at afterSelect
    · rename_i name named
      split at afterSelect
      · have impossible := (Snapshot.closeResult_provenance _ _ afterSelect).1; cases impossible
      · obtain ⟨identity, later, identityShape, afterIdentity⟩ := Snapshot.returns_call_split afterSelect
        rw [identityShape] at remaining
        obtain ⟨identityBefore, identityAfter, initial, operation, afterUid⟩ := history_head remaining
        have identityLive : identityBefore.handles selected.base = some base.handle := by
          rw [random_history_handles initial (by intro event impossible; cases impossible)]
          exact base.live
        have afterIdentityLive : identityAfter.handles selected.base = some base.handle := by
          rw [laws.retained _ _ _ _ operation (by simp [RetainsDescriptors])]
          exact identityLive
        dsimp only [Filesystem.Program.bind] at afterIdentity
        split at afterIdentity
        · have impossible := (Snapshot.closeResult_provenance _ _ afterIdentity).1; cases impossible
        · obtain ⟨inspecting, result, descending, inspected, afterInspect, inspectShape⟩ :=
            Snapshot.returns_bind_split _ _ afterIdentity
          rw [inspectShape] at afterUid
          obtain ⟨inspectedWorld, inspectingHistory, descendingHistory⟩ := history_split inspecting descending afterUid
          cases result with
          | error error => cases afterInspect
          | ok inspectedDirectory =>
            obtain ⟨sameFd, inspectedLive⟩ := inspected_handle laws _ _ _ ⟨inspected, inspectingHistory⟩ afterIdentityLive
            have atDirectory : inspectedWorld.handles inspectedDirectory.fd = some base.handle := by
              rw [sameFd]
              exact inspectedLive
            obtain ⟨descending, result, last, descended, final, descendShape⟩ :=
              Snapshot.returns_bind_split _ _ afterInspect
            obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
            cases result with
            | error error => cases same
            | ok directory =>
              cases same
              rw [descendShape] at descendingHistory
              obtain ⟨handle, live, raw⟩ := descend_handle laws _ _ _ _ base.handle
                ⟨descended, by simpa only [List.append_nil] using descendingHistory⟩ atDirectory baseRaw
              exact ⟨handle, live, raw⟩
    · have impossible := (Snapshot.closeResult_provenance _ _ afterSelect).1; cases impossible

end LeanCage.Host.Kernel
