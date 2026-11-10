import FilesystemProjection
import FilesystemSourceFrames
import FilesystemLookups
import FilesystemRecording

namespace LeanCage.Host.Kernel
open Filesystem

theorem history_directory {kernel : Contract} {before after : World} {events : List (Request × Reply)}
    (history : History kernel before events after) : after.workingDirectory = before.workingDirectory := by
  induction history with
  | nil => rfl
  | cons actual tail ih => exact ih.trans (kernel.step_directory _ _ _ _ actual)
  | environment interference tail ih => exact ih.trans (kernel.interference_directory _ _ interference)

private theorem split_component_bytes (bytes acc : List UInt8)
    (noNul : ∀ byte ∈ bytes, byte ≠ 0) (checkedAcc : ∀ byte ∈ acc, byte ≠ 0 ∧ byte ≠ 47) :
    ∀ part ∈ List.splitOnPPrepend (· == (47 : UInt8)) bytes acc,
      ∀ byte ∈ part, byte ≠ 0 ∧ byte ≠ 47 := by
  induction bytes generalizing acc with
  | nil =>
    intro part member byte occurs
    have same : part = acc.reverse := List.mem_singleton.mp member
    subst part
    exact checkedAcc byte (by simpa using occurs)
  | cons first rest ih =>
    rw [List.splitOnPPrepend_cons_eq_ite]
    split
    · intro part member byte occurs
      rcases List.mem_cons.mp member with rfl | later
      · exact checkedAcc byte (by simpa using occurs)
      · exact ih [] (fun byte member => noNul byte (by simp [member]))
          (by intro byte member; cases member) part later byte occurs
    · rename_i notSeparator
      apply ih
      · intro byte member; exact noNul byte (by simp [member])
      · intro byte member
        rcases List.mem_cons.mp member with rfl | old
        · exact ⟨noNul byte (by simp), by simpa using notSeparator⟩
        · exact checkedAcc byte old

-- §FS-host-boundary.ownership: Splitting the real checked bytes produces single safe components.
theorem source_components_are_components (path : ByteArray) (parts : List ByteArray)
    (accepted : SourcePaths.components path = .ok parts) :
    ∀ part ∈ parts, Directories.component part = true ∧ PrivateNames.reservedBytes part = false := by
  obtain ⟨_, valid, parsed, checked⟩ := Snapshot.sourceComponents_fields path parts accepted
  have noNul : ∀ byte ∈ path.data.toList, byte ≠ 0 := by
    have fields : path.size ≤ 4095 ∧ (0 : UInt8) ∉ path.data.toList := by
      simpa [rawPathValid, List.contains_iff_mem] using valid
    have absent := fields.2
    intro byte member same
    subst byte
    exact absent member
  intro part member
  have bounded := (checked part member).1
  have publicName := (checked part member).2
  rw [parsed] at member
  obtain ⟨bytes, source, rfl⟩ := List.mem_map.mp member
  obtain ⟨splitMember, nonempty⟩ := List.mem_filter.mp source
  have good := split_component_bytes path.data.toList [] noNul (by intro byte impossible; cases impossible)
    bytes splitMember
  have notNul : (0 : UInt8) ∉ bytes := by intro occurs; exact (good 0 occurs).1 rfl
  have notSlash : (47 : UInt8) ∉ bytes := by intro occurs; exact (good 47 occurs).2 rfl
  constructor
  · have nonempty : bytes ≠ [] := by simpa using nonempty
    cases bytes with
    | nil => exact False.elim (nonempty rfl)
    | cons first rest =>
      have bytesNonempty : ByteArray.mk (first :: rest).toArray ≠ .empty := by
        intro same
        have impossible := congrArg (fun value : ByteArray => value.data.toList) same
        simp at impossible
      simpa [Directories.component, ByteArray.isEmpty, Array.contains_toList,
        List.contains_iff_mem, notNul, notSlash] using ⟨bytesNonempty, bounded⟩
  · exact publicName

-- §FS-host-boundary.ownership: Path audit closes only newly opened handles, including error paths.
theorem publicHandle_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (fd : UInt64) (different : fd ≠ held) :
    BorrowPost kernel held handle (Successful (fun value : UInt64 => value ≠ held)) (SourcePaths.publicHandle fd) := by
  unfold SourcePaths.publicHandle
  apply borrow_bind (passive_borrow laws held handle _ (by simp [RetainsDescriptors]))
  intro reply _
  split
  · exact .pure different
  · apply borrow_weaken (close_borrow laws fd held handle _ (Ne.symm different))
    intro result shape
    rcases shape with rfl | ⟨_, rfl⟩ <;> trivial

theorem sourceOpenAt_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (parent : UInt64) (name : ByteArray) (directory : Bool) :
    BorrowPost kernel held handle (Successful (fun value : UInt64 => value ≠ held))
      (SourcePaths.openAt parent name directory) := by
  unfold SourcePaths.openAt
  apply borrow_bind (open_fresh_borrow laws held handle _ (.inl rfl))
  intro reply fresh
  split
  · exact .pure True.intro
  · rename_i fd opened
    exact publicHandle_borrow laws held handle fd (fresh fd opened)

theorem sourceIdentity_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (fd : UInt64) :
    BorrowPost kernel held handle (fun _ => True) (SourcePaths.identity fd) := by
  unfold SourcePaths.identity
  apply borrow_bind (passive_borrow laws held handle _ (by simp [RetainsDescriptors]))
  intro reply _
  split <;> exact .pure True.intro

theorem releaseParent_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (parent : UInt64) (child : Result UInt64)
    (different : parent ≠ held) (childFresh : Successful (fun fd => fd ≠ held) child) :
    BorrowPost kernel held handle (Successful (fun fd : UInt64 => fd ≠ held)) (SourcePaths.releaseParent parent child) := by
  unfold SourcePaths.releaseParent
  apply borrow_bind (close_borrow laws parent held handle child (Ne.symm different))
  intro released shape
  cases released with
  | ok fd =>
    rcases shape with same | ⟨error, impossible⟩
    · rw [← same] at childFresh
      exact .pure childFresh
    · cases impossible
  | error error =>
    cases child with
    | error => exact .pure True.intro
    | ok fd =>
      apply borrow_weaken (close_borrow laws fd held handle _ (Ne.symm childFresh))
      intro result shape
      rcases shape with rfl | ⟨_, rfl⟩ <;> trivial

theorem ancestry_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (fuel : Nat) (current : UInt64) (root : ByteArray) (different : current ≠ held) :
    BorrowPost kernel held handle (fun _ => True) (SourcePaths.ancestry fuel current root) := by
  induction fuel generalizing current with
  | zero =>
    apply borrow_weaken (close_borrow laws current held handle _ (Ne.symm different))
    intro _ _; trivial
  | succ fuel ih =>
    unfold SourcePaths.ancestry
    apply borrow_bind (sourceIdentity_borrow laws held handle _)
    intro observed _
    cases observed with
    | error =>
      apply borrow_weaken (close_borrow laws current held handle _ (Ne.symm different))
      intro _ _; trivial
    | ok value =>
      dsimp only
      split
      · apply borrow_weaken (close_borrow laws current held handle _ (Ne.symm different))
        intro _ _; trivial
      · apply borrow_bind (sourceOpenAt_borrow laws held handle _ _ _)
        intro parent fresh
        apply borrow_bind (releaseParent_borrow laws held handle current parent different fresh)
        intro released stillFresh
        cases released with
        | error => exact .pure True.intro
        | ok parent => exact ih parent stillFresh

-- §FS-host-boundary.ownership: The real CWD anchor stays open during the duplicate ancestry audit.
theorem checkAncestry_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (base : UInt64) :
    BorrowPost kernel held handle (fun _ => True) (SourcePaths.checkAncestry base) := by
  unfold SourcePaths.checkAncestry
  apply borrow_bind (sourceOpenAt_borrow laws held handle _ _ _)
  intro opened fresh
  cases opened with
  | error => exact .pure True.intro
  | ok root =>
    apply borrow_bind (pre := fun _ => True)
    · apply borrow_bind (sourceIdentity_borrow laws held handle root)
      intro result _
      apply borrow_weaken (close_borrow laws root held handle result (Ne.symm fresh))
      intro _ _; trivial
    · intro observed _
      cases observed with
      | error => exact .pure True.intro
      | ok value =>
        apply borrow_bind (sourceOpenAt_borrow laws held handle _ _ _)
        intro duplicate duplicateFresh
        cases duplicate with
        | error => exact .pure True.intro
        | ok duplicate => exact ancestry_borrow laws held handle 4096 duplicate value duplicateFresh

theorem actual_cwd_audit_retains_base {kernel : Contract} (laws : DescriptorContract kernel)
    (base : UInt64) (handle : Handle) {before after : World} {events : List (Request × Option Reply)}
    (run : PhysicalPrefix kernel (SourcePaths.checkAncestry base) before events after)
    (live : before.handles base = some handle) : after.handles base = some handle :=
  borrow_prefix (checkAncestry_borrow laws base handle base) run live

-- §FS-host-boundary.ownership: Open and private-tag lookup concern the same retained object.
theorem source_open_handle_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal : Nat) (parent : UInt64) (name : ByteArray) (directory : Bool)
    {before after : World} {events : List (Request × Reply)} {fd : UInt64}
    (source : Returns (SourcePaths.openAt parent name directory) events (.ok fd))
    (history : RecordedHistory kernel origin ordinal before events after) :
    ∃ (handle : Handle) (actual opened checking checked : World) (openReply guardReply : Reply),
      RecordedHistory kernel origin ordinal before [] actual ∧
      kernel.step actual {op := .openAt, first := parent, second := (if directory then directoryFlags else readFlags), left := name} (some openReply) opened ∧
      origin ordinal {op := .openAt, first := parent, second := (if directory then directoryFlags else readFlags), left := name} openReply actual opened ∧
      descriptor openReply = some fd ∧ opened.handles fd = some handle ∧
      RecordedHistory kernel origin (ordinal + 1) opened [] checking ∧
      kernel.step checking {op := .getAttribute, first := fd, second := 1, left := PrivateNames.attributeName} (some guardReply) checked ∧
      origin (ordinal + 1) {op := .getAttribute, first := fd, second := 1, left := PrivateNames.attributeName} guardReply checking checked ∧
      checking.handles fd = some handle ∧ checking.attributes handle.object PrivateNames.attributeName = none ∧
      RecordedHistory kernel origin (ordinal + 2) checked [] after ∧ after.handles fd = some handle := by
  obtain ⟨openReply, guardReply, shape, recognized, failed, absent⟩ := Snapshot.sourceOpenAt_source _ _ _ source
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
  exact ⟨handle, actual, opened, checking, checked, openReply, guardReply,
    leading, opening, openOrigin, recognized, live, between, guard, guardOrigin,
    checkedLive, missing, by simpa only [Nat.add_assoc] using final, finalLive⟩

theorem source_open_handle {kernel : Contract} (laws : DescriptorContract kernel)
    (parent : UInt64) (name : ByteArray) (directory : Bool)
    {before after : World} {events : List (Request × Reply)} {fd : UInt64}
    (run : ConcurrentRun kernel (SourcePaths.openAt parent name directory) before events after (.ok fd)) :
    ∃ (handle : Handle) (actual opened checking checked : World) (openReply guardReply : Reply),
      History kernel before [] actual ∧
      kernel.step actual {op := .openAt, first := parent, second := (if directory then directoryFlags else readFlags), left := name} (some openReply) opened ∧
      descriptor openReply = some fd ∧ opened.handles fd = some handle ∧
      History kernel opened [] checking ∧
      kernel.step checking {op := .getAttribute, first := fd, second := 1, left := PrivateNames.attributeName} (some guardReply) checked ∧
      checking.handles fd = some handle ∧ checking.attributes handle.object PrivateNames.attributeName = none ∧
      History kernel checked [] after ∧ after.handles fd = some handle := by
  obtain ⟨openReply, guardReply, shape, recognized, failed, absent⟩ := Snapshot.sourceOpenAt_source _ _ _ run.1
  have history := run.2
  rw [shape] at history
  obtain ⟨actual, opened, leading, opening, rest⟩ := history_head history
  obtain ⟨_, handle, live⟩ := laws.allocated_fresh _ _ _ _ _ opening (.inl rfl) recognized
  obtain ⟨checking, checked, between, guard, final⟩ := history_head rest
  have checkedLive : checking.handles fd = some handle := by
    rw [random_history_handles between (by intro event member; cases member)]
    exact live
  have missing := kernel.attribute_absent _ _ _ _ handle guard rfl rfl checkedLive failed absent
  have finalLive : after.handles fd = some handle := by
    rw [random_history_handles final (by intro event member; cases member),
      (kernel.attribute_frame _ _ _ _ guard rfl).1]
    exact checkedLive
  exact ⟨handle, actual, opened, checking, checked, openReply, guardReply,
    leading, opening, recognized, live, between, guard, checkedLive, missing, final, finalLive⟩

def SelectedBase {kernel : Contract} (origin : FilesystemOrigin) (ordinal : Nat)
    (initialObjects : ObjectId → Bool) (path : ByteArray) (before : World) (fd : UInt64) (handle : Handle) : Prop :=
  (path[0]! = 47 ∧ initialObjects handle.object = true) ∨
  (path[0]! ≠ 47 ∧ handle.object = before.workingDirectory ∧
    ∃ index checking checked reply, ordinal ≤ index ∧
      origin index {op := .workingDirectory} reply checking checked ∧
      kernel.step checking {op := .workingDirectory} (some reply) checked ∧
      checking.handles fd = some handle ∧ checking.workingDirectory = handle.object ∧
      SourcePaths.currentSpelling reply = .ok ())

-- §FS-host-boundary.ownership: Relative selection names the retained inherited CWD, not its
-- spelling.
theorem source_start_handle_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal : Nat)
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (lookup : DataLookupContract kernel initialObjects dataObjects) (path : ByteArray)
    {before after : World} {events : List (Request × Reply)} {selected : SourcePaths.Started}
    (run : RecordedRun kernel origin ordinal (SourcePaths.start path) before events after (.ok selected)) :
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
      have stage : RecordedRun kernel origin ordinal _ before events after (Except.ok selected : Result SourcePaths.Started) := ⟨source, history⟩
      obtain ⟨opening, result, last, openedAfter, shape, openedRun, finalRun⟩ := recorded_run_bind_split _ _ stage
      obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq finalRun.1
      cases result with
      | error error => cases same
      | ok base =>
        cases same
        obtain ⟨handle, actual, opened, checking, checked, reply, guardReply,
          leading, operation, _, recognized, live, _, _, _, _, _, _, finalLive⟩ :=
            source_open_handle_recorded laws origin ordinal _ _ _ openedRun.1 openedRun.2
        have root := lookup.root _ _ _ _ _ _ operation rfl rfl rfl rfl recognized live
        refine ⟨handle, ?_, .inl ⟨by simpa using absolute, root⟩, components⟩
        rw [random_history_handles (recorded_history_erase finalRun.2) (by intro event member; cases member)]
        exact finalLive
    · rename_i relative
      have stage : RecordedRun kernel origin ordinal _ before events after (Except.ok selected : Result SourcePaths.Started) := ⟨source, history⟩
      obtain ⟨opening, result, last, openedAfter, shape, openedRun, finalRun⟩ := recorded_run_bind_split _ _ stage
      cases result with
      | error error => cases finalRun.1
      | ok base =>
        obtain ⟨handle, actual, opened, checking, checked, reply, guardReply,
          leading, operation, _, recognized, live, _, _, _, _, _, _, baseLive⟩ :=
            source_open_handle_recorded laws origin ordinal _ _ _ openedRun.1 openedRun.2
        have cwd := lookup.cwd _ _ _ _ _ _ operation rfl rfl rfl rfl recognized live
        have selectedCwd : handle.object = before.workingDirectory := cwd.trans (history_directory (recorded_history_erase leading))
        have openCwd := history_directory (recorded_history_erase openedRun.2)
        obtain ⟨spelling, auditing, sourceShape, continued⟩ := Snapshot.returns_call_split finalRun.1
        have remaining := finalRun.2
        rw [sourceShape] at remaining
        obtain ⟨cwdBefore, cwdAfter, leadingCwd, observed, cwdOrigin, afterCwd⟩ := recorded_history_head remaining
        have cwdLive : cwdBefore.handles base = some handle := by
          rw [random_history_handles (recorded_history_erase leadingCwd) (by intro event member; cases member)]
          exact baseLive
        have auditLive : cwdAfter.handles base = some handle := by
          rw [laws.retained _ _ _ _ observed (by simp [RetainsDescriptors])]
          exact cwdLive
        dsimp only [Filesystem.Program.bind] at continued
        split at continued
        · have impossible := (Snapshot.closeResult_provenance _ _ continued).1
          cases impossible
        · rename_i spellingUnit spelled
          have auditingRun : RecordedRun kernel origin (ordinal + opening.length + 1) _ cwdAfter auditing after (Except.ok selected : Result SourcePaths.Started) := ⟨continued, afterCwd⟩
          obtain ⟨checkingEvents, checkResult, lastEvents, checkAfter, _, checkRun, finish⟩ :=
            recorded_run_bind_split _ _ auditingRun
          cases checkResult with
          | error error =>
            have impossible := (Snapshot.closeResult_provenance _ _ finish.1).1
            cases impossible
          | ok checkedUnit =>
            cases checkedUnit
            obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq finish.1
            cases same
            have stillLive := (borrow_returns (checkAncestry_borrow laws base handle base) ⟨checkRun.1, recorded_history_erase checkRun.2⟩ auditLive).1
            refine ⟨handle, ?_, .inr ⟨by simpa using relative, selectedCwd, ordinal + opening.length, cwdBefore, cwdAfter, spelling,
              Nat.le_add_right _ _, cwdOrigin, observed, cwdLive, ?_, spelled⟩, components⟩
            · rw [random_history_handles (recorded_history_erase finish.2) (by intro event member; cases member)]
              exact stillLive
            · exact (history_directory (recorded_history_erase leadingCwd)).trans (openCwd.trans selectedCwd.symm)

end LeanCage.Host.Kernel
