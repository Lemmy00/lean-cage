import FilesystemLoweredBorrowing
import FilesystemCwdFrames

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

-- §FS-host-boundary.ownership: Path audit closes only newly opened handles, including error paths.
theorem publicHandle_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (fd : UInt64) (different : fd ≠ held) :
    BorrowPost kernel held handle (Successful (fun value : UInt64 => value ≠ held)) (SourcePaths.publicHandle fd).lower := by
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
      (SourcePaths.openAt parent name directory).lower := by
  unfold SourcePaths.openAt
  apply borrow_bind (open_fresh_borrow laws held handle _ (.inl rfl))
  intro reply fresh
  split
  · exact .pure True.intro
  · rename_i fd opened
    exact publicHandle_borrow laws held handle fd (fresh fd opened)

theorem sourceIdentity_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (fd : UInt64) :
    BorrowPost kernel held handle (fun _ => True) (SourcePaths.identity fd).lower := by
  unfold SourcePaths.identity
  apply borrow_bind (passive_borrow laws held handle _ (by simp [RetainsDescriptors]))
  intro reply _
  split <;> exact .pure True.intro

theorem releaseParent_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (parent : UInt64) (child : Result UInt64)
    (different : parent ≠ held) (childFresh : Successful (fun fd => fd ≠ held) child) :
    BorrowPost kernel held handle (Successful (fun fd : UInt64 => fd ≠ held)) (SourcePaths.releaseParent parent child).lower := by
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
    BorrowPost kernel held handle (fun _ => True) (SourcePaths.ancestry fuel current root).lower := by
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
    BorrowPost kernel held handle (fun _ => True) (SourcePaths.checkAncestry base).lower := by
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


-- §FS-host-boundary.ownership: The real selected CWD is borrowed through each ancestry probe.
theorem sourceStart_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (path : ByteArray) :
    BorrowPost kernel held handle (Successful (fun value : SourcePaths.Started => value.base ≠ held))
      (SourcePaths.start path).lower := by
  unfold SourcePaths.start
  split
  · exact .pure True.intro
  · split
    · apply borrow_bind (sourceOpenAt_borrow laws held handle _ _ _)
      intro opened fresh
      cases opened with
      | error => exact .pure True.intro
      | ok fd => exact .pure fresh
    · apply borrow_bind (sourceOpenAt_borrow laws held handle _ _ _)
      intro opened fresh
      cases opened with
      | error => exact .pure True.intro
      | ok fd =>
        apply borrow_bind (passive_borrow laws held handle _ (by simp [RetainsDescriptors]))
        intro reply _
        split
        · apply borrow_weaken (close_borrow laws fd held handle _ (Ne.symm fresh))
          intro result shape
          rcases shape with rfl | ⟨_, rfl⟩ <;> trivial
        · apply borrow_bind (checkAncestry_borrow laws held handle fd)
          intro checked _
          cases checked with
          | error =>
            apply borrow_weaken (close_borrow laws fd held handle _ (Ne.symm fresh))
            intro result shape
            rcases shape with rfl | ⟨_, rfl⟩ <;> trivial
          | ok => exact .pure fresh

theorem sourceWalk_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (parent : UInt64) (parts : List ByteArray) (directory : Bool)
    (different : parent ≠ held) :
    BorrowPost kernel held handle (Successful (fun fd : UInt64 => fd ≠ held))
      (SourcePaths.walk parent parts directory).lower := by
  induction parts generalizing parent with
  | nil => exact .pure different
  | cons name rest ih =>
    unfold SourcePaths.walk
    apply borrow_bind (sourceOpenAt_borrow laws held handle _ _ _)
    intro opened fresh
    apply borrow_bind (releaseParent_borrow laws held handle parent opened different fresh)
    intro released freshChild
    cases released with
    | error => exact .pure True.intro
    | ok child => exact ih child freshChild

theorem sourceOpen_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (path : ByteArray) (directory : Bool) :
    BorrowPost kernel held handle (Successful (fun fd : UInt64 => fd ≠ held))
      (SourcePaths.open path directory).lower := by
  unfold SourcePaths.open
  apply borrow_bind (sourceStart_borrow laws held handle path)
  intro selected fresh
  cases selected with
  | error => exact .pure True.intro
  | ok selected => exact sourceWalk_borrow laws held handle selected.base selected.parts directory fresh

-- §FS-host-boundary.snapshot: Caller copying closes only the new FD, on success or failure.
theorem sourceCopyFile_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (path : ByteArray) (limit : Nat) :
    BorrowPost kernel held handle (fun _ => True) (SourcePaths.copyFile path limit).lower := by
  unfold SourcePaths.copyFile
  apply borrow_bind (sourceOpen_borrow laws held handle path false)
  intro opened fresh
  cases opened with
  | error => exact .pure True.intro
  | ok fd =>
    apply borrow_bind (copyOpened_borrow laws held handle fd limit)
    intro result _
    apply borrow_weaken (close_borrow laws fd held handle result (Ne.symm fresh))
    intro _ _
    trivial

theorem actual_cwd_audit_retains_base {kernel : Contract} (laws : DescriptorContract kernel)
    (base : UInt64) (handle : Handle) {before after : World} {events : List (Request × Option Reply)}
    (run : PhysicalPrefix kernel (SourcePaths.checkAncestry base).lower before events after)
    (live : before.handles base = some handle) : after.handles base = some handle :=
  borrow_prefix (checkAncestry_borrow laws base handle base) run live

end LeanCage.Host.Kernel.Lowered
