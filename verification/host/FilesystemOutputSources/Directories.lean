import FilesystemOutputSources.Bootstrap

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

theorem close_effect_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (fd : UInt64) (different : fd ≠ held) :
    BorrowPost kernel held handle (fun _ => True) (Filesystem.Program.effect {op := .close, first := fd}).lower := by
  apply BorrowPost.call
  · intro before after observed actual live
    rw [laws.close_other _ _ _ _ _ actual rfl (Ne.symm different)]
    exact live
  · intro before after reply actual live
    exact .pure True.intro

theorem directory_descend_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (create : Bool)
    (current : Directories.Opened) (names : List ByteArray) (different : current.fd ≠ held) :
    BorrowPost kernel held handle (Successful (fun opened : Directories.Opened => opened.fd ≠ held))
      (Directories.descend uid create current names).lower := by
  induction names generalizing current with
  | nil => exact .pure different
  | cons name rest ih =>
    unfold Directories.descend
    apply borrow_bind (public_at_borrow laws held handle _ _ _ _)
    intro opened fresh
    apply borrow_bind (close_borrow laws current.fd held handle opened (Ne.symm different))
    intro closed shape
    cases closed with
    | error error =>
      cases opened with
      | error => exact .pure True.intro
      | ok next =>
        apply borrow_weaken (close_borrow laws next.fd held handle _ (Ne.symm fresh))
        intro result shape
        rcases shape with rfl | ⟨_, rfl⟩ <;> trivial
    | ok next =>
      rcases shape with same | ⟨error, impossible⟩
      · rw [← same] at fresh
        exact ih next fresh
      · cases impossible

theorem directory_parent_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (path : ByteArray) (create : Bool) :
    BorrowPost kernel held handle (Successful (fun parent : Directories.Parent => parent.directory.fd ≠ held))
      (Directories.parent path create).lower := by
  unfold Directories.parent
  apply borrow_bind (sourceStart_borrow laws held handle _)
  intro selected fresh
  cases selected with
  | error => exact .pure True.intro
  | ok selected =>
    dsimp only
    split
    · split
      · apply borrow_weaken (close_borrow laws selected.base held handle _ (Ne.symm fresh))
        intro result shape
        rcases shape with rfl | ⟨_, rfl⟩ <;> trivial
      · apply borrow_bind (passive_borrow laws held handle _ (by simp [RetainsDescriptors]))
        intro uid _
        split
        · apply borrow_weaken (close_borrow laws selected.base held handle _ (Ne.symm fresh))
          intro result shape
          rcases shape with rfl | ⟨_, rfl⟩ <;> trivial
        · apply borrow_bind (directoryInspect_borrow laws held handle _ selected.base fresh)
          intro base freshBase
          cases base with
          | error => exact .pure True.intro
          | ok base =>
            apply borrow_bind (directory_descend_borrow laws held handle _ _ base _ freshBase)
            intro found freshFound
            cases found with
            | error => exact .pure True.intro
            | ok parent => exact .pure freshFound
    · apply borrow_weaken (close_borrow laws selected.base held handle _ (Ne.symm fresh))
      intro result shape
      rcases shape with rfl | ⟨_, rfl⟩ <;> trivial

theorem temporary_parent_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) :
    BorrowPost kernel held handle (Successful (fun area : Directories.Opened × String × Nat => area.1.fd ≠ held))
      Directories.temporaryParent.lower := by
  unfold Directories.temporaryParent
  apply borrow_bind (passive_borrow laws held handle _ (by simp [RetainsDescriptors]))
  intro uid _
  split
  · exact .pure True.intro
  · apply borrow_bind (directoryOpen_borrow laws held handle _ _ _)
    intro root fresh
    cases root with
    | error => exact .pure True.intro
    | ok root => exact .pure fresh

-- §FS-host-boundary.ownership: Both actual run-directory FDs are newly allocated before
-- they are stored for later image/validator cleanup; failed setup closes only those FDs.
theorem run_create_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) :
    BorrowPost kernel held handle (Successful (fun run : RunDirectory.Owned =>
      run.directory.fd ≠ held ∧ run.container.fd ≠ held)) RunDirectory.create.lower := by
  unfold RunDirectory.create
  apply borrow_bind (temporary_parent_borrow laws held handle)
  intro area freshArea
  cases area with
  | error => exact .pure True.intro
  | ok area =>
    rcases area with ⟨container, areaPath, uid⟩
    apply borrow_bind (directoryChild_borrow laws held handle _ _ _)
    intro child freshChild
    cases child with
    | error =>
      apply borrow_weaken (close_borrow laws container.fd held handle _ (Ne.symm freshArea))
      intro result shape
      rcases shape with rfl | ⟨_, rfl⟩ <;> trivial
    | ok child =>
      apply borrow_bind (passive_borrow laws held handle _ (by simp [RetainsDescriptors]))
      intro marked _
      split
      · apply borrow_bind (close_effect_borrow laws held handle child.directory.fd freshChild)
        intro _ _
        apply borrow_bind (passive_borrow laws held handle _ (by simp [RetainsDescriptors]))
        intro _ _
        apply borrow_weaken (close_borrow laws container.fd held handle _ (Ne.symm freshArea))
        intro result shape
        rcases shape with rfl | ⟨_, rfl⟩ <;> trivial
      · split
        · apply borrow_bind (close_effect_borrow laws held handle child.directory.fd freshChild)
          intro _ _
          apply borrow_weaken (close_borrow laws container.fd held handle _ (Ne.symm freshArea))
          intro result shape
          rcases shape with rfl | ⟨_, rfl⟩ <;> trivial
        · dsimp only
          split
          · apply borrow_bind (close_effect_borrow laws held handle child.directory.fd freshChild)
            intro _ _
            apply borrow_weaken (close_borrow laws container.fd held handle _ (Ne.symm freshArea))
            intro result shape
            rcases shape with rfl | ⟨_, rfl⟩ <;> trivial
          · exact .pure ⟨freshChild, freshArea⟩

theorem run_release_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (run : RunDirectory.Owned)
    (fresh : run.directory.fd ≠ held ∧ run.container.fd ≠ held) :
    BorrowPost kernel held handle (fun _ => True) (Validation.releaseDirectory run).lower := by
  unfold Validation.releaseDirectory
  apply borrow_bind (close_effect_borrow laws held handle _ fresh.1)
  intro _ _
  apply borrow_bind (close_effect_borrow laws held handle _ fresh.2)
  intro _ _
  exact .pure True.intro

theorem run_cleanup_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (run : RunDirectory.Owned)
    (fresh : run.directory.fd ≠ held ∧ run.container.fd ≠ held) :
    BorrowPost kernel held handle (fun _ => True) (RunDirectory.cleanup run).lower := by
  unfold RunDirectory.cleanup
  apply borrow_bind (pre := fun _ => True)
  · apply borrow_forIn
    intro name state
    apply borrow_bind (passive_borrow laws held handle _ (by simp [RetainsDescriptors]))
    intro _ _
    exact .pure True.intro
  · intro _ _
    apply borrow_bind (close_effect_borrow laws held handle _ fresh.1)
    intro _ _
    apply borrow_bind (passive_borrow laws held handle _ (by simp [RetainsDescriptors]))
    intro _ _
    apply borrow_bind (close_effect_borrow laws held handle _ fresh.2)
    intro _ _
    exact .pure True.intro

theorem image_writer_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) {α : Type} {fd : UInt64} {program : Filesystem.Program α}
    (source : Image.WriteProgram fd program) : BorrowPost kernel held handle (fun _ => True) program.lower := by
  induction source with
  | pure => exact .pure True.intro
  | @call request next allowed following ih =>
    exact passive_call laws held handle (by rw [allowed.1]; simp [RetainsDescriptors]) ih

theorem image_create_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (runFd : UInt64) (bundle : Validation.Bundle) (overlay : List Image.Entry) :
    BorrowPost kernel held handle (fun _ => True) (Image.create runFd bundle overlay).lower := by
  unfold Image.create
  split
  · exact .pure True.intro
  · apply borrow_bind (identified_copy_borrow laws held handle _ _ _)
    intro base _
    cases base with
    | error => exact .pure True.intro
    | ok base =>
      apply borrow_bind (open_fresh_borrow laws held handle _ (.inl rfl))
      intro reply fresh
      split
      · exact .pure True.intro
      · rename_i fd recognized
        apply borrow_bind (image_writer_borrow laws held handle (Image.content_scoped _ _ _))
        intro result _
        apply borrow_weaken (close_borrow laws fd held handle result (Ne.symm (fresh fd recognized)))
        intro _ _; trivial

end LeanCage.Host.Kernel.Lowered
