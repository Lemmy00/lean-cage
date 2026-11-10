import FilesystemLoweredDirectories
import FilesystemLoweredPathGuards

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

-- §FS-host-boundary.ownership: Every added guard/probe and failed-open close retains the
-- separate held directory. A successful result has a freshly allocated descriptor.
theorem directoryInspect_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (fd : UInt64) (different : fd ≠ held) :
    BorrowPost kernel held handle (Successful (fun opened : Directories.Opened => opened.fd ≠ held))
      (Directories.inspect uid fd).lower := by
  rw [directory_inspect_identity]
  exact Kernel.directoryInspect_borrow laws held handle uid fd different

theorem directoryOpen_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (parent : UInt64) (name : ByteArray) :
    BorrowPost kernel held handle (Successful (fun opened : Directories.Opened => opened.fd ≠ held))
      (Directories.openAt uid parent name).lower := by
  unfold Directories.openAt
  change BorrowPost kernel held handle _ ((Filesystem.Program.effect {
    op := .openAt, first := parent, second := directoryFlags, left := name }).bind _).lower
  apply borrow_bind (open_fresh_borrow laws held handle _ (.inl rfl))
  intro reply fresh
  split
  · exact .pure True.intro
  · rename_i fd recognized
    exact directoryInspect_borrow laws held handle uid fd (fresh fd recognized)

theorem directoryEnsure_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (parent : UInt64) (name : ByteArray) :
    BorrowPost kernel held handle (Successful (fun opened : Directories.Opened => opened.fd ≠ held))
      (Directories.ensureAt uid parent name).lower := by
  unfold Directories.ensureAt
  apply borrow_bind (passive_borrow laws held handle _ (by simp [RetainsDescriptors]))
  intro reply irrelevant
  split
  · exact directoryOpen_borrow laws held handle _ _ _
  · split
    · exact directoryOpen_borrow laws held handle _ _ _
    · exact .pure True.intro

theorem public_at_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (parent : UInt64) (name : ByteArray) (create : Bool) :
    BorrowPost kernel held handle (Successful (fun opened : Directories.Opened => opened.fd ≠ held))
      (Directories.publicAt uid parent name create).lower := by
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

theorem directoryRandom_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (fuel count : Nat) (bytes : ByteArray) :
    BorrowPost kernel held handle (fun _ => True) (Directories.randomBytes fuel count bytes).lower := by
  induction fuel generalizing bytes with
  | zero => exact .pure True.intro
  | succ fuel ih =>
    unfold Directories.randomBytes
    split
    · exact .pure True.intro
    · split
      · exact .pure True.intro
      · apply passive_call laws held handle (by simp [RetainsDescriptors])
        intro reply
        split
        · exact .pure True.intro
        · split
          · exact .pure True.intro
          · exact ih _

theorem directoryChild_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (parent : UInt64) (prefixName : String) :
    BorrowPost kernel held handle (Successful (fun child : Directories.NewDirectory => child.directory.fd ≠ held))
      (Directories.newChild uid parent prefixName).lower := by
  unfold Directories.newChild
  apply borrow_bind (directoryRandom_borrow laws held handle _ _ _)
  intro random _
  cases random with
  | error => exact .pure True.intro
  | ok bytes =>
    dsimp only
    split
    · exact .pure True.intro
    · apply passive_call laws held handle (by simp [RetainsDescriptors])
      intro reply
      dsimp only [Filesystem.Program.bind]
      split
      · exact .pure True.intro
      · apply borrow_bind (directoryOpen_borrow laws held handle _ _ _)
        intro opened fresh
        cases opened with
        | error => exact .pure True.intro
        | ok directory =>
          dsimp only at fresh ⊢
          split
          · apply borrow_weaken (close_borrow laws directory.fd held handle _ (Ne.symm fresh))
            intro result shape
            rcases shape with rfl | ⟨_, rfl⟩ <;> trivial
          · exact .pure fresh

theorem directoryFresh_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (parent : Directories.Parent) :
    BorrowPost kernel held handle (Successful (fun stage : Directories.Fresh =>
      stage.directory.fd ≠ held ∧ stage.container.fd ≠ held)) (Directories.fresh parent).lower := by
  unfold Directories.fresh
  apply borrow_bind (directoryOpen_borrow laws held handle _ _ _)
  intro container freshContainer
  cases container with
  | error => exact .pure True.intro
  | ok container =>
    apply borrow_bind (directoryChild_borrow laws held handle _ _ _)
    intro child freshChild
    cases child with
    | error =>
      apply borrow_weaken (close_borrow laws container.fd held handle _ (Ne.symm freshContainer))
      intro result shape
      rcases shape with rfl | ⟨_, rfl⟩ <;> trivial
    | ok child => exact .pure ⟨freshChild, freshContainer⟩

end LeanCage.Host.Kernel.Lowered
