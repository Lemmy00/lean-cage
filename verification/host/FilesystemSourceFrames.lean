import FilesystemBorrowing
import ImageProofs.Writes

namespace LeanCage.Host.Kernel
open Filesystem

private theorem passive_call {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) {α : Type} {request : Request}
    {next : Reply → Filesystem.Program α} {post : α → Prop}
    (passive : RetainsDescriptors request.op)
    (following : ∀ reply, BorrowPost kernel held handle post (next reply)) :
    BorrowPost kernel held handle post (.call request next) := by
  apply BorrowPost.call
  · intro before after observed operation live
    rw [laws.retained _ _ _ _ operation passive]
    exact live
  · intro before after reply operation live
    exact following reply

-- §FS-host-boundary.snapshot: Actual read/stat/hash calls retain every pre-existing FD reference.
theorem readLoop_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (fuel : Nat) (fd : UInt64) (limit : Nat) (bytes : ByteArray) :
    BorrowPost kernel held handle (fun _ => True) (readLoop fuel fd limit bytes) := by
  induction fuel generalizing bytes with
  | zero => exact .pure True.intro
  | succ fuel ih =>
    unfold readLoop
    split
    · exact .pure True.intro
    · apply passive_call laws held handle (by simp [RetainsDescriptors])
      intro reply
      split
      · exact .pure True.intro
      · split
        · exact .pure True.intro
        · split
          · exact .pure True.intro
          · split
            · exact .pure True.intro
            · exact ih _

theorem copyOpened_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (fd : UInt64) (limit : Nat) :
    BorrowPost kernel held handle (fun _ => True) (copyOpened fd limit) := by
  unfold copyOpened
  apply passive_call laws held handle (by simp [RetainsDescriptors])
  intro reply
  split
  · exact .pure True.intro
  · split
    · exact .pure True.intro
    · apply borrow_bind (readLoop_borrow laws held handle _ _ _ _)
      intro result _
      cases result with
      | error => exact .pure True.intro
      | ok bytes =>
        apply passive_call laws held handle (by simp [RetainsDescriptors])
        intro finalReply
        split
        · exact .pure True.intro
        · split <;> exact .pure True.intro

theorem copyAt_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (parent : UInt64) (path : ByteArray) (limit : Nat) :
    BorrowPost kernel held handle (fun _ => True) (copyAt parent path limit) := by
  unfold copyAt
  split
  · exact .pure True.intro
  · apply borrow_bind (open_fresh_borrow laws held handle _ (.inl rfl))
    intro reply fresh
    split
    · exact .pure True.intro
    · rename_i fd recognized
      apply borrow_bind (copyOpened_borrow laws held handle fd limit)
      intro result _
      apply borrow_weaken (close_borrow laws fd held handle result (Ne.symm (fresh fd recognized)))
      intro _ _
      trivial

theorem hash_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (bytes : ByteArray) :
    BorrowPost kernel held handle (fun _ => True) (Filesystem.hash bytes) := by
  unfold Filesystem.hash
  apply passive_call laws held handle (by simp [RetainsDescriptors])
  intro reply
  split <;> exact .pure True.intro

-- §FS-host-boundary.ownership: An opened directory is a new descriptor, even for the same object.
theorem directoryInspect_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (fd : UInt64) (different : fd ≠ held) :
    BorrowPost kernel held handle (Successful (fun opened : Directories.Opened => opened.fd ≠ held))
      (Directories.inspect uid fd) := by
  unfold Directories.inspect
  apply passive_call laws held handle (by simp [RetainsDescriptors])
  intro reply
  split
  · apply borrow_weaken (close_borrow laws fd held handle _ (Ne.symm different))
    intro result shape
    rcases shape with rfl | ⟨_, rfl⟩ <;> trivial
  · split
    · exact .pure different
    · apply borrow_weaken (close_borrow laws fd held handle _ (Ne.symm different))
      intro result shape
      rcases shape with rfl | ⟨_, rfl⟩ <;> trivial

theorem directoryOpen_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (parent : UInt64) (name : ByteArray) :
    BorrowPost kernel held handle (Successful (fun opened : Directories.Opened => opened.fd ≠ held))
      (Directories.openAt uid parent name) := by
  unfold Directories.openAt
  apply borrow_bind (open_fresh_borrow laws held handle _ (.inl rfl))
  intro reply fresh
  split
  · exact .pure True.intro
  · rename_i fd recognized
    exact directoryInspect_borrow laws held handle uid fd (fresh fd recognized)

theorem directoryRandom_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (fuel count : Nat) (bytes : ByteArray) :
    BorrowPost kernel held handle (fun _ => True) (Directories.randomBytes fuel count bytes) := by
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
      (Directories.newChild uid parent prefixName) := by
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
      stage.directory.fd ≠ held ∧ stage.container.fd ≠ held)) (Directories.fresh parent) := by
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

-- §FS-host-boundary.ownership: The caller's retained public parent survives the full stage setup.
theorem actual_fresh_retains_parent {kernel : Contract} (laws : DescriptorContract kernel)
    (parent : Directories.Parent) (handle : Handle)
    {before after : World} {events : List (Request × Reply)} {stage : Directories.Fresh}
    (run : ConcurrentRun kernel (Directories.fresh parent) before events after (.ok stage))
    (live : before.handles parent.directory.fd = some handle) :
    after.handles parent.directory.fd = some handle ∧ stage.directory.fd ≠ parent.directory.fd ∧
      stage.container.fd ≠ parent.directory.fd :=
  borrow_returns (directoryFresh_borrow laws parent.directory.fd handle parent) run live

-- §FS-host-boundary.acceptance: This frame includes errors, partial prefixes and lost replies.
theorem actual_child_retains_parent {kernel : Contract} (laws : DescriptorContract kernel)
    (uid : Nat) (parent : UInt64) (prefixName : String) (handle : Handle)
    {before after : World} {events : List (Request × Option Reply)}
    (run : PhysicalPrefix kernel (Directories.newChild uid parent prefixName) before events after)
    (live : before.handles parent = some handle) : after.handles parent = some handle :=
  borrow_prefix (directoryChild_borrow laws parent handle uid parent prefixName) run live

theorem identified_copy_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (bundle : Validation.Bundle) (name : String) (limit : Nat) :
    BorrowPost kernel held handle (fun _ => True) (Validation.copyIdentified bundle name limit) := by
  unfold Validation.copyIdentified
  split
  · split
    · apply borrow_bind (pre := fun _ => True)
      · unfold readBounded
        exact borrow_bind (copyAt_borrow laws held handle _ _ _) (fun _ _ => .pure True.intro)
      · intro result _
        cases result with
        | error => exact .pure True.intro
        | ok bytes =>
          apply borrow_bind (hash_borrow laws held handle _)
          intro digest _
          cases digest with
          | error => exact .pure True.intro
          | ok bytes => dsimp only; split <;> exact .pure True.intro
    · exact .pure True.intro
  · exact .pure True.intro

theorem image_write_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) {α : Type} {fd : UInt64} {program : Filesystem.Program α}
    (source : Image.WriteProgram fd program) : BorrowPost kernel held handle (fun _ => True) program := by
  induction source with
  | pure => exact .pure True.intro
  | @call request next allowed following ih =>
    exact passive_call laws held handle (by rw [allowed.1]; simp [RetainsDescriptors]) ih

-- §FS-host-boundary.ownership: Image creation keeps the run/container raw references until cleanup.
theorem image_create_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (runFd : UInt64) (bundle : Validation.Bundle) (overlay : List Image.Entry) :
    BorrowPost kernel held handle (fun _ => True) (Image.create runFd bundle overlay) := by
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
        apply borrow_bind (image_write_borrow laws held handle (Image.content_scoped _ _ _))
        intro result _
        apply borrow_weaken (close_borrow laws fd held handle result (Ne.symm (fresh fd recognized)))
        intro _ _; trivial

theorem actual_image_retains_directory {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (runFd : UInt64) (bundle : Validation.Bundle) (overlay : List Image.Entry)
    {before after : World} {events : List (Request × Option Reply)}
    (run : PhysicalPrefix kernel (Image.create runFd bundle overlay) before events after)
    (live : before.handles held = some handle) : after.handles held = some handle :=
  borrow_prefix (image_create_borrow laws held handle runFd bundle overlay) run live

end LeanCage.Host.Kernel
