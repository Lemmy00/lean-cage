import FilesystemSourceFrames
import PublicationMarkerProofs

namespace LeanCage.Host.Kernel
open Filesystem

private theorem passive_call {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) {α : Type} {request : Request}
    {next : Reply → Filesystem.Program α} {post : α → Prop}
    (passive : RetainsDescriptors request.op)
    (following : ∀ reply, BorrowPost kernel held handle post (next reply)) :
    BorrowPost kernel held handle post (.call request next) := by
  apply BorrowPost.call
  · intro before after observed actual live
    rw [laws.retained _ _ _ _ actual passive]
    exact live
  · intro before after reply actual live
    exact following reply

theorem writeLoop_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (fuel : Nat) (fd : UInt64) (bytes : ByteArray) (offset : Nat) :
    BorrowPost kernel held handle (fun _ => True) (writeLoop fuel fd bytes offset) := by
  induction fuel generalizing offset with
  | zero => exact .pure True.intro
  | succ fuel ih =>
    unfold writeLoop
    split
    · exact .pure True.intro
    · apply passive_call laws held handle (by simp [RetainsDescriptors])
      intro reply
      repeat' first | exact .pure True.intro | exact ih _ | split

-- §FS-host-boundary.ownership: Exclusive writers close only their new FD, never a live parent.
theorem writeNew_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (parent : UInt64) (name bytes : ByteArray) (mode : UInt64) :
    BorrowPost kernel held handle (fun _ => True) (writeNew parent name bytes mode) := by
  unfold writeNew
  split
  · exact .pure True.intro
  · apply borrow_bind (open_fresh_borrow laws held handle _ (.inl rfl))
    intro reply fresh
    split
    · exact .pure True.intro
    · rename_i fd recognized
      apply borrow_bind (writeLoop_borrow laws held handle _ _ _ _)
      intro result _
      apply borrow_weaken (close_borrow laws fd held handle result (Ne.symm (fresh fd recognized)))
      intro _ _
      trivial

theorem directoryEnsure_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (parent : UInt64) (name : ByteArray) :
    BorrowPost kernel held handle (Successful (fun opened : Directories.Opened => opened.fd ≠ held))
      (Directories.ensureAt uid parent name) := by
  unfold Directories.ensureAt
  apply passive_call laws held handle (by simp [RetainsDescriptors])
  intro reply
  dsimp only [Filesystem.Program.bind]
  split
  · exact directoryOpen_borrow laws held handle _ _ _
  · split
    · exact directoryOpen_borrow laws held handle _ _ _
    · exact .pure True.intro

theorem publication_under_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) {α : Type} (uid : Nat) (fd : UInt64) (names : List String) (create : Bool)
    (action : UInt64 → Filesystem.Program (Result α))
    (permitted : ∀ fd, BorrowPost kernel held handle (fun _ => True) (action fd)) :
    BorrowPost kernel held handle (fun _ => True) (Publication.under uid fd names create action) := by
  induction names generalizing fd with
  | nil => exact permitted fd
  | cons name rest ih =>
    unfold Publication.under
    split
    · exact .pure True.intro
    · cases create <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · apply borrow_bind (directoryOpen_borrow laws held handle _ _ _)
        intro opened fresh
        cases opened with
        | error => exact .pure True.intro
        | ok child =>
          apply borrow_bind (ih child.fd)
          intro result _
          apply borrow_weaken (close_borrow laws child.fd held handle result (Ne.symm fresh))
          intro _ _
          trivial
      · apply borrow_bind (directoryEnsure_borrow laws held handle _ _ _)
        intro opened fresh
        cases opened with
        | error => exact .pure True.intro
        | ok child =>
          apply borrow_bind (ih child.fd)
          intro result _
          apply borrow_weaken (close_borrow laws child.fd held handle result (Ne.symm fresh))
          intro _ _
          trivial

theorem publication_write_relative_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (root : UInt64) (file : Artifacts.ValidatedFile) :
    BorrowPost kernel held handle (fun _ => True) (Publication.writeRelative uid root file) := by
  unfold Publication.writeRelative
  dsimp only
  split
  · exact publication_under_borrow laws held handle _ _ _ _ _ (fun _ => writeNew_borrow laws held handle _ _ _ _)
  · exact .pure True.intro

theorem borrow_forIn {kernel : Contract} (held : UInt64) (handle : Handle) {α β : Type}
    (items : List α) (initial : β) (body : α → β → Filesystem.Program (ForInStep β))
    (permitted : ∀ item state, BorrowPost kernel held handle (fun _ => True) (body item state)) :
    BorrowPost kernel held handle (fun _ => True) (forIn items initial body) := by
  induction items generalizing initial with
  | nil => exact .pure True.intro
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply borrow_bind (permitted item initial)
    intro step _
    cases step with
    | done => exact .pure True.intro
    | yield state => exact ih state

theorem publication_directories_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (root : UInt64) (paths : List Artifacts.ExportPath) :
    BorrowPost kernel held handle (fun _ => True) (Publication.directories uid root paths) := by
  unfold Publication.directories
  apply borrow_bind (pre := fun _ => True)
  · apply borrow_forIn
    intro path state
    apply borrow_bind (publication_under_borrow laws held handle _ _ _ _ _ (fun _ => .pure True.intro))
    intro made _
    cases made <;> exact .pure True.intro
  · intro state _
    dsimp only
    split <;> exact .pure True.intro

theorem publication_exports_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (stage : UInt64) (input : Publication.Input) :
    BorrowPost kernel held handle (fun _ => True) (Publication.exports uid stage input) := by
  unfold Publication.exports
  apply passive_call laws held handle (by simp [RetainsDescriptors])
  intro made
  dsimp only [Filesystem.Program.bind]
  split
  · exact .pure True.intro
  · apply borrow_bind (directoryOpen_borrow laws held handle _ _ _)
    intro opened fresh
    cases opened with
    | error => exact .pure True.intro
    | ok root =>
      apply borrow_bind (pre := fun _ => True)
      · apply borrow_bind (publication_directories_borrow laws held handle _ _ _)
        intro made _
        cases made with
        | error => exact .pure True.intro
        | ok made =>
          apply borrow_bind (pre := fun _ => True)
          · apply borrow_forIn
            intro file state
            apply borrow_bind (publication_write_relative_borrow laws held handle _ _ _)
            intro written _
            cases written <;> exact .pure True.intro
          · intro state _
            split <;> exact .pure True.intro
      · intro filled _
        apply borrow_weaken (close_borrow laws root.fd held handle filled (Ne.symm fresh))
        intro _ _
        trivial

theorem publication_fill_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (stage : UInt64) (input : Publication.Input) (json wire : ByteArray) :
    BorrowPost kernel held handle (fun _ => True) (Publication.fill uid stage input json wire) := by
  unfold Publication.fill
  repeat' first | exact .pure True.intro | (dsimp only; split) | split
  all_goals
    apply borrow_bind (pre := fun _ => True)
    · apply borrow_forIn
      intro pair state
      apply borrow_bind (writeNew_borrow laws held handle _ _ _ _)
      intro written _
      cases written <;> exact .pure True.intro
    · intro state _
      split
      · exact .pure True.intro
      · exact publication_exports_borrow laws held handle _ _ _

-- §FS-host-boundary.publication: Key copying closes only its fresh FD, preserving stage custody.
theorem authentication_key_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (bundle : Validation.Bundle) :
    BorrowPost kernel held handle (fun _ => True) (Publication.authenticationKey bundle) := by
  unfold Publication.authenticationKey
  split
  · split
    · apply passive_call laws held handle (by simp [RetainsDescriptors])
      intro uid
      dsimp only [Filesystem.Program.bind]
      split
      · exact .pure True.intro
      · apply borrow_bind (open_fresh_borrow laws held handle _ (.inl rfl))
        intro reply fresh
        split
        · rename_i fd recognized
          apply passive_call laws held handle (by simp [RetainsDescriptors])
          intro privateReply
          dsimp only [Filesystem.Program.bind]
          split
          · apply borrow_weaken (close_borrow laws fd held handle _ (Ne.symm (fresh fd recognized)))
            intro _ _
            trivial
          · apply borrow_bind (pre := fun _ => True)
            · apply borrow_bind (copyOpened_borrow laws held handle _ _)
              intro copied _
              apply borrow_weaken (close_borrow laws fd held handle copied (Ne.symm (fresh fd recognized)))
              intro _ _
              trivial
            · intro copied _
              cases copied with
              | error => exact .pure True.intro
              | ok copied =>
                dsimp only
                split
                · exact .pure True.intro
                · apply borrow_bind (hash_borrow laws held handle _)
                  intro digest _
                  cases digest with
                  | error => exact .pure True.intro
                  | ok digest => dsimp only; split <;> exact .pure True.intro
        · exact .pure True.intro
    · exact .pure True.intro
  · exact .pure True.intro

theorem authentication_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (bundle : Validation.Bundle) (wire : ByteArray) :
    BorrowPost kernel held handle (fun _ => True) (Publication.authenticate bundle wire) := by
  unfold Publication.authenticate
  split
  · exact .pure True.intro
  · apply borrow_bind (authentication_key_borrow laws held handle _)
    intro key _
    cases key with
    | error => exact .pure True.intro
    | ok key =>
      apply passive_call laws held handle (by simp [RetainsDescriptors])
      intro reply
      dsimp only [Filesystem.Program.bind]
      split <;> exact .pure True.intro

-- §FS-host-boundary.publication: Actual hash/authentication/fill/marker order keeps this raw lease.
theorem publication_prepare_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (bundle : Validation.Bundle) (input : Publication.Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) (parent : Directories.Parent) (stage : Directories.Fresh) :
    BorrowPost kernel held handle (fun _ => True)
      (Publication.prepare bundle input target stdoutHash stderrHash parent stage) := by
  unfold Publication.prepare
  apply borrow_bind (hash_borrow laws held handle _)
  intro digest _
  cases digest with
  | error => exact .pure True.intro
  | ok digest =>
    dsimp only
    split
    · split
      · exact .pure True.intro
      · apply borrow_bind (authentication_borrow laws held handle _ _)
        intro tag _
        cases tag with
        | error => exact .pure True.intro
        | ok tag =>
          apply borrow_bind (publication_fill_borrow laws held handle _ _ _ _ _)
          intro filled _
          cases filled with
          | error => exact .pure True.intro
          | ok filled =>
            apply passive_call laws held handle (by simp [RetainsDescriptors])
            intro reply
            dsimp only [Filesystem.Program.bind]
            split <;> exact .pure True.intro
    · exact .pure True.intro

-- §FS-host-boundary.acceptance: A lost marker cannot switch the retained publication object.
theorem actual_prepare_retains_stage {kernel : Contract} (laws : DescriptorContract kernel)
    (bundle : Validation.Bundle) (input : Publication.Input) (target stdoutHash stderrHash : ByteArray)
    (parent : Directories.Parent) (stage : Directories.Fresh) (handle : Handle)
    {before after : World} {events : List (Request × Option Reply)}
    (source : PhysicalPrefix kernel (Publication.prepare bundle input target stdoutHash stderrHash parent stage)
      before events after) (live : before.handles stage.directory.fd = some handle) :
    after.handles stage.directory.fd = some handle :=
  borrow_prefix (publication_prepare_borrow laws stage.directory.fd handle _ _ _ _ _ _ _) source live

end LeanCage.Host.Kernel
