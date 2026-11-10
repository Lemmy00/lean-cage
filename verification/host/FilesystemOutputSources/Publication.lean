import FilesystemOutputSources.Directories
import PublicationProofs.CleanupSource

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

private theorem loop_unit_borrow {kernel : Contract} (held : UInt64) (handle : Handle)
    {α β : Type} (items : List α) (initial : β) (body : α → β → Filesystem.Program (ForInStep β))
    (permitted : ∀ item state, BorrowPost kernel held handle (fun _ => True) (body item state).lower) :
    BorrowPost kernel held handle (fun _ => True)
      ((forIn items initial body).bind (fun _ => Filesystem.Program.pure ())).lower :=
  borrow_bind (borrow_forIn held handle items initial body permitted) (fun _ _ => .pure True.intro)

theorem outcome_identify_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (outcome : Outcome) :
    BorrowPost kernel held handle (fun _ => True) outcome.identify.lower := by
  unfold Outcome.identify
  split
  · exact .pure True.intro
  · apply borrow_bind (hash_borrow laws held handle _)
    intro stdout _
    cases stdout with
    | error => exact .pure True.intro
    | ok stdout =>
      apply borrow_bind (hash_borrow laws held handle _)
      intro stderr _
      exact .pure True.intro

theorem publication_unlink_relative_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (root : UInt64)
    (components : List String) (directory : Bool) :
    BorrowPost kernel held handle (fun _ => True) (Publication.unlinkRelative uid root components directory).lower := by
  unfold Publication.unlinkRelative
  split
  · apply borrow_bind (publication_under_borrow laws held handle _ _ _ _ _ ?_)
    · intro _ _
      exact .pure True.intro
    · intro fd
      apply borrow_bind (passive_borrow laws held handle _ (by simp [RetainsDescriptors]))
      intro reply _
      split <;> exact .pure True.intro
  · exact .pure True.intro

private theorem cleanup_export_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (root : Directories.Opened)
    (input : Publication.Input) (fresh : root.fd ≠ held) :
    BorrowPost kernel held handle (fun _ => True) (Publication.cleanupExport uid root input).lower := by
  unfold Publication.cleanupExport Publication.cleanupFiles Publication.cleanupDirectories
  apply borrow_bind (pre := fun _ => True)
  · apply loop_unit_borrow
    intro file state
    apply borrow_bind (publication_unlink_relative_borrow laws held handle _ _ _ _)
    intro _ _
    exact .pure True.intro
  · intro _ _
    apply borrow_bind (pre := fun _ => True)
    · apply loop_unit_borrow
      intro path state
      apply borrow_bind (publication_unlink_relative_borrow laws held handle _ _ _ _)
      intro _ _
      exact .pure True.intro
    · intro _ _
      apply borrow_bind (close_effect_borrow laws held handle _ fresh)
      intro _ _
      exact .pure True.intro

private theorem cleanup_footer_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (stage : Directories.Fresh)
    (fresh : stage.directory.fd ≠ held ∧ stage.container.fd ≠ held) :
    BorrowPost kernel held handle (fun _ => True) (Publication.cleanupFooter stage).lower := by
  unfold Publication.cleanupFooter Publication.cleanupStageFiles
  apply borrow_bind (pre := fun _ => True)
  · apply loop_unit_borrow
    intro name state
    apply borrow_bind (passive_borrow laws held handle _ (by simp [RetainsDescriptors]))
    intro _ _
    exact .pure True.intro
  · intro _ _
    apply borrow_bind (passive_borrow laws held handle _ (by simp [RetainsDescriptors]))
    intro _ _
    apply borrow_bind (close_effect_borrow laws held handle _ fresh.1)
    intro _ _
    apply borrow_bind (passive_borrow laws held handle _ (by simp [RetainsDescriptors]))
    intro _ _
    apply borrow_bind (close_effect_borrow laws held handle _ fresh.2)
    intro _ _
    exact .pure True.intro

-- §FS-host-boundary.ownership: Cleanup follows only fresh handles returned by the real
-- directory helpers. A failed or uncertain commit never authorizes another target's FD.
theorem publication_cleanup_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (parent : Directories.Parent) (stage : Directories.Fresh)
    (input : Publication.Input) (fresh : stage.directory.fd ≠ held ∧ stage.container.fd ≠ held) :
    BorrowPost kernel held handle (fun _ => True) (Publication.cleanup parent stage input).lower := by
  rw [Publication.cleanup_source_shape]
  apply borrow_bind (directoryOpen_borrow laws held handle _ _ _)
  intro root freshRoot
  cases root with
  | error => exact cleanup_footer_borrow laws held handle _ fresh
  | ok root =>
    apply borrow_bind (cleanup_export_borrow laws held handle _ _ _ freshRoot)
    intro _ _
    exact cleanup_footer_borrow laws held handle _ fresh

theorem publication_close_owned_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (parent : Directories.Parent) (stage : Directories.Fresh)
    (freshParent : parent.directory.fd ≠ held)
    (freshStage : stage.directory.fd ≠ held ∧ stage.container.fd ≠ held) :
    BorrowPost kernel held handle (fun _ => True) (Publication.closeOwned parent stage).lower := by
  unfold Publication.closeOwned
  apply borrow_bind (close_effect_borrow laws held handle _ freshStage.1)
  intro _ _
  apply borrow_bind (close_effect_borrow laws held handle _ freshStage.2)
  intro _ _
  apply borrow_bind (close_effect_borrow laws held handle _ freshParent)
  intro _ _
  exact .pure True.intro

theorem publication_finish_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (parent : Directories.Parent) (stage : Directories.Fresh)
    (outcome : Outcome) (renamed : Reply) (freshParent : parent.directory.fd ≠ held)
    (freshStage : stage.directory.fd ≠ held ∧ stage.container.fd ≠ held) :
    BorrowPost kernel held handle (fun _ => True) (Publication.finishCommit parent stage outcome renamed).lower := by
  unfold Publication.finishCommit
  apply borrow_bind (publication_close_owned_borrow laws held handle _ _ freshParent freshStage)
  intro _ _
  repeat' first | exact .pure True.intro | split

theorem publication_absolute_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (path : ByteArray) :
    BorrowPost kernel held handle (fun _ => True) (Publication.absolute path).lower := by
  unfold Publication.absolute
  split
  · exact .pure True.intro
  · split
    · exact .pure True.intro
    · apply borrow_bind (passive_borrow laws held handle _ (by simp [RetainsDescriptors]))
      intro current _
      repeat' first | exact .pure True.intro | split | dsimp only

theorem publication_destination_borrow {kernel : Contract} (held : UInt64) (handle : Handle)
    (request : GatewayWire.Request) (bundle : Validation.Bundle) (id : String) :
    BorrowPost kernel held handle (fun _ => True) (Publication.destination request bundle id).lower := by
  unfold Publication.destination
  dsimp only
  split <;> exact .pure True.intro

theorem publication_attempt_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (bundle : Validation.Bundle) (input : Publication.Input)
    (target stdoutHash stderrHash : ByteArray) :
    BorrowPost kernel held handle (fun _ => True)
      (Publication.attempt bundle input target stdoutHash stderrHash).lower := by
  unfold Publication.attempt
  apply borrow_bind (publication_absolute_borrow laws held handle _)
  intro display _
  cases display with
  | error => exact .pure True.intro
  | ok display =>
    apply borrow_bind (directory_parent_borrow laws held handle _ _)
    intro parent freshParent
    cases parent with
    | error => exact .pure True.intro
    | ok parent =>
      apply borrow_bind (directoryFresh_borrow laws held handle parent)
      intro fresh freshStage
      cases fresh with
      | error =>
        apply borrow_weaken (close_borrow laws parent.directory.fd held handle _ (Ne.symm freshParent))
        intro _ _; trivial
      | ok stage =>
        apply borrow_bind (publication_prepare_borrow laws held handle _ _ _ _ _ _ _)
        intro prepared _
        cases prepared with
        | error =>
          apply borrow_bind (publication_cleanup_borrow laws held handle parent stage input freshStage)
          intro _ _
          apply borrow_weaken (close_borrow laws parent.directory.fd held handle _ (Ne.symm freshParent))
          intro _ _; trivial
        | ok outcome =>
          apply borrow_bind (passive_borrow laws held handle _ (by simp [RetainsDescriptors]))
          intro renamed _
          exact publication_finish_borrow laws held handle parent stage outcome renamed freshParent freshStage

theorem publication_publish_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (request : GatewayWire.Request)
    (bundle : Validation.Bundle) (input : Publication.Input) :
    BorrowPost kernel held handle (fun _ => True) (Publication.publish request bundle input).lower := by
  unfold Publication.publish
  apply borrow_bind (outcome_identify_borrow laws held handle _)
  intro identified _
  cases identified with
  | error error | ok value =>
    apply borrow_bind (publication_destination_borrow held handle _ _ _)
    intro target _
    cases target with
    | error => exact .pure True.intro
    | ok target =>
      apply borrow_bind (publication_attempt_borrow laws held handle _ _ _ _ _)
      intro published _
      exact .pure True.intro

end LeanCage.Host.Kernel.Lowered
