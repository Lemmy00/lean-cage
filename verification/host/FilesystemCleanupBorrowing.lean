import FilesystemCleanupStageReferences
import FilesystemLoweredPublicationBorrowing
import FilesystemUses

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

private theorem then_uses {kernel : Contract} {fd : UInt64} {handle : Handle} {needs : Request → Prop}
    {α β : Type} {program : Filesystem.Program α} {next : α → Filesystem.Program β} {post : α → Prop}
    (first : BorrowPost kernel fd handle post program.lower)
    (tail : ∀ value, post value → BorrowUses kernel fd handle needs (next value).lower) :
    BorrowUses kernel fd handle needs (program.bind next).lower := by
  rw [Filesystem.Program.lower_bind]
  exact borrow_then_uses first tail

theorem cleanup_files_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (root : UInt64) (files : List Artifacts.ValidatedFile) :
    BorrowPost kernel held handle (fun _ => True) (Publication.cleanupFiles uid root files).lower := by
  unfold Publication.cleanupFiles
  apply borrow_bind
  · apply borrow_forIn
    intro file state
    apply borrow_bind (publication_unlink_relative_borrow laws held handle _ _ _ _)
    intro ignored _
    exact .pure True.intro
  · intro ignored _
    exact .pure True.intro

private theorem cleanup_directories_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (root : UInt64) (paths : List Artifacts.ExportPath) :
    BorrowPost kernel held handle (fun _ => True) (Publication.cleanupDirectories uid root paths).lower := by
  unfold Publication.cleanupDirectories
  apply borrow_bind
  · apply borrow_forIn
    intro path state
    apply borrow_bind (publication_unlink_relative_borrow laws held handle _ _ _ _)
    intro ignored _
    exact .pure True.intro
  · intro ignored _
    exact .pure True.intro

private theorem effect_close_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held closed : UInt64) (handle : Handle) (different : held ≠ closed) :
    BorrowPost kernel held handle (fun _ => True) (Filesystem.Program.effect {op := .close, first := closed}).lower := by
  change BorrowPost kernel held handle (fun _ => True) (.call {op := .close, first := closed} (fun reply => .pure reply))
  apply BorrowPost.call
  · intro before after observed actual live
    rw [laws.close_other _ _ _ _ _ actual rfl different]
    exact live
  · intro before after reply actual live
    exact .pure True.intro

-- §FS-host-boundary.ownership: Each completed export cleanup retains the
-- live outer stage/container. Nested opens are fresh relative to that exact
-- held descriptor; closing the export root uses its derived distinctness.
theorem cleanup_export_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (root : Directories.Opened) (input : Publication.Input)
    (different : held ≠ root.fd) :
    BorrowPost kernel held handle (fun _ => True) (Publication.cleanupExport uid root input).lower := by
  unfold Publication.cleanupExport
  apply borrow_bind (cleanup_files_borrow laws held handle _ _ _)
  intro ignored _
  apply borrow_bind (cleanup_directories_borrow laws held handle _ _ _)
  intro ignored _
  apply borrow_bind (effect_close_borrow laws held root.fd handle different)
  intro ignored _
  exact .pure True.intro

theorem cleanup_stage_files_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (stage : Directories.Fresh) (names : List String) :
    BorrowPost kernel held handle (fun _ => True) (Publication.cleanupStageFiles stage names).lower := by
  unfold Publication.cleanupStageFiles
  apply borrow_bind
  · apply borrow_forIn
    intro name state
    apply passive_call laws held handle (by simp [RetainsDescriptors])
    intro ignored
    exact .pure True.intro
  · intro ignored _
    exact .pure True.intro

def InnerStageUnlink (stage : Directories.Fresh) (request : Request) : Prop :=
  request.op = .unlinkAt ∧ request.first ≠ stage.container.fd

private theorem adapter_no_inner {stage : Directories.Fresh} {primary : Request}
    (unused : ¬ InnerStageUnlink stage primary) {α : Type} {program : Filesystem.Program α}
    (source : RequestProfile (AdapterRequest primary) program) :
    RequestProgram (fun request => ¬ InnerStageUnlink stage request) program := by
  induction source with
  | pure => exact .pure _
  | call request next allowed following ih =>
    apply RequestProgram.call ?_ ih
    rcases allowed with same | magic | flags | close
    · exact same ▸ unused
    · simp [InnerStageUnlink, magic]
    · simp [InnerStageUnlink, flags]
    · simp [InnerStageUnlink, close]

private theorem lower_no_inner {stage : Directories.Fresh} {α : Type} {program : Filesystem.Program α}
    (source : RequestProgram (fun request => ¬ InnerStageUnlink stage request) program) :
    RequestProgram (fun request => ¬ InnerStageUnlink stage request) program.lower := by
  induction source with
  | pure => exact .pure _
  | call allowed following ih => exact request_bind (adapter_no_inner allowed (guarded_call_profile _)) ih

private theorem footer_stage_uses {kernel : Contract} (laws : DescriptorContract kernel)
    (stage : Directories.Fresh) (handle : Handle) :
    BorrowUses kernel stage.directory.fd handle (InnerStageUnlink stage) (Publication.cleanupFooter stage).lower := by
  unfold Publication.cleanupFooter
  apply then_uses (cleanup_stage_files_borrow laws stage.directory.fd handle _ _)
  intro ignored _
  apply then_uses (passive_borrow laws stage.directory.fd handle {
    op := .unlinkAt, first := stage.directory.fd, second := 512, left := "export".toUTF8 }
    (by simp [RetainsDescriptors]))
  intro ignored _
  apply BorrowUses.unused
  apply lower_no_inner
  repeat' first
    | exact .pure _
    | apply RequestProgram.call (by simp [InnerStageUnlink]); intro ignored

private theorem footer_container_uses {kernel : Contract} (laws : DescriptorContract kernel)
    (stage : Directories.Fresh) (handle : Handle) (different : stage.container.fd ≠ stage.directory.fd) :
    BorrowUses kernel stage.container.fd handle (fun request => request.op = .unlinkAt)
      (Publication.cleanupFooter stage).lower := by
  unfold Publication.cleanupFooter
  apply then_uses (cleanup_stage_files_borrow laws stage.container.fd handle _ _)
  intro ignored _
  apply then_uses (passive_borrow laws stage.container.fd handle {
    op := .unlinkAt, first := stage.directory.fd, second := 512, left := "export".toUTF8 }
    (by simp [RetainsDescriptors]))
  intro ignored _
  apply then_uses (effect_close_borrow laws stage.container.fd stage.directory.fd handle different)
  intro ignored _
  apply then_uses (passive_borrow laws stage.container.fd handle {
    op := .unlinkAt, first := stage.container.fd, second := 512, left := stage.name }
    (by simp [RetainsDescriptors]))
  intro ignored _
  apply BorrowUses.unused
  exact .call (by intro impossible; cases impossible) (fun _ => .pure _)

-- §FS-host-boundary.ownership: Every inner cleanup unlink occurs before
-- the actual stage close. Final parent-relative deletion is excluded by its
-- real operand; later name reuse or a lost close cannot grant another use.
theorem cleanup_stage_uses {kernel : Contract} (laws : DescriptorContract kernel)
    (parent : Directories.Parent) (stage : Directories.Fresh) (input : Publication.Input) (handle : Handle) :
    BorrowUses kernel stage.directory.fd handle (InnerStageUnlink stage) (Publication.cleanup parent stage input).lower := by
  rw [Publication.cleanup_source_shape]
  apply then_uses (directoryOpen_borrow laws stage.directory.fd handle _ _ _)
  intro opened fresh
  cases opened with
  | error => exact footer_stage_uses laws stage handle
  | ok root =>
    dsimp only
    apply then_uses (cleanup_export_borrow laws stage.directory.fd handle _ _ _ (Ne.symm fresh))
    intro ignored _
    exact footer_stage_uses laws stage handle

theorem cleanup_container_uses {kernel : Contract} (laws : DescriptorContract kernel)
    (parent : Directories.Parent) (stage : Directories.Fresh) (input : Publication.Input) (handle : Handle)
    (different : stage.container.fd ≠ stage.directory.fd) :
    BorrowUses kernel stage.container.fd handle (fun request => request.op = .unlinkAt)
      (Publication.cleanup parent stage input).lower := by
  rw [Publication.cleanup_source_shape]
  apply then_uses (directoryOpen_borrow laws stage.container.fd handle _ _ _)
  intro opened fresh
  cases opened with
  | error => exact footer_container_uses laws stage handle different
  | ok root =>
    dsimp only
    apply then_uses (cleanup_export_borrow laws stage.container.fd handle _ _ _ (Ne.symm fresh))
    intro ignored _
    exact footer_container_uses laws stage handle different

end LeanCage.Host.Kernel.Lowered
