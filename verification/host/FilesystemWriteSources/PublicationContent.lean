import FilesystemWriteSources.FileWriters

namespace LeanCage.Host.Kernel.WriteSources
open Filesystem

private theorem readonly_files {α : Type} {program : Filesystem.Program α}
    (source : Retrieval.ReadOnly program) : FileWriters program := file_no_write (read_only_no_write source)

private theorem ensure_files (uid : Nat) (parent : UInt64) (name : ByteArray) :
    FileWriters (Directories.ensureAt uid parent name) := by
  unfold Directories.ensureAt
  apply file_call (by intro wrong; cases wrong)
  intro reply
  dsimp only [Filesystem.Program.bind]
  repeat' first
    | exact (file_pure _)
    | split
    | exact readonly_files (Retrieval.openAt_readOnly _ _ _)

theorem under_files {α : Type} (uid : Nat) (root : UInt64) (names : List String)
    (create : Bool) (action : UInt64 → Filesystem.Program (Result α))
    (permitted : ∀ fd, FileWriters (action fd)) :
    FileWriters (Publication.under uid root names create action) := by
  induction names generalizing root with
  | nil => exact permitted root
  | cons name rest ih =>
    unfold Publication.under
    split
    · exact (file_pure _)
    · cases create <;> simp only [Bool.false_eq_true, ↓reduceIte]
      all_goals apply file_bind
      · exact readonly_files (Retrieval.openAt_readOnly _ _ _)
      · intro opened
        cases opened with
        | error => exact (file_pure _)
        | ok child =>
          apply file_bind (ih child.fd)
          intro result
          exact readonly_files (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
      · exact ensure_files _ _ _
      · intro opened
        cases opened with
        | error => exact (file_pure _)
        | ok child =>
          apply file_bind (ih child.fd)
          intro result
          exact readonly_files (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))

theorem write_relative_files (uid : Nat) (root : UInt64) (file : Artifacts.ValidatedFile) :
    FileWriters (Publication.writeRelative uid root file) := by
  unfold Publication.writeRelative
  dsimp only
  split
  · exact under_files _ _ _ _ _ (fun _ => file_writeNew _ _ _ _)
  · exact (file_pure _)

private theorem directories_files (uid : Nat) (root : UInt64) (paths : List Artifacts.ExportPath) :
    FileWriters (Publication.directories uid root paths) := by
  unfold Publication.directories
  apply file_bind
  · apply file_forIn
    intro path member state
    apply file_bind (under_files _ _ _ _ _ (fun _ => (file_pure _)))
    intro made
    cases made <;> exact (file_pure _)
  · intro state
    dsimp only
    split <;> exact (file_pure _)

private theorem exports_files (uid : Nat) (stage : UInt64) (input : Publication.Input) :
    FileWriters (Publication.exports uid stage input) := by
  unfold Publication.exports
  apply file_call (by intro wrong; cases wrong)
  intro made
  dsimp only [Filesystem.Program.bind]
  split
  · exact (file_pure _)
  · apply file_bind (readonly_files (Retrieval.openAt_readOnly _ _ _))
    intro opened
    cases opened with
    | error => exact (file_pure _)
    | ok root =>
      apply file_bind
      · apply file_bind (directories_files _ _ _)
        intro made
        cases made with
        | error => exact (file_pure _)
        | ok made =>
          apply file_bind
          · apply file_forIn
            intro file member state
            apply file_bind (write_relative_files _ _ _)
            intro written
            cases written <;> exact (file_pure _)
          · intro state
            split <;> exact (file_pure _)
      · intro filled
        exact readonly_files (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))

theorem fill_files (uid : Nat) (stage : UInt64) (input : Publication.Input)
    (json wire : ByteArray) :
    FileWriters (Publication.fill uid stage input json wire) := by
  unfold Publication.fill
  repeat' first
    | exact (file_pure _)
    | (dsimp only; split)
    | split
  all_goals
    apply file_bind
    · apply file_forIn
      intro pair member state
      apply file_bind (file_writeNew _ _ _ _)
      intro written
      cases written <;> exact (file_pure _)
    · intro state
      split
      · exact (file_pure _)
      · exact exports_files _ _ _

-- §FS-host-boundary.publication: Stage filling and authentication write only through
-- the actual nested exclusive file writers; this is a source proof, not a region frame.
theorem prepare_files (bundle : Validation.Bundle) (input : Publication.Input)
    (target stdoutHash stderrHash : ByteArray) (parent : Directories.Parent) (stage : Directories.Fresh) :
    FileWriters
      (Publication.prepare bundle input target stdoutHash stderrHash parent stage) := by
  unfold Publication.prepare
  apply file_bind (readonly_files (Retrieval.readOnly_snapshot (Snapshot.hash_input _)))
  intro policyDigest
  cases policyDigest with
  | error => exact (file_pure _)
  | ok policyDigest =>
    dsimp only
    split
    · split
      · exact (file_pure _)
      · apply file_bind (readonly_files (Retrieval.authenticate_readOnly _ _))
        intro digest
        cases digest with
        | error => exact (file_pure _)
        | ok digest =>
          dsimp only
          apply file_bind (fill_files _ _ _ _ _)
          intro filled
          cases filled with
          | error => exact (file_pure _)
          | ok filled =>
            apply file_call (by intro wrong; cases wrong)
            intro reply
            dsimp only [Filesystem.Program.bind]
            split <;> exact (file_pure _)
    · exact (file_pure _)


end LeanCage.Host.Kernel.WriteSources
