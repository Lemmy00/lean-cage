import FilesystemSourceIntervals
import ImageProofs.Writes
import FilesystemCreationSources

namespace LeanCage.Host.Kernel
open Filesystem

private theorem readonly_nondestructive {α : Type} {program : Filesystem.Program α}
    (source : Retrieval.ReadOnly program) : RequestProgram (fun request => ¬ DestructiveRequest request) program :=
  request_weaken (read_only_namespace_passive source) (fun _ => namespace_passive_not_destructive)

private theorem writes_nondestructive {α : Type} {program : Filesystem.Program α} {fd : UInt64}
    (source : Image.WriteProgram fd program) : RequestProgram (fun request => ¬ DestructiveRequest request) program := by
  induction source with
  | pure => exact .pure _
  | call allowed following ih =>
    apply RequestProgram.call _ ih
    intro destructive
    rcases destructive with removing | moving
    · rw [allowed.1] at removing; cases removing
    · rw [allowed.1] at moving; cases moving

theorem writeNew_nondestructive (parent : UInt64) (name bytes : ByteArray) (mode : UInt64) :
    RequestProgram (fun request => ¬ DestructiveRequest request) (writeNew parent name bytes mode) := by
  unfold writeNew
  split
  · exact .pure _
  · apply RequestProgram.call (by simp [DestructiveRequest])
    intro reply
    split
    · exact .pure _
    · exact request_bind (writes_nondestructive (Image.writeLoop_scoped _ _ _ _))
        (fun _ => readonly_nondestructive (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _)))

private theorem ensure_nondestructive (uid : Nat) (parent : UInt64) (name : ByteArray) :
    RequestProgram (fun request => ¬ DestructiveRequest request) (Directories.ensureAt uid parent name) := by
  unfold Directories.ensureAt
  apply RequestProgram.call (by simp [DestructiveRequest])
  intro reply
  dsimp only [Filesystem.Program.bind]
  repeat' first
    | exact .pure _
    | split
    | exact readonly_nondestructive (Retrieval.openAt_readOnly _ _ _)

theorem publication_under_nondestructive {α : Type} (uid : Nat) (root : UInt64) (names : List String)
    (create : Bool) (action : UInt64 → Filesystem.Program (Result α))
    (permitted : ∀ fd, RequestProgram (fun request => ¬ DestructiveRequest request) (action fd)) :
    RequestProgram (fun request => ¬ DestructiveRequest request) (Publication.under uid root names create action) := by
  induction names generalizing root with
  | nil => exact permitted root
  | cons name rest ih =>
    unfold Publication.under
    split
    · exact .pure _
    · cases create <;> simp only [Bool.false_eq_true, ↓reduceIte]
      all_goals apply request_bind
      · exact readonly_nondestructive (Retrieval.openAt_readOnly _ _ _)
      · intro opened
        cases opened with
        | error => exact .pure _
        | ok child =>
          apply request_bind (ih child.fd)
          intro result
          exact readonly_nondestructive (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
      · exact ensure_nondestructive _ _ _
      · intro opened
        cases opened with
        | error => exact .pure _
        | ok child =>
          apply request_bind (ih child.fd)
          intro result
          exact readonly_nondestructive (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))

private theorem write_relative_nondestructive (uid : Nat) (root : UInt64) (file : Artifacts.ValidatedFile) :
    RequestProgram (fun request => ¬ DestructiveRequest request) (Publication.writeRelative uid root file) := by
  unfold Publication.writeRelative
  dsimp only
  split
  · exact publication_under_nondestructive _ _ _ _ _ (fun _ => writeNew_nondestructive _ _ _ _)
  · exact .pure _

private theorem directories_nondestructive (uid : Nat) (root : UInt64) (paths : List Artifacts.ExportPath) :
    RequestProgram (fun request => ¬ DestructiveRequest request) (Publication.directories uid root paths) := by
  unfold Publication.directories
  apply request_bind
  · apply request_forIn
    intro path member state
    apply request_bind (publication_under_nondestructive _ _ _ _ _ (fun _ => .pure _))
    intro made
    cases made <;> exact .pure _
  · intro state
    dsimp only
    split <;> exact .pure _

private theorem exports_nondestructive (uid : Nat) (stage : UInt64) (input : Publication.Input) :
    RequestProgram (fun request => ¬ DestructiveRequest request) (Publication.exports uid stage input) := by
  unfold Publication.exports
  apply RequestProgram.call (by simp [DestructiveRequest])
  intro made
  dsimp only [Filesystem.Program.bind]
  split
  · exact .pure _
  · apply request_bind (readonly_nondestructive (Retrieval.openAt_readOnly _ _ _))
    intro opened
    cases opened with
    | error => exact .pure _
    | ok root =>
      apply request_bind
      · apply request_bind (directories_nondestructive _ _ _)
        intro made
        cases made with
        | error => exact .pure _
        | ok made =>
          apply request_bind
          · apply request_forIn
            intro file member state
            apply request_bind (write_relative_nondestructive _ _ _)
            intro written
            cases written <;> exact .pure _
          · intro state
            split <;> exact .pure _
      · intro filled
        exact readonly_nondestructive (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))

theorem publication_fill_nondestructive (uid : Nat) (stage : UInt64) (input : Publication.Input)
    (json wire : ByteArray) :
    RequestProgram (fun request => ¬ DestructiveRequest request) (Publication.fill uid stage input json wire) := by
  unfold Publication.fill
  repeat' first
    | exact .pure _
    | (dsimp only; split)
    | split
  all_goals
    apply request_bind
    · apply request_forIn
      intro pair member state
      apply request_bind (writeNew_nondestructive _ _ _ _)
      intro written
      cases written <;> exact .pure _
    · intro state
      split
      · exact .pure _
      · exact exports_nondestructive _ _ _

-- §FS-host-boundary.publication: Filling and authenticating a private stage cannot retire
-- its registered name/scope. This is an actual source profile, not a private-region frame.
theorem publication_prepare_nondestructive (bundle : Validation.Bundle) (input : Publication.Input)
    (target stdoutHash stderrHash : ByteArray) (parent : Directories.Parent) (stage : Directories.Fresh) :
    RequestProgram (fun request => ¬ DestructiveRequest request)
      (Publication.prepare bundle input target stdoutHash stderrHash parent stage) := by
  unfold Publication.prepare
  apply request_bind (readonly_nondestructive (Retrieval.readOnly_snapshot (Snapshot.hash_input _)))
  intro policyDigest
  cases policyDigest with
  | error => exact .pure _
  | ok policyDigest =>
    dsimp only
    split
    · split
      · exact .pure _
      · apply request_bind (readonly_nondestructive (Retrieval.authenticate_readOnly _ _))
        intro digest
        cases digest with
        | error => exact .pure _
        | ok digest =>
          dsimp only
          apply request_bind (publication_fill_nondestructive _ _ _ _ _)
          intro filled
          cases filled with
          | error => exact .pure _
          | ok filled =>
            apply RequestProgram.call (by simp [DestructiveRequest])
            intro reply
            dsimp only [Filesystem.Program.bind]
            split <;> exact .pure _
    · exact .pure _

end LeanCage.Host.Kernel
