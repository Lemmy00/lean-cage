import FilesystemWriteSources.PublicationContent

namespace LeanCage.Host.Kernel.WriteSources
open Filesystem Publication

private theorem readonly_files {α : Type} {program : Filesystem.Program α}
    (source : Retrieval.ReadOnly program) : FileWriters program := file_no_write (read_only_no_write source)

theorem ensureAt_files (uid : Nat) (parent : UInt64) (name : ByteArray) :
    FileWriters (Directories.ensureAt uid parent name) := by
  unfold Directories.ensureAt
  apply file_call (by intro wrong; cases wrong)
  intro reply
  dsimp only [Filesystem.Program.bind]
  split
  · exact readonly_files (Retrieval.openAt_readOnly _ _ _)
  · split
    · exact readonly_files (Retrieval.openAt_readOnly _ _ _)
    · exact (file_pure _)

theorem publicAt_files (uid : Nat) (parent : UInt64) (name : ByteArray) (create : Bool) :
    FileWriters (Directories.publicAt uid parent name create) := by
  cases create <;> unfold Directories.publicAt
  all_goals simp only [Bool.false_eq_true, ↓reduceIte]
  · apply file_bind (readonly_files (Retrieval.openAt_readOnly _ _ _))
    intro result
    cases result with
    | error => exact (file_pure _)
    | ok opened =>
      apply file_bind (readonly_files (Retrieval.readOnly_snapshot (Snapshot.publicHandle_input _)))
      intro allowed
      exact (file_pure _)
  · apply file_bind (ensureAt_files _ _ _)
    intro result
    cases result with
    | error => exact (file_pure _)
    | ok opened =>
      apply file_bind (readonly_files (Retrieval.readOnly_snapshot (Snapshot.publicHandle_input _)))
      intro allowed
      exact (file_pure _)

theorem descend_files (uid : Nat) (create : Bool) (current : Directories.Opened) (names : List ByteArray) :
    FileWriters (Directories.descend uid create current names) := by
  induction names generalizing current with
  | nil => exact (file_pure _)
  | cons name rest ih =>
    unfold Directories.descend
    apply file_bind (publicAt_files _ _ _ _)
    intro next
    apply file_bind (readonly_files (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _)))
    intro closed
    cases closed with
    | error =>
      cases next with
      | error => exact (file_pure _)
      | ok => exact readonly_files (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
    | ok => exact ih _

theorem parent_files (path : ByteArray) (create : Bool) : FileWriters (Directories.parent path create) := by
  unfold Directories.parent
  apply file_bind (readonly_files (Retrieval.readOnly_snapshot (Snapshot.sourceStart_input _)))
  intro selected
  cases selected with
  | error => exact (file_pure _)
  | ok selected =>
    dsimp only
    split
    · split
      · exact readonly_files (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
      · apply file_call (by intro wrong; cases wrong)
        intro identity
        dsimp only [Filesystem.Program.bind]
        split
        · exact readonly_files (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
        · apply file_bind (readonly_files (Retrieval.inspect_readOnly _ _))
          intro base
          cases base with
          | error => exact (file_pure _)
          | ok base =>
            apply file_bind (descend_files _ _ _ _)
            intro result
            exact (file_pure _)
    · exact readonly_files (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))

private theorem unlinkRelative_files (uid : Nat) (root : UInt64) (components : List String) (directory : Bool) :
    FileWriters (Publication.unlinkRelative uid root components directory) := by
  unfold Publication.unlinkRelative
  split
  · apply file_bind (under_files _ _ _ _ _ (fun _ => by
      apply file_call (by intro wrong; cases wrong)
      intro reply
      dsimp only [Filesystem.Program.bind]
      split <;> exact file_pure _))
    intro ignored
    exact file_pure _
  · exact file_pure _

private theorem cleanup_files_footer (stage : Directories.Fresh) : FileWriters (do
    for name in ["policy.json", "boot.log", "vm-report.json", "stdout", "stderr",
        "stored-report.json", "export.manifest", "result.json", "publication.wire"] do
      let _ ← Filesystem.Program.effect {op := .unlinkAt, first := stage.directory.fd, left := name.toUTF8}
    let _ ← Filesystem.Program.effect {
      op := .unlinkAt, first := stage.directory.fd, second := 512, left := "export".toUTF8 }
    let _ ← Filesystem.Program.effect {op := .close, first := stage.directory.fd}
    let _ ← Filesystem.Program.effect {
      op := .unlinkAt, first := stage.container.fd, second := 512, left := stage.name }
    let _ ← Filesystem.Program.effect {op := .close, first := stage.container.fd}
    pure ()) := by
  apply file_bind
  · apply file_forIn
    intro name member state
    apply file_call (by intro wrong; cases wrong)
    intro reply
    exact (file_pure _)
  · intro finished
    apply file_call (by intro wrong; cases wrong)
    intro reply
    apply file_call (by intro wrong; cases wrong)
    intro reply
    apply file_call (by intro wrong; cases wrong)
    intro reply
    apply file_call (by intro wrong; cases wrong)
    intro reply
    exact (file_pure _)

theorem cleanup_files (parent : Directories.Parent) (stage : Directories.Fresh) (input : Input) :
    FileWriters (cleanup parent stage input) := by
  unfold cleanup
  apply file_bind (readonly_files (Retrieval.openAt_readOnly _ _ _))
  intro opened
  dsimp only
  split
  · apply file_bind
    · apply file_forIn
      intro file member state
      apply file_bind (unlinkRelative_files _ _ _ _)
      intro ignored
      exact (file_pure _)
    · intro finished
      apply file_bind
      · apply file_forIn
        intro path member state
        apply file_bind (unlinkRelative_files _ _ _ _)
        intro ignored
        exact (file_pure _)
      · intro finished
        apply file_call (by intro wrong; cases wrong)
        intro reply
        exact cleanup_files_footer _
  · exact cleanup_files_footer _

theorem closeOwned_files (parent : Directories.Parent) (stage : Directories.Fresh) :
    FileWriters (closeOwned parent stage) := by
  unfold closeOwned
  apply file_call (by intro wrong; cases wrong)
  intro reply
  apply file_call (by intro wrong; cases wrong)
  intro reply
  apply file_call (by intro wrong; cases wrong)
  intro reply
  exact (file_pure _)

theorem fresh_files (parent : Directories.Parent) : FileWriters (Directories.fresh parent) := by
  unfold Directories.fresh
  apply file_bind (readonly_files (Retrieval.openAt_readOnly _ _ _))
  intro container
  cases container with
  | error => exact file_pure _
  | ok container =>
    apply file_bind
    · apply file_no_write
      apply request_weaken (RunDirectory.directoryChild_requests _ _ _)
      intro request role writing
      simp only [RunDirectory.BeforeMarkRequest, RunDirectory.DirectoryRequest, writing] at role
      exact role.1
    · intro child
      cases child with
      | error => exact file_closeResult _ _
      | ok => exact file_pure _

theorem attempt_files (bundle : Validation.Bundle) (input : Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) : FileWriters (attempt bundle input target stdoutHash stderrHash) := by
  unfold attempt
  apply file_bind (readonly_files (Retrieval.absolute_readOnly _))
  intro display
  cases display with
  | error => exact (file_pure _)
  | ok display =>
    apply file_bind (parent_files _ _)
    intro parent
    cases parent with
    | error => exact (file_pure _)
    | ok parent =>
      apply file_bind (fresh_files _)
      intro fresh
      cases fresh with
      | error => exact readonly_files (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
      | ok stage =>
        apply file_bind (prepare_files _ _ _ _ _ _ _)
        intro prepared
        cases prepared with
        | error =>
          apply file_bind (cleanup_files _ _ _)
          intro ignored
          exact readonly_files (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
        | ok outcome =>
          apply file_call (by intro wrong; cases wrong)
          intro renamed
          dsimp only [Filesystem.Program.bind]
          unfold finishCommit
          apply file_bind (closeOwned_files _ _)
          intro ignored
          split
          · exact (file_pure _)
          · split
            · exact (file_pure _)
            · exact (file_pure _)

theorem publish_files (request : GatewayWire.Request) (bundle : Validation.Bundle) (input : Input) :
    FileWriters (publish request bundle input) := by
  unfold publish
  apply file_bind (readonly_files (Retrieval.identify_readOnly _))
  intro identified
  cases identified with
  | error =>
    apply file_bind (readonly_files (Retrieval.publicationDestination_readOnly _ _ _))
    intro target
    cases target with
    | error => exact (file_pure _)
    | ok target => exact file_bind (attempt_files _ _ _ _ _) (fun _ => (file_pure _))
  | ok hashes =>
    cases hashes
    apply file_bind (readonly_files (Retrieval.publicationDestination_readOnly _ _ _))
    intro target
    cases target with
    | error => exact (file_pure _)
    | ok target => exact file_bind (attempt_files _ _ _ _ _) (fun _ => (file_pure _))


end LeanCage.Host.Kernel.WriteSources
