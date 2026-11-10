import FilesystemSourceKinds
import RunDirectoryProofs.Requests
import PublicationCustodyProofs

namespace LeanCage.Host.Publication
open Filesystem

-- §FS-host-boundary.publication: Content helpers cannot expose a publication authentication tag.
def NoAttribute (request : Request) : Prop := request.op ≠ .setAttribute

theorem namespace_no_attribute (request : Request) (safe : Kernel.NamespacePassive request) :
    NoAttribute request := by
  intro same
  simp only [Kernel.NamespacePassive, same] at safe

theorem readOnly_no_attribute {α : Type} {program : Filesystem.Program α}
    (safe : Retrieval.ReadOnly program) : RequestProgram NoAttribute program :=
  request_weaken (Kernel.read_only_namespace_passive safe) namespace_no_attribute

theorem writeLoop_no_attribute (fuel : Nat) (fd : UInt64) (bytes : ByteArray) (offset : Nat) :
    RequestProgram NoAttribute (writeLoop fuel fd bytes offset) :=
  request_weaken (Kernel.write_loop_namespace_passive _ _ _ _) namespace_no_attribute

theorem writeNew_no_attribute (parent : UInt64) (name bytes : ByteArray) (mode : UInt64) :
    RequestProgram NoAttribute (writeNew parent name bytes mode) := by
  unfold writeNew
  split
  · exact .pure _
  · apply RequestProgram.call (by change Op.openAt ≠ Op.setAttribute; decide)
    intro reply
    split
    · exact .pure _
    · exact request_bind (writeLoop_no_attribute _ _ _ _)
        (fun _ => readOnly_no_attribute (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _)))

theorem ensureAt_no_attribute (uid : Nat) (parent : UInt64) (name : ByteArray) :
    RequestProgram NoAttribute (Directories.ensureAt uid parent name) := by
  unfold Directories.ensureAt
  apply RequestProgram.call (by change Op.mkdirAt ≠ Op.setAttribute; decide)
  intro reply
  dsimp only [Filesystem.Program.bind]
  split
  · exact readOnly_no_attribute (Retrieval.openAt_readOnly _ _ _)
  · split
    · exact readOnly_no_attribute (Retrieval.openAt_readOnly _ _ _)
    · exact .pure _

theorem publicAt_no_attribute (uid : Nat) (parent : UInt64) (name : ByteArray) (create : Bool) :
    RequestProgram NoAttribute (Directories.publicAt uid parent name create) := by
  cases create <;> unfold Directories.publicAt
  all_goals simp only [Bool.false_eq_true, ↓reduceIte]
  · apply request_bind (readOnly_no_attribute (Retrieval.openAt_readOnly _ _ _))
    intro result
    cases result with
    | error => exact .pure _
    | ok opened =>
      exact request_bind
        (readOnly_no_attribute (Retrieval.readOnly_snapshot (Snapshot.publicHandle_input _))) (fun _ => .pure _)
  · apply request_bind (ensureAt_no_attribute _ _ _)
    intro result
    cases result with
    | error => exact .pure _
    | ok opened =>
      exact request_bind
        (readOnly_no_attribute (Retrieval.readOnly_snapshot (Snapshot.publicHandle_input _))) (fun _ => .pure _)

theorem descend_no_attribute (uid : Nat) (create : Bool) (current : Directories.Opened) (names : List ByteArray) :
    RequestProgram NoAttribute (Directories.descend uid create current names) := by
  induction names generalizing current with
  | nil => exact .pure _
  | cons name rest ih =>
    unfold Directories.descend
    apply request_bind (publicAt_no_attribute _ _ _ _)
    intro next
    apply request_bind (readOnly_no_attribute (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _)))
    intro closed
    cases closed with
    | error =>
      cases next with
      | error => exact .pure _
      | ok => exact readOnly_no_attribute (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
    | ok => exact ih _

theorem parent_no_attribute (path : ByteArray) (create : Bool) :
    RequestProgram NoAttribute (Directories.parent path create) := by
  unfold Directories.parent
  apply request_bind (readOnly_no_attribute (Retrieval.readOnly_snapshot (Snapshot.sourceStart_input _)))
  intro selected
  cases selected with
  | error => exact .pure _
  | ok selected =>
    dsimp only
    split
    · split
      · exact readOnly_no_attribute (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
      · apply RequestProgram.call (by change Op.euid ≠ Op.setAttribute; decide)
        intro identity
        dsimp only [Filesystem.Program.bind]
        split
        · exact readOnly_no_attribute (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
        · apply request_bind (readOnly_no_attribute (Retrieval.inspect_readOnly _ _))
          intro base
          cases base with
          | error => exact .pure _
          | ok base => exact request_bind (descend_no_attribute _ _ _ _) (fun _ => .pure _)
    · exact readOnly_no_attribute (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))

theorem fresh_no_attribute (parent : Directories.Parent) :
    RequestProgram NoAttribute (Directories.fresh parent) := by
  unfold Directories.fresh
  apply request_bind (readOnly_no_attribute (Retrieval.openAt_readOnly _ _ _))
  intro container
  cases container with
  | error => exact .pure _
  | ok container =>
    apply request_bind (request_weaken (RunDirectory.directoryChild_requests _ _ _)
      (fun _ permitted => permitted.2.1))
    intro child
    cases child with
    | error => exact readOnly_no_attribute (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
    | ok => exact .pure _

theorem under_no_attribute {α : Type} (uid : Nat) (fd : UInt64) (names : List String) (create : Bool)
    (action : UInt64 → Filesystem.Program (Result α))
    (allowed : ∀ fd, RequestProgram NoAttribute (action fd)) :
    RequestProgram NoAttribute (under uid fd names create action) := by
  induction names generalizing fd with
  | nil => exact allowed fd
  | cons name rest ih =>
    unfold under
    split
    · exact .pure _
    · cases create <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · apply request_bind (readOnly_no_attribute (Retrieval.openAt_readOnly _ _ _))
        intro opened
        cases opened with
        | error => exact .pure _
        | ok child =>
          exact request_bind (ih child.fd)
            (fun _ => readOnly_no_attribute (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _)))
      · apply request_bind (ensureAt_no_attribute _ _ _)
        intro opened
        cases opened with
        | error => exact .pure _
        | ok child =>
          exact request_bind (ih child.fd)
            (fun _ => readOnly_no_attribute (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _)))

theorem writeRelative_no_attribute (uid : Nat) (root : UInt64) (file : Artifacts.ValidatedFile) :
    RequestProgram NoAttribute (writeRelative uid root file) := by
  unfold writeRelative
  dsimp only
  split
  · exact under_no_attribute _ _ _ _ _ (fun _ => writeNew_no_attribute _ _ _ _)
  · exact .pure _

theorem directories_no_attribute (uid : Nat) (root : UInt64) (paths : List Artifacts.ExportPath) :
    RequestProgram NoAttribute (directories uid root paths) := by
  unfold directories
  apply request_bind
  · apply request_forIn
    intro path member state
    apply request_bind (under_no_attribute _ _ _ _ _ (fun _ => .pure _))
    intro made
    cases made <;> exact .pure _
  · intro state
    dsimp only
    split <;> exact .pure _

theorem exports_no_attribute (uid : Nat) (stage : UInt64) (input : Input) :
    RequestProgram NoAttribute (exports uid stage input) := by
  unfold exports
  apply RequestProgram.call (by change Op.mkdirAt ≠ Op.setAttribute; decide)
  intro made
  dsimp only [Filesystem.Program.bind]
  split
  · exact .pure _
  · apply request_bind (readOnly_no_attribute (Retrieval.openAt_readOnly _ _ _))
    intro opened
    cases opened with
    | error => exact .pure _
    | ok root =>
      apply request_bind
      · apply request_bind (directories_no_attribute _ _ _)
        intro made
        cases made with
        | error => exact .pure _
        | ok made =>
          apply request_bind
          · apply request_forIn
            intro file member state
            apply request_bind (writeRelative_no_attribute _ _ _)
            intro written
            cases written <;> exact .pure _
          · intro state
            split <;> exact .pure _
      · intro filled
        exact readOnly_no_attribute (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))

theorem fill_no_attribute (uid : Nat) (stage : UInt64) (input : Input) (json wire : ByteArray) :
    RequestProgram NoAttribute (fill uid stage input json wire) := by
  unfold fill
  repeat' first
    | exact .pure _
    | (dsimp only; split)
    | split
  all_goals
    apply request_bind
    · apply request_forIn
      intro pair member state
      apply request_bind (writeNew_no_attribute _ _ _ _)
      intro written
      cases written <;> exact .pure _
    · intro state
      split
      · exact .pure _
      · exact exports_no_attribute _ _ _

theorem unlinkRelative_no_attribute (uid : Nat) (root : UInt64) (parts : List String) (directory : Bool) :
    RequestProgram NoAttribute (unlinkRelative uid root parts directory) := by
  unfold unlinkRelative
  split
  · apply request_bind (under_no_attribute _ _ _ _ _ (fun _ => by
      apply RequestProgram.call (by change Op.unlinkAt ≠ Op.setAttribute; decide)
      intro reply
      dsimp only [Filesystem.Program.bind]
      split <;> exact .pure _))
    intro ignored
    exact .pure _
  · exact .pure _

private theorem cleanup_footer_no_attribute (stage : Directories.Fresh) : RequestProgram NoAttribute (do
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
  apply request_bind
  · apply request_forIn
    intro name member state
    apply RequestProgram.call (by change Op.unlinkAt ≠ Op.setAttribute; decide)
    intro reply
    exact .pure _
  · intro finished
    apply RequestProgram.call (by change Op.unlinkAt ≠ Op.setAttribute; decide)
    intro reply
    apply RequestProgram.call (by change Op.close ≠ Op.setAttribute; decide)
    intro reply
    apply RequestProgram.call (by change Op.unlinkAt ≠ Op.setAttribute; decide)
    intro reply
    apply RequestProgram.call (by change Op.close ≠ Op.setAttribute; decide)
    intro reply
    exact .pure _

theorem cleanup_no_attribute (parent : Directories.Parent) (stage : Directories.Fresh) (input : Input) :
    RequestProgram NoAttribute (cleanup parent stage input) := by
  unfold cleanup
  apply request_bind (readOnly_no_attribute (Retrieval.openAt_readOnly _ _ _))
  intro opened
  dsimp only
  split
  · apply request_bind
    · apply request_forIn
      intro file member state
      exact request_bind (unlinkRelative_no_attribute _ _ _ _) (fun _ => .pure _)
    · intro finished
      apply request_bind
      · apply request_forIn
        intro path member state
        exact request_bind (unlinkRelative_no_attribute _ _ _ _) (fun _ => .pure _)
      · intro finished
        apply RequestProgram.call (by change Op.close ≠ Op.setAttribute; decide)
        intro reply
        exact cleanup_footer_no_attribute _
  · exact cleanup_footer_no_attribute _

end LeanCage.Host.Publication
