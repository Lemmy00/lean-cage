import GatewayStoredReadProfile
import PublicationProofs.Prefix

namespace LeanCage.Host.PrivateStreams.Publishing
open Filesystem Kernel Publication PrivateStreams

-- §FS-host-boundary.publication: These are the real publisher branches;
-- every copied input uses pread and every output/cleanup operation remains.
theorem positioned_forIn {α β : Type} (items : List α) (state : β)
    (body : α → β → Filesystem.Program (ForInStep β))
    (allowed : ∀ item state, RequestProgram PositionedReads (body item state)) :
    RequestProgram PositionedReads (forIn items state body) :=
  request_forIn items state PositionedReads body (fun item _ state => allowed item state)

theorem positioned_bind_post {α β : Type} {program : Filesystem.Program α} {next : α → Filesystem.Program β}
    {post : α → Prop} (first : RequestProgram PositionedReads program) (observed : Snapshot.PostProgram post program)
    (tail : ∀ value, post value → RequestProgram PositionedReads (next value)) :
    RequestProgram PositionedReads (program.bind next) := by
  induction first with
  | pure value => cases observed with | pure property => exact tail value property
  | call allowed rest ih =>
    cases observed with
    | call valid => exact .call allowed (fun reply => ih reply (valid reply))

theorem directory_profile_positioned {α : Type} {program : Filesystem.Program α}
    (source : RequestProgram RunDirectory.DirectoryRequest program) : RequestProgram PositionedReads program := by
  apply request_weaken source
  intro request role reading
  simp only [RunDirectory.DirectoryRequest, reading] at role

theorem ensureAt_positioned (uid : Nat) (parent : UInt64) (name : ByteArray) :
    RequestProgram PositionedReads (Directories.ensureAt uid parent name) := by
  unfold Directories.ensureAt
  apply RequestProgram.call (by intro impossible; cases impossible)
  intro reply
  dsimp only [Filesystem.Program.bind]
  split
  · exact (PrivateStreams.openAt_positioned _ _ _)
  · split
    · exact (PrivateStreams.openAt_positioned _ _ _)
    · exact .pure _

theorem publicAt_positioned (uid : Nat) (parent : UInt64) (name : ByteArray) (create : Bool) :
    RequestProgram PositionedReads (Directories.publicAt uid parent name create) := by
  cases create <;> unfold Directories.publicAt
  all_goals simp only [Bool.false_eq_true, ↓reduceIte]
  · apply request_bind ((PrivateStreams.openAt_positioned _ _ _))
    intro result
    cases result with
    | error => exact .pure _
    | ok opened =>
      apply request_bind ((no_read_positioned (publicHandle_noRead _)))
      intro allowed
      exact .pure _
  · apply request_bind (ensureAt_positioned _ _ _)
    intro result
    cases result with
    | error => exact .pure _
    | ok opened =>
      apply request_bind ((no_read_positioned (publicHandle_noRead _)))
      intro allowed
      exact .pure _

theorem descend_positioned (uid : Nat) (create : Bool) (current : Directories.Opened) (names : List ByteArray) :
    RequestProgram PositionedReads (Directories.descend uid create current names) := by
  induction names generalizing current with
  | nil => exact .pure _
  | cons name rest ih =>
    unfold Directories.descend
    apply request_bind (publicAt_positioned _ _ _ _)
    intro next
    apply request_bind ((close_positioned _ _))
    intro closed
    cases closed with
    | error =>
      cases next with
      | error => exact .pure _
      | ok => exact (close_positioned _ _)
    | ok => exact ih _

theorem parent_positioned (path : ByteArray) (create : Bool) : RequestProgram PositionedReads (Directories.parent path create) := by
  unfold Directories.parent
  apply request_bind ((no_read_positioned (sourceStart_noRead _)))
  intro selected
  cases selected with
  | error => exact .pure _
  | ok selected =>
    dsimp only
    split
    · split
      · exact (close_positioned _ _)
      · apply RequestProgram.call (by intro impossible; cases impossible)
        intro identity
        dsimp only [Filesystem.Program.bind]
        split
        · exact (close_positioned _ _)
        · apply request_bind ((PrivateStreams.inspect_positioned _ _))
          intro base
          cases base with
          | error => exact .pure _
          | ok base =>
            apply request_bind (descend_positioned _ _ _ _)
            intro result
            exact .pure _
    · exact (close_positioned _ _)

theorem randomBytes_positioned (fuel count : Nat) (bytes : ByteArray) (bound : count ≤ 16) :
    RequestProgram PositionedReads (Directories.randomBytes fuel count bytes) := by
  apply directory_profile_positioned (request_weaken (RunDirectory.directoryRandom_requests fuel count bytes bound) ?_)
  intro request allowed
  exact allowed.1

theorem newChild_positioned (uid : Nat) (parent : UInt64) (prefixName : String) :
    RequestProgram PositionedReads (Directories.newChild uid parent prefixName) := by
  unfold Directories.newChild
  apply request_bind (randomBytes_positioned _ _ _ (by decide))
  intro random
  cases random with
  | error => exact .pure _
  | ok bytes =>
    dsimp only
    split
    · exact .pure _
    · apply RequestProgram.call (by intro impossible; cases impossible)
      intro made
      dsimp only [Filesystem.Program.bind]
      split
      · exact .pure _
      · apply request_bind ((PrivateStreams.openAt_positioned _ _ _))
        intro opened
        cases opened with
        | error => exact .pure _
        | ok directory =>
          dsimp only
          split
          · exact (close_positioned _ _)
          · exact .pure _

theorem fresh_positioned (parent : Directories.Parent) : RequestProgram PositionedReads (Directories.fresh parent) := by
  unfold Directories.fresh
  apply request_bind ((PrivateStreams.openAt_positioned _ _ _))
  intro container
  cases container with
  | error => exact .pure _
  | ok container =>
    apply request_bind (newChild_positioned _ _ _)
    intro child
    cases child with
    | error => exact (close_positioned _ _)
    | ok => exact .pure _

-- §FS-host-boundary.ownership: Checked components retain the exact parent until its action closes.
theorem under_positioned {α : Type} (uid : Nat) (fd : UInt64) (names : List String) (create : Bool)
    (action : UInt64 → Filesystem.Program (Result α)) (allowed : ∀ fd, RequestProgram PositionedReads (action fd)) :
    RequestProgram PositionedReads (under uid fd names create action) := by
  induction names generalizing fd with
  | nil => exact allowed fd
  | cons name rest ih =>
    unfold under
    split
    · exact .pure _
    · cases create <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · apply request_bind ((PrivateStreams.openAt_positioned _ _ _))
        intro opened
        cases opened with
        | error => exact .pure _
        | ok child =>
          exact request_bind (ih child.fd)
            (fun _ => (close_positioned _ _))
      · apply request_bind (ensureAt_positioned _ _ _)
        intro opened
        cases opened with
        | error => exact .pure _
        | ok child =>
          exact request_bind (ih child.fd)
            (fun _ => (close_positioned _ _))


theorem writeRelative_positioned (uid : Nat) (root : UInt64) (file : Artifacts.ValidatedFile) :
    RequestProgram PositionedReads (writeRelative uid root file) := by
  unfold writeRelative
  dsimp only
  split
  · exact under_positioned _ _ _ _ _ (fun _ => write_new_positioned _ _ _ _)
  · exact .pure _

theorem directories_positioned (uid : Nat) (root : UInt64) (paths : List Artifacts.ExportPath) :
    RequestProgram PositionedReads (directories uid root paths) := by
  unfold directories
  apply request_bind
  · apply positioned_forIn
    intro path state
    apply request_bind (under_positioned _ _ _ _ _ (fun _ => .pure _))
    intro made
    cases made <;> exact .pure _
  · intro state
    dsimp only
    split <;> exact .pure _

theorem exports_positioned (uid : Nat) (stage : UInt64) (input : Input) :
    RequestProgram PositionedReads (exports uid stage input) := by
  unfold exports
  apply RequestProgram.call (by intro impossible; cases impossible)
  intro made
  dsimp only [Filesystem.Program.bind]
  split
  · exact .pure _
  · apply request_bind ((PrivateStreams.openAt_positioned _ _ _))
    intro opened
    cases opened with
    | error => exact .pure _
    | ok root =>
      apply request_bind
      · apply request_bind (directories_positioned _ _ _)
        intro made
        cases made with
        | error => exact .pure _
        | ok made =>
          apply request_bind
          · apply positioned_forIn
            intro file state
            apply request_bind (writeRelative_positioned _ _ _)
            intro written
            cases written <;> exact .pure _
          · intro state
            split <;> exact .pure _
      · intro filled
        exact (close_positioned _ _)

theorem fill_positioned (uid : Nat) (stage : UInt64) (input : Input) (json wire : ByteArray) :
    RequestProgram PositionedReads (fill uid stage input json wire) := by
  unfold fill
  repeat' first
    | exact .pure _
    | (dsimp only; split)
    | split
  all_goals
    apply request_bind
    · apply positioned_forIn
      intro pair state
      apply request_bind (write_new_positioned _ _ _ _)
      intro written
      cases written <;> exact .pure _
    · intro state
      split
      · exact .pure _
      · exact exports_positioned _ _ _

theorem unlinkRelative_positioned (uid : Nat) (root : UInt64) (parts : List String) (directory : Bool) :
    RequestProgram PositionedReads (unlinkRelative uid root parts directory) := by
  unfold unlinkRelative
  split
  · apply request_bind (under_positioned _ _ _ _ _ (fun _ => by
      apply RequestProgram.call
      · intro impossible; cases impossible
      · intro reply
        dsimp only [Filesystem.Program.bind]
        split <;> exact .pure _))
    intro ignored
    exact .pure _
  · exact .pure _


private theorem cleanup_footer (stage : Directories.Fresh) : RequestProgram PositionedReads (do
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
  · apply positioned_forIn
    intro name state
    apply RequestProgram.call (by intro impossible; cases impossible)
    intro reply
    exact .pure _
  · intro finished
    apply RequestProgram.call (by intro impossible; cases impossible)
    intro reply
    apply RequestProgram.call (by intro impossible; cases impossible)
    intro reply
    apply RequestProgram.call (by intro impossible; cases impossible)
    intro reply
    apply RequestProgram.call (by intro impossible; cases impossible)
    intro reply
    exact .pure _

theorem cleanup_positioned (parent : Directories.Parent) (stage : Directories.Fresh) (input : Input) :
    RequestProgram PositionedReads (cleanup parent stage input) := by
  unfold cleanup
  apply request_bind ((PrivateStreams.openAt_positioned _ _ _))
  intro opened
  dsimp only
  split
  · apply request_bind
    · apply positioned_forIn
      intro file state
      apply request_bind (unlinkRelative_positioned _ _ _ _)
      intro ignored
      exact .pure _
    · intro finished
      apply request_bind
      · apply positioned_forIn
        intro path state
        apply request_bind (unlinkRelative_positioned _ _ _ _)
        intro ignored
        exact .pure _
      · intro finished
        apply RequestProgram.call (by intro impossible; cases impossible)
        intro reply
        exact cleanup_footer _
  · exact cleanup_footer _

theorem closeOwned_positioned (parent : Directories.Parent) (stage : Directories.Fresh) :
    RequestProgram PositionedReads (closeOwned parent stage) := by
  unfold closeOwned
  apply RequestProgram.call (by intro impossible; cases impossible)
  intro reply
  apply RequestProgram.call (by intro impossible; cases impossible)
  intro reply
  apply RequestProgram.call (by intro impossible; cases impossible)
  intro reply
  exact .pure _

theorem prepare_positioned (bundle : Validation.Bundle) (input : Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) (parent : Directories.Parent) (stage : Directories.Fresh) :
    RequestProgram PositionedReads (prepare bundle input target stdoutHash stderrHash parent stage) := by
  unfold prepare
  apply request_bind ((hash_positioned _))
  intro policyDigest
  cases policyDigest with
  | error => exact .pure _
  | ok policyDigest =>
    dsimp only
    split
    · split
      · exact .pure _
      · apply positioned_bind_post ((PrivateStreams.authenticate_positioned _ _)) (Publication.authenticate_sized _ _)
        intro digest sized
        cases digest with
        | error => exact .pure _
        | ok digest =>
          dsimp only
          apply request_bind (fill_positioned _ _ _ _ _)
          intro filled
          cases filled with
          | error => exact .pure _
          | ok filled =>
            apply RequestProgram.call
            · intro impossible; cases impossible
            · intro reply
              dsimp only [Filesystem.Program.bind]
              split <;> exact .pure _
    · exact .pure _

theorem attempt_positioned (bundle : Validation.Bundle) (input : Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) : RequestProgram PositionedReads (attempt bundle input target stdoutHash stderrHash) := by
  unfold attempt
  apply request_bind (((PrivateStreams.absolute_positioned _)))
  intro display
  cases display with
  | error => exact .pure _
  | ok display =>
    apply request_bind ((parent_positioned _ _))
    intro parent
    cases parent with
    | error => exact .pure _
    | ok parent =>
      apply request_bind ((fresh_positioned _))
      intro fresh
      cases fresh with
      | error => exact ((close_positioned _ _))
      | ok stage =>
        apply request_bind ((prepare_positioned _ _ _ _ _ _ _))
        intro prepared
        cases prepared with
        | error =>
          apply request_bind ((cleanup_positioned _ _ _))
          intro ignored
          exact ((close_positioned _ _))
        | ok outcome =>
          apply RequestProgram.call (by intro impossible; cases impossible)
          intro renamed
          dsimp only [Filesystem.Program.bind]
          unfold finishCommit
          apply request_bind ((closeOwned_positioned _ _))
          intro ignored
          split
          · exact .pure _
          · split
            · exact .pure _
            · exact .pure _

theorem publish_positioned (request : GatewayWire.Request) (bundle : Validation.Bundle) (input : Input) :
    RequestProgram PositionedReads (publish request bundle input) := by
  unfold publish
  apply request_bind (((PrivateStreams.identify_positioned _)))
  intro identified
  cases identified with
  | error =>
    apply request_bind (((PrivateStreams.publicationDestination_positioned _ _ _)))
    intro target
    cases target with
    | error => exact .pure _
    | ok target => exact request_bind (attempt_positioned _ _ _ _ _) (fun _ => .pure _)
  | ok hashes =>
    cases hashes
    apply request_bind (((PrivateStreams.publicationDestination_positioned _ _ _)))
    intro target
    cases target with
    | error => exact .pure _
    | ok target => exact request_bind (attempt_positioned _ _ _ _ _) (fun _ => .pure _)


end LeanCage.Host.PrivateStreams.Publishing
