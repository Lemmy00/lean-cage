import GatewayFileReadProfile
import RetrievalProofs.ReadOnly

namespace LeanCage.Host.PrivateStreams
open Filesystem Kernel Retrieval

-- §FS-host-boundary.publication: Stored observations use the same positional
-- file-copy implementation; source branch and error coverage are retained.
theorem positioned_checked_bind {α β : Type} {program : Retrieval.Checked α} {next : α → Retrieval.Checked β}
    (first : RequestProgram PositionedReads program.run)
    (tail : ∀ value, RequestProgram PositionedReads (next value).run) :
    RequestProgram PositionedReads ((program.bind next).run) := by
  simp only [ExceptT.bind, ExceptT.run, ExceptT.mk]
  apply request_bind first
  intro result
  cases result with
  | error => exact .pure _
  | ok value => exact tail value

theorem hash_only_positioned {α : Type} {program : Filesystem.Program α}
    (source : Artifacts.HashOnly program) : RequestProgram PositionedReads program := by
  induction source with
  | pure => exact .pure _
  | call hash tail ih =>
    apply RequestProgram.call _ ih
    intro reading
    rw [hash] at reading
    cases reading

theorem inspect_positioned (uid : Nat) (fd : UInt64) : RequestProgram PositionedReads (Directories.inspect uid fd) := by
  unfold Directories.inspect
  apply RequestProgram.call (by intro impossible; cases impossible)
  intro reply
  split
  · exact close_positioned _ _
  · split
    · exact .pure _
    · exact close_positioned _ _

theorem openAt_positioned (uid : Nat) (parent : UInt64) (name : ByteArray) :
    RequestProgram PositionedReads (Directories.openAt uid parent name) := by
  unfold Directories.openAt
  apply RequestProgram.call (by intro impossible; cases impossible)
  intro reply
  split
  · exact .pure _
  · exact inspect_positioned _ _

theorem publicAt_positioned (uid : Nat) (parent : UInt64) (name : ByteArray) :
    RequestProgram PositionedReads (Directories.publicAt uid parent name false) := by
  unfold Directories.publicAt
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply request_bind (openAt_positioned _ _ _)
  intro result
  cases result with
  | error => exact .pure _
  | ok opened =>
    apply request_bind (no_read_positioned (publicHandle_noRead _))
    intro allowed
    exact .pure _

theorem descend_positioned (uid : Nat) (current : Directories.Opened) (names : List ByteArray) :
    RequestProgram PositionedReads (Directories.descend uid false current names) := by
  induction names generalizing current with
  | nil => exact .pure _
  | cons name rest ih =>
    simp only [Directories.descend]
    apply request_bind (publicAt_positioned _ _ _)
    intro next
    apply request_bind (close_positioned _ _)
    intro closed
    cases closed with
    | error =>
      cases next with
      | error => exact .pure _
      | ok => exact close_positioned _ _
    | ok => exact ih _

theorem parent_positioned (path : ByteArray) : RequestProgram PositionedReads (Directories.parent path false) := by
  unfold Directories.parent
  apply request_bind (no_read_positioned (sourceStart_noRead _))
  intro selected
  cases selected with
  | error => exact .pure _
  | ok selected =>
    dsimp only
    split
    · split
      · exact close_positioned _ _
      · apply RequestProgram.call (by intro impossible; cases impossible)
        intro identity
        dsimp only [Filesystem.Program.bind]
        split
        · exact close_positioned _ _
        · apply request_bind (inspect_positioned _ _)
          intro base
          cases base with
          | error => exact .pure _
          | ok base =>
            apply request_bind (descend_positioned _ _ _)
            intro result
            exact .pure _
    · exact close_positioned _ _

theorem under_positioned {α : Type} (uid : Nat) (fd : UInt64) (names : List String)
    (action : UInt64 → Filesystem.Program (Result α)) (allowed : ∀ fd, RequestProgram PositionedReads (action fd)) :
    RequestProgram PositionedReads (Publication.under uid fd names false action) := by
  induction names generalizing fd with
  | nil => exact allowed fd
  | cons name rest ih =>
    simp only [Publication.under]
    split
    · exact .pure _
    · simp only [Bool.false_eq_true, ↓reduceIte]
      apply request_bind (openAt_positioned _ _ _)
      intro result
      cases result with
      | error => exact .pure _
      | ok child =>
        exact request_bind (ih child.fd) (fun _ => close_positioned _ _)

theorem absolute_positioned (path : ByteArray) : RequestProgram PositionedReads (Publication.absolute path) := by
  unfold Publication.absolute
  split
  · exact .pure _
  · split
    · exact .pure _
    · apply RequestProgram.call (by intro impossible; cases impossible)
      intro reply
      dsimp only [Filesystem.Program.bind]
      split
      · exact .pure _
      · split <;> exact .pure _

theorem publicationDestination_positioned (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (identity : String) : RequestProgram PositionedReads (Publication.destination request bundle identity) := by
  unfold Publication.destination
  dsimp only
  split <;> exact .pure _

theorem key_positioned (bundle : Validation.Bundle) : RequestProgram PositionedReads (Publication.authenticationKey bundle) := by
  unfold Publication.authenticationKey
  split
  · split
    · apply RequestProgram.call (by intro impossible; cases impossible)
      intro reply
      dsimp only [Filesystem.Program.bind]
      split
      · exact .pure _
      · apply RequestProgram.call (by intro impossible; cases impossible)
        intro opened
        dsimp only [Filesystem.Program.bind]
        split
        · apply RequestProgram.call (by intro impossible; cases impossible)
          intro privateReply
          dsimp only [Filesystem.Program.bind]
          split
          · exact close_positioned _ _
          · apply request_bind (request_bind (copy_opened_positioned _ _) (close_positioned _))
            intro copied
            cases copied with
            | error => exact .pure _
            | ok copied =>
              dsimp only
              split
              · exact .pure _
              · apply request_bind (hash_positioned _)
                intro hashed
                cases hashed with
                | error => exact .pure _
                | ok digest => dsimp only; split <;> exact .pure _
        · exact .pure _
    · exact .pure _
  · exact .pure _

theorem authenticate_positioned (bundle : Validation.Bundle) (wire : ByteArray) :
    RequestProgram PositionedReads (Publication.authenticate bundle wire) := by
  unfold Publication.authenticate
  split
  · exact .pure _
  · apply request_bind (key_positioned _)
    intro key
    cases key with
    | error => exact .pure _
    | ok key =>
      apply RequestProgram.call (by intro impossible; cases impossible)
      intro reply
      dsimp only [Filesystem.Program.bind]
      split <;> exact .pure _

theorem verify_positioned (bundle : Validation.Bundle) (wire supplied : ByteArray) :
    RequestProgram PositionedReads (Publication.verify bundle wire supplied) := by
  unfold Publication.verify
  split
  · exact .pure _
  · apply request_bind (authenticate_positioned _ _)
    intro expected
    cases expected with
    | error => exact .pure _
    | ok expected =>
      apply RequestProgram.call (by intro impossible; cases impossible)
      intro reply
      dsimp only [Filesystem.Program.bind]
      split
      · exact .pure _
      · split <;> exact .pure _


theorem readFile_positioned (root : UInt64) (name : ByteArray) (limit : Nat) :
    RequestProgram PositionedReads (readFile root name limit) := by
  unfold readFile
  exact request_bind (copy_at_positioned _ _ _) (fun _ => .pure _)

theorem optionalFile_positioned (root : UInt64) (name : ByteArray) (limit : Nat) (present : Bool) :
    RequestProgram PositionedReads (optionalFile root name limit present) := by
  unfold optionalFile
  split
  · exact request_bind (readFile_positioned _ _ _) (fun _ => .pure _)
  · exact .pure _

theorem collect_positioned (uid : Nat) (root : UInt64) (limits : Transport.Limits)
    (nodes : List Artifacts.Node) (state : Collected) : RequestProgram PositionedReads (collect uid root limits nodes state).run := by
  induction nodes generalizing state with
  | nil => exact .pure _
  | cons node rest ih =>
    simp only [collect]
    split
    · exact .pure _
    · cases node with
      | omitted => exact ih _
      | directory path =>
        dsimp only
        apply positioned_checked_bind (under_positioned _ _ _ _ (fun _ => .pure _))
        intro value
        exact ih _
      | file path executable size digest =>
        dsimp only
        split
        · exact .pure _
        · split
          · apply positioned_checked_bind (under_positioned _ _ _ _
              (fun _ => copy_at_positioned _ _ _))
            intro copied
            split
            · exact .pure _
            · apply positioned_checked_bind (hash_positioned _)
              intro hashed
              split
              · exact .pure _
              · split
                · exact ih _
                · split
                  · exact ih _
                  · exact .pure _
          · exact .pure _

theorem exportBlobs_positioned (uid : Nat) (stage : UInt64) (limits : Transport.Limits) (raw : ByteArray) :
    RequestProgram PositionedReads (exportBlobs uid stage limits raw) := by
  unfold exportBlobs
  split
  · exact .pure _
  · apply request_bind (openAt_positioned _ _ _)
    intro opened
    cases opened with
    | error => exact .pure _
    | ok root =>
      apply request_bind (collect_positioned _ _ _ _ _)
      intro collected
      apply request_bind (close_positioned _ _)
      intro closed
      exact .pure _

theorem resultJson_positioned (root : UInt64) (metadata : GatewayWire.Value) :
    RequestProgram PositionedReads (resultJson root metadata) := by
  unfold resultJson
  split
  · exact .pure _
  · split
    · exact .pure _
    · exact request_bind (readFile_positioned _ _ _) (fun _ => .pure _)

theorem readMarker_positioned (target : UInt64) : RequestProgram PositionedReads (readMarker target) := by
  unfold readMarker
  apply RequestProgram.call (by intro impossible; cases impossible)
  intro reply
  dsimp only [Filesystem.Program.bind]
  split <;> exact .pure _

theorem storedPolicy_positioned (bundle : Validation.Bundle) (target : UInt64) (envelope : Envelope) :
    RequestProgram PositionedReads (storedPolicy bundle target envelope).run := by
  unfold storedPolicy
  apply positioned_checked_bind (readFile_positioned _ _ _)
  intro raw
  apply positioned_checked_bind (hash_positioned _)
  intro digest
  split
  · exact .pure _
  · apply positioned_checked_bind (RequestProgram.pure _)
    intro value
    apply positioned_checked_bind (RequestProgram.pure _)
    intro policy
    split <;> exact .pure _

theorem identify_positioned (outcome : Outcome) : RequestProgram PositionedReads outcome.identify := by
  unfold Outcome.identify
  split
  · exact .pure _
  · apply request_bind (hash_positioned _)
    intro stdout
    cases stdout with
    | error => exact .pure _
    | ok stdout => exact request_bind (hash_positioned _) (fun _ => .pure _)

theorem manifestBlobs_positioned (uid : Nat) (target : UInt64) (limits : Transport.Limits)
    (manifest : Option ByteArray) : RequestProgram PositionedReads (manifestBlobs uid target limits manifest) := by
  cases manifest with
  | none => exact .pure _
  | some => exact exportBlobs_positioned _ _ _ _

theorem validateMetadata_positioned (bundle : Validation.Bundle) (envelope : Envelope)
    (policy : Policy.Accepted) (received : Transport.Result) :
    RequestProgram PositionedReads (validateMetadata bundle envelope policy received).run := by
  unfold validateMetadata
  apply positioned_checked_bind (RequestProgram.pure _)
  intro expected
  apply positioned_checked_bind (hash_only_positioned (Artifacts.validate_hashOnly _ _))
  intro validated
  split
  · exact .pure _
  · apply positioned_checked_bind (identify_positioned _)
    intro hashes
    dsimp only
    split <;> exact .pure _

theorem completeMetadata_positioned (uid : Nat) (target : UInt64) (bundle : Validation.Bundle)
    (envelope : Envelope) (policy : Policy.Accepted) (raw : Option ByteArray) :
    RequestProgram PositionedReads (completeMetadata uid target bundle envelope policy raw).run := by
  unfold completeMetadata
  split
  · split
    · apply positioned_checked_bind (optionalFile_positioned _ _ _ _)
      intro stored
      apply positioned_checked_bind (readFile_positioned _ _ _)
      intro stdout
      apply positioned_checked_bind (readFile_positioned _ _ _)
      intro stderr
      split
      · exact .pure _
      · apply positioned_checked_bind (optionalFile_positioned _ _ _ _)
        intro manifest
        apply positioned_checked_bind (manifestBlobs_positioned _ _ _ _)
        intro blobs
        exact validateMetadata_positioned _ _ _ _
    · exact .pure _
  · exact .pure _

theorem readStored_positioned (bundle : Validation.Bundle) (parent : Directories.Parent)
    (target : Directories.Opened) (identity : Option String) :
    RequestProgram PositionedReads (readStored bundle parent target identity).run := by
  unfold readStored
  apply positioned_checked_bind (readFile_positioned _ _ _)
  intro wire
  apply positioned_checked_bind (readMarker_positioned _)
  intro marker
  apply positioned_checked_bind (verify_positioned _ _ _)
  intro verified
  apply positioned_checked_bind (RequestProgram.pure _)
  intro envelope
  split
  · exact .pure _
  · apply positioned_checked_bind (storedPolicy_positioned _ _ _)
    intro policy
    apply positioned_checked_bind (resultJson_positioned _ _)
    intro json
    apply positioned_checked_bind (optionalFile_positioned _ _ _ _)
    intro raw
    split
    · exact completeMetadata_positioned _ _ _ _ _ _
    · exact .pure _

theorem destination_positioned (request : GatewayWire.Request) (bundle : Validation.Bundle) :
    RequestProgram PositionedReads (destination request bundle) := by
  unfold destination
  dsimp only
  split
  · split
    · exact .pure _
    · exact request_bind (publicationDestination_positioned _ _ _) (fun _ => .pure _)
  · exact .pure _

theorem atDestination_positioned (bundle : Validation.Bundle) (path : ByteArray) (identity : Option String) :
    RequestProgram PositionedReads (atDestination bundle path identity) := by
  unfold atDestination
  apply request_bind (parent_positioned _)
  intro parent
  cases parent with
  | error => exact .pure _
  | ok parent =>
    apply request_bind (publicAt_positioned _ _ _)
    intro target
    cases target with
    | error => exact close_positioned _ _
    | ok target =>
      apply request_bind (readStored_positioned _ _ _ _)
      intro observed
      apply request_bind (close_positioned _ _)
      intro closed
      exact close_positioned _ _

theorem report_positioned (request : GatewayWire.Request) (bundle : Validation.Bundle) :
    RequestProgram PositionedReads (report request bundle) := by
  unfold report
  split
  · exact .pure _
  · apply request_bind (destination_positioned _ _)
    intro selected
    cases selected with
    | error => exact .pure _
    | ok selected => exact atDestination_positioned _ _ _


end LeanCage.Host.PrivateStreams
