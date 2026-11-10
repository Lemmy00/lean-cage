import RetrievalProofs.Directories

namespace LeanCage.Host.Retrieval

open Filesystem

theorem readFile_readOnly (root : UInt64) (name : ByteArray) (limit : Nat) :
    ReadOnly (readFile root name limit) := by
  unfold readFile
  exact readOnly_bind (readOnly_snapshot (Snapshot.copyAt_input _ _ _)) (fun _ => .pure _)

theorem optionalFile_readOnly (root : UInt64) (name : ByteArray) (limit : Nat) (present : Bool) :
    ReadOnly (optionalFile root name limit present) := by
  unfold optionalFile
  split
  · exact readOnly_bind (readFile_readOnly _ _ _) (fun _ => .pure _)
  · exact .pure _

theorem collect_readOnly (uid : Nat) (root : UInt64) (limits : Transport.Limits)
    (nodes : List Artifacts.Node) (state : Collected) : ReadOnly (collect uid root limits nodes state).run := by
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
        apply readOnly_checked_bind (under_readOnly _ _ _ _ (fun _ => .pure _))
        intro value
        exact ih _
      | file path executable size digest =>
        dsimp only
        split
        · exact .pure _
        · split
          · apply readOnly_checked_bind (under_readOnly _ _ _ _
              (fun _ => readOnly_snapshot (Snapshot.copyAt_input _ _ _)))
            intro copied
            split
            · exact .pure _
            · apply readOnly_checked_bind (readOnly_snapshot (Snapshot.hash_input _))
              intro hashed
              split
              · exact .pure _
              · split
                · exact ih _
                · split
                  · exact ih _
                  · exact .pure _
          · exact .pure _

theorem exportBlobs_readOnly (uid : Nat) (stage : UInt64) (limits : Transport.Limits) (raw : ByteArray) :
    ReadOnly (exportBlobs uid stage limits raw) := by
  unfold exportBlobs
  split
  · exact .pure _
  · apply readOnly_bind (openAt_readOnly _ _ _)
    intro opened
    cases opened with
    | error => exact .pure _
    | ok root =>
      apply readOnly_bind (collect_readOnly _ _ _ _ _)
      intro collected
      apply readOnly_bind (readOnly_snapshot (Snapshot.closeResult_input _ _))
      intro closed
      exact .pure _

theorem resultJson_readOnly (root : UInt64) (metadata : GatewayWire.Value) :
    ReadOnly (resultJson root metadata) := by
  unfold resultJson
  split
  · exact .pure _
  · split
    · exact .pure _
    · exact readOnly_bind (readFile_readOnly _ _ _) (fun _ => .pure _)

theorem readMarker_readOnly (target : UInt64) : ReadOnly (readMarker target) := by
  unfold readMarker
  apply ReadOnly.call (by change (Publication.markerMagic.size + 32).toUInt64.toNat ≤ 40; decide)
  intro reply
  dsimp only [Filesystem.Program.bind]
  split <;> exact .pure _

theorem storedPolicy_readOnly (bundle : Validation.Bundle) (target : UInt64) (envelope : Envelope) :
    ReadOnly (storedPolicy bundle target envelope).run := by
  unfold storedPolicy
  apply readOnly_checked_bind (readFile_readOnly _ _ _)
  intro raw
  apply readOnly_checked_bind (readOnly_snapshot (Snapshot.hash_input _))
  intro digest
  split
  · exact .pure _
  · apply readOnly_checked_bind (ReadOnly.pure _)
    intro value
    apply readOnly_checked_bind (ReadOnly.pure _)
    intro policy
    split <;> exact .pure _

theorem identify_readOnly (outcome : Outcome) : ReadOnly outcome.identify := by
  unfold Outcome.identify
  split
  · exact .pure _
  · apply readOnly_bind (readOnly_snapshot (Snapshot.hash_input _))
    intro stdout
    cases stdout with
    | error => exact .pure _
    | ok stdout => exact readOnly_bind (readOnly_snapshot (Snapshot.hash_input _)) (fun _ => .pure _)

theorem manifestBlobs_readOnly (uid : Nat) (target : UInt64) (limits : Transport.Limits)
    (manifest : Option ByteArray) : ReadOnly (manifestBlobs uid target limits manifest) := by
  cases manifest with
  | none => exact .pure _
  | some => exact exportBlobs_readOnly _ _ _ _

theorem validateMetadata_readOnly (bundle : Validation.Bundle) (envelope : Envelope)
    (policy : Policy.Accepted) (received : Transport.Result) :
    ReadOnly (validateMetadata bundle envelope policy received).run := by
  unfold validateMetadata
  apply readOnly_checked_bind (ReadOnly.pure _)
  intro expected
  apply readOnly_checked_bind (readOnly_hashOnly (Artifacts.validate_hashOnly _ _))
  intro validated
  split
  · exact .pure _
  · apply readOnly_checked_bind (identify_readOnly _)
    intro hashes
    dsimp only
    split <;> exact .pure _

theorem completeMetadata_readOnly (uid : Nat) (target : UInt64) (bundle : Validation.Bundle)
    (envelope : Envelope) (policy : Policy.Accepted) (raw : Option ByteArray) :
    ReadOnly (completeMetadata uid target bundle envelope policy raw).run := by
  unfold completeMetadata
  split
  · split
    · apply readOnly_checked_bind (optionalFile_readOnly _ _ _ _)
      intro stored
      apply readOnly_checked_bind (readFile_readOnly _ _ _)
      intro stdout
      apply readOnly_checked_bind (readFile_readOnly _ _ _)
      intro stderr
      split
      · exact .pure _
      · apply readOnly_checked_bind (optionalFile_readOnly _ _ _ _)
        intro manifest
        apply readOnly_checked_bind (manifestBlobs_readOnly _ _ _ _)
        intro blobs
        exact validateMetadata_readOnly _ _ _ _
    · exact .pure _
  · exact .pure _

theorem readStored_readOnly (bundle : Validation.Bundle) (parent : Directories.Parent)
    (target : Directories.Opened) (identity : Option String) :
    ReadOnly (readStored bundle parent target identity).run := by
  unfold readStored
  apply readOnly_checked_bind (readFile_readOnly _ _ _)
  intro wire
  apply readOnly_checked_bind (readMarker_readOnly _)
  intro marker
  apply readOnly_checked_bind (verify_readOnly _ _ _)
  intro verified
  apply readOnly_checked_bind (ReadOnly.pure _)
  intro envelope
  split
  · exact .pure _
  · apply readOnly_checked_bind (storedPolicy_readOnly _ _ _)
    intro policy
    apply readOnly_checked_bind (resultJson_readOnly _ _)
    intro json
    apply readOnly_checked_bind (optionalFile_readOnly _ _ _ _)
    intro raw
    split
    · exact completeMetadata_readOnly _ _ _ _ _ _
    · exact .pure _

theorem destination_readOnly (request : GatewayWire.Request) (bundle : Validation.Bundle) :
    ReadOnly (destination request bundle) := by
  unfold destination
  dsimp only
  split
  · split
    · exact .pure _
    · exact readOnly_bind (publicationDestination_readOnly _ _ _) (fun _ => .pure _)
  · exact .pure _

theorem atDestination_readOnly (bundle : Validation.Bundle) (path : ByteArray) (identity : Option String) :
    ReadOnly (atDestination bundle path identity) := by
  unfold atDestination
  apply readOnly_bind (parent_readOnly _)
  intro parent
  cases parent with
  | error => exact .pure _
  | ok parent =>
    apply readOnly_bind (publicAt_readOnly _ _ _)
    intro target
    cases target with
    | error => exact readOnly_snapshot (Snapshot.closeResult_input _ _)
    | ok target =>
      apply readOnly_bind (readStored_readOnly _ _ _ _)
      intro observed
      apply readOnly_bind (readOnly_snapshot (Snapshot.closeResult_input _ _))
      intro closed
      exact readOnly_snapshot (Snapshot.closeResult_input _ _)

theorem report_readOnly (request : GatewayWire.Request) (bundle : Validation.Bundle) :
    ReadOnly (report request bundle) := by
  unfold report
  split
  · exact .pure _
  · apply readOnly_bind (destination_readOnly _ _)
    intro selected
    cases selected with
    | error => exact .pure _
    | ok selected => exact atDestination_readOnly _ _ _

-- §FS-host-boundary.publication: Errors, interruptions and a lost final operation remain read-only.
theorem report_no_write_prefix (request : GatewayWire.Request) (bundle : Validation.Bundle)
    {events : List (Request × Option Reply)} (run : Prefix (report request bundle) events) :
    ∀ event ∈ events, Allowed event.1 := readOnly_prefix (report_readOnly _ _) run

end LeanCage.Host.Retrieval
