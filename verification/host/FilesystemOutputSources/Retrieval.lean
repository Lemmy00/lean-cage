import FilesystemOutputSources.Publication

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

theorem hash_only_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) {α : Type} {program : Filesystem.Program α}
    (source : Artifacts.HashOnly program) : BorrowPost kernel held handle (fun _ => True) program.lower := by
  induction source with
  | pure => exact .pure True.intro
  | call hash tail ih => exact passive_call laws held handle (by rw [hash]; simp [RetainsDescriptors]) ih

theorem retrieval_read_file_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (root : UInt64) (name : ByteArray) (limit : Nat) :
    BorrowPost kernel held handle (fun _ => True) (Retrieval.readFile root name limit).lower := by
  unfold Retrieval.readFile
  apply borrow_bind (copyAt_borrow laws held handle _ _ _)
  intro copied _
  exact .pure True.intro

theorem retrieval_optional_file_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (root : UInt64) (name : ByteArray) (limit : Nat) (present : Bool) :
    BorrowPost kernel held handle (fun _ => True) (Retrieval.optionalFile root name limit present).lower := by
  unfold Retrieval.optionalFile
  split
  · apply borrow_bind (retrieval_read_file_borrow laws held handle _ _ _)
    intro read _
    exact .pure True.intro
  · exact .pure True.intro

-- §FS-host-boundary.publication: Every recursive export read closes only its new FD;
-- traversal, content validation and digest collision branches retain the inherited channel.
theorem retrieval_collect_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (root : UInt64) (limits : Transport.Limits)
    (nodes : List Artifacts.Node) (state : Retrieval.Collected) :
    BorrowPost kernel held handle (fun _ => True) (Retrieval.collect uid root limits nodes state).run.lower := by
  induction nodes generalizing state with
  | nil => exact .pure True.intro
  | cons node rest ih =>
    unfold Retrieval.collect
    split
    · exact .pure True.intro
    · cases node with
      | omitted => exact ih _
      | directory path =>
        apply checked_bind_borrow
        · exact publication_under_borrow laws held handle _ _ _ _ _ (fun _ => .pure True.intro)
        · intro ignored
          exact ih _
      | file path executable size digest =>
        dsimp only
        split
        · exact .pure True.intro
        · split
          · apply checked_bind_borrow
            · exact publication_under_borrow laws held handle _ _ _ _ _ (fun _ => copyAt_borrow laws held handle _ _ _)
            · intro copied
              split
              · exact .pure True.intro
              · apply checked_bind_borrow
                · exact hash_borrow laws held handle _
                · intro hashed
                  split
                  · exact .pure True.intro
                  · split
                    · exact ih _
                    · split
                      · exact ih _
                      · exact .pure True.intro
          · exact .pure True.intro

theorem retrieval_export_blobs_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (stage : UInt64) (limits : Transport.Limits) (raw : ByteArray) :
    BorrowPost kernel held handle (fun _ => True) (Retrieval.exportBlobs uid stage limits raw).lower := by
  unfold Retrieval.exportBlobs
  split
  · exact .pure True.intro
  · apply borrow_bind (directoryOpen_borrow laws held handle _ _ _)
    intro opened fresh
    cases opened with
    | error => exact .pure True.intro
    | ok root =>
      apply borrow_bind (retrieval_collect_borrow laws held handle _ _ _ _ _)
      intro collected _
      apply borrow_bind (close_borrow laws root.fd held handle collected (Ne.symm fresh))
      intro closed _
      exact .pure True.intro

theorem retrieval_manifest_blobs_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (stage : UInt64) (limits : Transport.Limits)
    (manifest : Option ByteArray) :
    BorrowPost kernel held handle (fun _ => True) (Retrieval.manifestBlobs uid stage limits manifest).lower := by
  cases manifest with
  | none => exact .pure True.intro
  | some manifest => exact retrieval_export_blobs_borrow laws held handle _ _ _ _

theorem retrieval_result_json_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (root : UInt64) (metadata : GatewayWire.Value) :
    BorrowPost kernel held handle (fun _ => True) (Retrieval.resultJson root metadata).lower := by
  unfold Retrieval.resultJson
  split
  · exact .pure True.intro
  · split
    · exact .pure True.intro
    · apply borrow_bind (retrieval_read_file_borrow laws held handle _ _ _)
      intro actual _
      exact .pure True.intro

theorem retrieval_marker_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (root : UInt64) :
    BorrowPost kernel held handle (fun _ => True) (Retrieval.readMarker root).lower := by
  unfold Retrieval.readMarker
  apply borrow_bind (passive_borrow laws held handle _ (by simp [RetainsDescriptors]))
  intro reply _
  split <;> exact .pure True.intro

theorem retrieval_verify_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (bundle : Validation.Bundle) (wire supplied : ByteArray) :
    BorrowPost kernel held handle (fun _ => True) (Publication.verify bundle wire supplied).lower := by
  unfold Publication.verify
  split
  · exact .pure True.intro
  · apply borrow_bind (authentication_borrow laws held handle _ _)
    intro expected _
    cases expected with
    | error => exact .pure True.intro
    | ok expected =>
      apply borrow_bind (passive_borrow laws held handle _ (by simp [RetainsDescriptors]))
      intro compared _
      repeat' first | exact .pure True.intro | split

theorem retrieval_policy_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (bundle : Validation.Bundle) (root : UInt64) (envelope : Retrieval.Envelope) :
    BorrowPost kernel held handle (fun _ => True) (Retrieval.storedPolicy bundle root envelope).run.lower := by
  unfold Retrieval.storedPolicy
  apply checked_bind_borrow
  · exact retrieval_read_file_borrow laws held handle _ _ _
  · intro raw
    apply checked_bind_borrow
    · exact hash_borrow laws held handle _
    · intro digest
      split
      · exact .pure True.intro
      · apply checked_bind_borrow
        · exact .pure True.intro
        · intro value
          apply checked_bind_borrow
          · exact .pure True.intro
          · intro policy
            split <;> exact .pure True.intro

theorem retrieval_validate_metadata_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (bundle : Validation.Bundle) (envelope : Retrieval.Envelope)
    (policy : Policy.Accepted) (received : Transport.Result) :
    BorrowPost kernel held handle (fun _ => True)
      (Retrieval.validateMetadata bundle envelope policy received).run.lower := by
  unfold Retrieval.validateMetadata
  apply checked_bind_borrow
  · exact .pure True.intro
  · intro expected
    apply checked_bind_borrow
    · exact hash_only_borrow laws held handle (Artifacts.validate_hashOnly _ _)
    · intro validated
      split
      · exact .pure True.intro
      · apply checked_bind_borrow
        · exact outcome_identify_borrow laws held handle _
        · intro hashes
          dsimp only
          split <;> exact .pure True.intro

theorem retrieval_complete_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (root : UInt64) (bundle : Validation.Bundle)
    (envelope : Retrieval.Envelope) (policy : Policy.Accepted) (raw : Option ByteArray) :
    BorrowPost kernel held handle (fun _ => True)
      (Retrieval.completeMetadata uid root bundle envelope policy raw).run.lower := by
  unfold Retrieval.completeMetadata
  split
  · split
    · apply checked_bind_borrow
      · exact retrieval_optional_file_borrow laws held handle _ _ _ _
      · intro stored
        apply checked_bind_borrow
        · exact retrieval_read_file_borrow laws held handle _ _ _
        · intro stdout
          apply checked_bind_borrow
          · exact retrieval_read_file_borrow laws held handle _ _ _
          · intro stderr
            split
            · exact .pure True.intro
            · apply checked_bind_borrow
              · exact retrieval_optional_file_borrow laws held handle _ _ _ _
              · intro manifest
                apply checked_bind_borrow
                · exact retrieval_manifest_blobs_borrow laws held handle _ _ _ _
                · intro blobs
                  exact retrieval_validate_metadata_borrow laws held handle _ _ _ _
    · exact .pure True.intro
  · exact .pure True.intro

theorem retrieval_stored_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (bundle : Validation.Bundle) (parent : Directories.Parent)
    (target : Directories.Opened) (identity : Option String) :
    BorrowPost kernel held handle (fun _ => True) (Retrieval.readStored bundle parent target identity).run.lower := by
  unfold Retrieval.readStored
  apply checked_bind_borrow
  · exact retrieval_read_file_borrow laws held handle _ _ _
  · intro wire
    apply checked_bind_borrow
    · exact retrieval_marker_borrow laws held handle _
    · intro marker
      apply checked_bind_borrow
      · exact retrieval_verify_borrow laws held handle _ _ _
      · intro ignored
        apply checked_bind_borrow
        · exact .pure True.intro
        · intro envelope
          split
          · exact .pure True.intro
          · apply checked_bind_borrow
            · exact retrieval_policy_borrow laws held handle _ _ _
            · intro policy
              apply checked_bind_borrow
              · exact retrieval_result_json_borrow laws held handle _ _
              · intro ignored
                apply checked_bind_borrow
                · exact retrieval_optional_file_borrow laws held handle _ _ _ _
                · intro raw
                  split
                  · exact retrieval_complete_borrow laws held handle _ _ _ _ _ _
                  · exact .pure True.intro

theorem retrieval_destination_borrow {kernel : Contract} (held : UInt64) (handle : Handle)
    (request : GatewayWire.Request) (bundle : Validation.Bundle) :
    BorrowPost kernel held handle (fun _ => True) (Retrieval.destination request bundle).lower := by
  unfold Retrieval.destination
  dsimp only
  split
  · split
    · exact .pure True.intro
    · apply borrow_bind (publication_destination_borrow held handle _ _ _)
      intro target _
      exact .pure True.intro
  · exact .pure True.intro

theorem retrieval_at_destination_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (bundle : Validation.Bundle) (path : ByteArray) (identity : Option String) :
    BorrowPost kernel held handle (fun _ => True) (Retrieval.atDestination bundle path identity).lower := by
  unfold Retrieval.atDestination
  apply borrow_bind (directory_parent_borrow laws held handle _ _)
  intro parent freshParent
  cases parent with
  | error => exact .pure True.intro
  | ok parent =>
    apply borrow_bind (public_at_borrow laws held handle _ _ _ _)
    intro target freshTarget
    cases target with
    | error =>
      apply borrow_weaken (close_borrow laws parent.directory.fd held handle _ (Ne.symm freshParent))
      intro _ _; trivial
    | ok target =>
      apply borrow_bind (retrieval_stored_borrow laws held handle _ _ _ _)
      intro observed _
      apply borrow_bind (close_borrow laws target.fd held handle observed (Ne.symm freshTarget))
      intro closed _
      apply borrow_weaken (close_borrow laws parent.directory.fd held handle closed (Ne.symm freshParent))
      intro _ _; trivial

theorem retrieval_report_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (request : GatewayWire.Request) (bundle : Validation.Bundle) :
    BorrowPost kernel held handle (fun _ => True) (Retrieval.report request bundle).lower := by
  unfold Retrieval.report
  split
  · exact .pure True.intro
  · apply borrow_bind (retrieval_destination_borrow held handle _ _)
    intro selected _
    cases selected with
    | error => exact .pure True.intro
    | ok selected => exact retrieval_at_destination_borrow laws held handle _ _ _

end LeanCage.Host.Kernel.Lowered
