import FilesystemOutputSources.Retrieval
import FilesystemSnapshotBorrowing
import FilesystemChannelVM

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

variable {kernel : Contract} {sourceProgram : Program UInt32} {runtime : ActorRuntime kernel sourceProgram}

theorem actor_checked_bind {actor : ActorId} {held : UInt64} {handle : Handle}
    {α β : Type} (first : Checked α) (next : α → Checked β) {pre : Result α → Prop}
    (source : ActorBorrowPost runtime actor held handle pre (PrimitiveFilesystem.lower first.run))
    (tail : ∀ value, pre (.ok value) →
      ActorBorrowPost runtime actor held handle (fun _ => True) (PrimitiveFilesystem.lower (next value).run)) :
    ActorBorrowPost runtime actor held handle (fun _ => True) (PrimitiveFilesystem.lower ((first >>= next).run)) := by
  change ActorBorrowPost runtime actor held handle (fun _ => True)
    (PrimitiveFilesystem.lower (first.run.bind (ExceptT.bindCont next)))
  apply actor_bind source
  intro result permitted
  cases result with
  | error => exact .pure True.intro
  | ok value => exact tail value permitted

theorem actor_lift_borrow {actor : ActorId} {held : UInt64} {handle : Handle}
    {α : Type} (program : Program α) {pre : α → Prop}
    (source : ActorBorrowPost runtime actor held handle pre (PrimitiveFilesystem.lower program)) :
    ActorBorrowPost runtime actor held handle (fun _ => True)
      (PrimitiveFilesystem.lower (ExceptT.lift program : Checked α).run) := by
  apply actor_bind source
  intro value _
  exact .pure True.intro

theorem validator_finish_borrow (laws : DescriptorContract kernel)
    (actor : ActorId) (held : UInt64) (handle : Handle) (directory : RunDirectory.Owned)
    (observed : Validation.ChildObservation)
    (fresh : directory.directory.fd ≠ held ∧ directory.container.fd ≠ held) :
    ActorBorrowPost runtime actor held handle (fun _ => True)
      (PrimitiveFilesystem.lower (Validation.finishValidation directory observed)) := by
  unfold Validation.finishValidation
  apply actor_bind (first := fun _ => True)
  · apply actor_filesystem actor
    split
    · exact run_cleanup_borrow laws held handle directory fresh
    · exact run_release_borrow laws held handle directory fresh
  · intro _ _
    exact .pure True.intro

-- §FS-host-boundary.caller: The validator's actual create/write/spawn/read/wait/release
-- source preserves raw caller channels under the individual parent-SDK descriptor laws.
theorem validator_borrow (laws : DescriptorContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (raw : handle.rawOwned = true)
    (bundle : Validation.Bundle) (bytes : ByteArray) :
    ActorBorrowPost runtime actor held handle (fun _ => True)
      (PrimitiveFilesystem.lower (Validation.validateCopied bundle bytes)) := by
  unfold Validation.validateCopied
  apply actor_bind (actor_filesystem actor (run_create_borrow laws held handle))
  intro temporary fresh
  cases temporary with
  | error => exact .pure True.intro
  | ok directory =>
    apply actor_bind (actor_filesystem actor (writeNew_borrow laws held handle _ _ _ _))
    intro written _
    cases written with
    | error =>
      apply actor_bind (actor_filesystem actor (run_cleanup_borrow laws held handle directory fresh))
      intro _ _
      exact .pure True.intro
    | ok writtenUnit =>
      apply actor_bind (runtime_only_borrow sdk actor held handle raw
        (.call (.spawn _) _ (by trivial) (fun _ => .pure _)))
      intro child _
      apply actor_bind (runtime_only_borrow sdk actor held handle raw (observe_child_runtime_only bytes child))
      intro observed _
      exact validator_finish_borrow laws actor held handle directory observed fresh

theorem policy_prepare_borrow (laws : DescriptorContract kernel)
    (directories : DirectoryRetirementContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (raw : handle.rawOwned = true)
    (request : GatewayWire.Request) (bundle : Validation.Bundle) :
    ActorBorrowPost runtime actor held handle (fun _ => True)
      (PrimitiveFilesystem.lower (preparePolicy request bundle).run) := by
  unfold preparePolicy
  apply actor_checked_bind
  · exact actor_filesystem actor (policy_load_borrow laws held handle _)
  · intro bytes _
    apply actor_checked_bind
    · exact validator_borrow laws sdk actor held handle raw bundle bytes
    · intro value _
      apply actor_checked_bind (pre := fun _ => True)
      · exact .pure True.intro
      · intro accepted _
        apply actor_checked_bind
        · exact actor_filesystem actor (snapshot_freeze_borrow laws directories held handle _ _ _)
        · intro frozen _
          apply actor_checked_bind (pre := fun _ => True)
          · exact .pure True.intro
          · intro bound _
            apply actor_checked_bind
            · exact validator_borrow laws sdk actor held handle raw bundle bound.raw
            · intro validated _
              split
              · exact .pure True.intro
              · apply actor_checked_bind (pre := fun _ => True)
                · exact .pure True.intro
                · intro final _
                  split <;> exact .pure True.intro

theorem dispatch_image_borrow (laws : DescriptorContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (raw : handle.rawOwned = true)
    (request : String) (bundle : Validation.Bundle) (preflight : Bool) (policy : Policy.Accepted)
    (run : RunDirectory.Owned) (duration : Nat) (transport : Transport.State) (image : Result Unit) :
    ActorBorrowPost runtime actor held handle (fun _ => True)
      (PrimitiveFilesystem.lower (dispatchImage request bundle preflight policy run duration transport image)) := by
  cases image with
  | error => exact .pure True.intro
  | ok =>
    unfold dispatchImage
    apply actor_bind (channel_borrow (channel_lower
      (VirtualMachine.channel_run laws sdk actor held handle raw bundle run.path duration transport)))
    intro vm _
    exact actor_filesystem actor (hash_only_borrow laws held handle (ReceiveProofs.receive_hashOnly _ _ _ _ _))

theorem cleanup_run_borrow (laws : DescriptorContract kernel)
    (actor : ActorId) (held : UInt64) (handle : Handle) (run : RunDirectory.Owned) (input : Publication.Input)
    (fresh : run.directory.fd ≠ held ∧ run.container.fd ≠ held) :
    ActorBorrowPost runtime actor held handle (fun _ => True) (PrimitiveFilesystem.lower (cleanupRun run input)) := by
  unfold cleanupRun
  split
  · apply actor_bind (actor_filesystem actor (close_effect_borrow laws held handle _ fresh.1))
    intro _ _
    apply actor_bind (actor_filesystem actor (close_effect_borrow laws held handle _ fresh.2))
    intro _ _
    exact .pure True.intro
  · exact actor_filesystem actor (run_cleanup_borrow laws held handle _ fresh)

theorem duration_borrow (actor : ActorId) (held : UInt64) (handle : Handle)
    (request : GatewayWire.Request) (policy : Policy.Accepted) (override : Option Nat) :
    ActorBorrowPost runtime actor held handle (fun _ => True)
      (PrimitiveFilesystem.lower (requestDuration request policy override).run) := by
  unfold requestDuration
  split
  · exact .pure True.intro
  · split <;> exact .pure True.intro

theorem execute_run_borrow (laws : DescriptorContract kernel)
    (directories : DirectoryRetirementContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (raw : handle.rawOwned = true)
    (request : GatewayWire.Request) (bundle : Validation.Bundle) (override : Option Nat) :
    ActorBorrowPost runtime actor held handle (fun _ => True)
      (PrimitiveFilesystem.lower (executeRun request bundle override).run) := by
  unfold executeRun
  apply actor_checked_bind
  · exact policy_prepare_borrow laws directories sdk actor held handle raw request bundle
  · intro prepared _
    rcases prepared with ⟨policy, frozen⟩
    apply actor_checked_bind
    · exact actor_filesystem actor (directoryRandom_borrow laws held handle _ _ _)
    · intro random _
      apply actor_checked_bind
      · exact duration_borrow actor held handle _ _ _
      · intro duration _
        apply actor_checked_bind (pre := fun _ => True)
        · exact .pure True.intro
        · intro transport _
          apply actor_checked_bind
          · exact actor_filesystem actor (run_create_borrow laws held handle)
          · intro run fresh
            apply actor_checked_bind
            · exact actor_lift_borrow _ (actor_filesystem actor (image_create_borrow laws held handle _ _ _))
            · intro image _
              apply actor_checked_bind
              · exact actor_lift_borrow _ (dispatch_image_borrow laws sdk actor held handle raw _ _ _ _ _ _ _ _)
              · intro input _
                apply actor_checked_bind
                · exact actor_lift_borrow _ (cleanup_run_borrow laws actor held handle run input fresh)
                · intro ignored _
                  apply actor_checked_bind
                  · exact actor_lift_borrow _ (actor_filesystem actor (publication_publish_borrow laws held handle _ _ _))
                  · intro published _
                    exact .pure True.intro

end LeanCage.Host.Kernel.Lowered
