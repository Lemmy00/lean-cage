import PublicationProofs.ExclusiveFrontier
import FilesystemPublicationPreparing

namespace LeanCage.Host.Kernel.PublicationExclusive
open Filesystem

private theorem readonly_no_exclusive {α : Type} {program : Filesystem.Program α}
    (source : Retrieval.ReadOnly program) : RequestProgram (fun request => ¬ ExclusiveFile request) program :=
  request_weaken (read_only_namespace_passive source) (fun _ => passive_not_exclusive)

private theorem ensure_no_exclusive (uid : Nat) (parent : UInt64) (name : ByteArray) :
    RequestProgram (fun request => ¬ ExclusiveFile request) (Directories.ensureAt uid parent name) := by
  unfold Directories.ensureAt
  apply RequestProgram.call (by simp [ExclusiveFile])
  intro reply
  dsimp only [Filesystem.Program.bind]
  repeat' first | exact .pure _ | split | exact readonly_no_exclusive (Retrieval.openAt_readOnly _ _ _)

private theorem public_at_no_exclusive (uid : Nat) (parent : UInt64) (name : ByteArray) (create : Bool) :
    RequestProgram (fun request => ¬ ExclusiveFile request) (Directories.publicAt uid parent name create) := by
  cases create <;> unfold Directories.publicAt
  all_goals simp only [Bool.false_eq_true, ↓reduceIte]
  · apply request_bind (readonly_no_exclusive (Retrieval.openAt_readOnly _ _ _))
    intro result
    cases result with
    | error => exact .pure _
    | ok opened =>
      apply request_bind (readonly_no_exclusive (Retrieval.readOnly_snapshot (Snapshot.publicHandle_input _)))
      intro allowed
      exact .pure _
  · apply request_bind (ensure_no_exclusive _ _ _)
    intro result
    cases result with
    | error => exact .pure _
    | ok opened =>
      apply request_bind (readonly_no_exclusive (Retrieval.readOnly_snapshot (Snapshot.publicHandle_input _)))
      intro allowed
      exact .pure _

private theorem descend_no_exclusive (uid : Nat) (create : Bool) (current : Directories.Opened)
    (names : List ByteArray) :
    RequestProgram (fun request => ¬ ExclusiveFile request) (Directories.descend uid create current names) := by
  induction names generalizing current with
  | nil => exact .pure _
  | cons name rest ih =>
    unfold Directories.descend
    apply request_bind (public_at_no_exclusive _ _ _ _)
    intro next
    apply request_bind (readonly_no_exclusive (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _)))
    intro closed
    cases closed with
    | error =>
      cases next with
      | error => exact .pure _
      | ok => exact readonly_no_exclusive (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
    | ok => exact ih _

theorem parent_no_exclusive (path : ByteArray) (create : Bool) :
    RequestProgram (fun request => ¬ ExclusiveFile request) (Directories.parent path create) := by
  unfold Directories.parent
  apply request_bind (readonly_no_exclusive (Retrieval.readOnly_snapshot (Snapshot.sourceStart_input _)))
  intro selected
  cases selected with
  | error => exact .pure _
  | ok selected =>
    dsimp only
    split
    · split
      · exact readonly_no_exclusive (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
      · apply RequestProgram.call (by simp [ExclusiveFile])
        intro identity
        dsimp only [Filesystem.Program.bind]
        split
        · exact readonly_no_exclusive (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
        · apply request_bind (readonly_no_exclusive (Retrieval.inspect_readOnly _ _))
          intro base
          cases base with
          | error => exact .pure _
          | ok base =>
            apply request_bind (descend_no_exclusive _ _ _ _)
            intro result
            exact .pure _
    · exact readonly_no_exclusive (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))

theorem fresh_no_exclusive (parent : Directories.Parent) :
    RequestProgram (fun request => ¬ ExclusiveFile request) (Directories.fresh parent) := by
  unfold Directories.fresh
  apply request_bind (readonly_no_exclusive (Retrieval.openAt_readOnly _ _ _))
  intro result
  cases result with
  | error => exact .pure _
  | ok container =>
    apply request_bind
    · apply request_weaken (RunDirectory.directoryChild_requests _ _ _)
      intro request allowed
      cases operation : request.op <;>
        simp_all [RunDirectory.BeforeMarkRequest, RunDirectory.DirectoryRequest, ExclusiveFile, directoryFlags, newFileFlags]
    · intro result
      cases result with
      | error => exact readonly_no_exclusive (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
      | ok => exact .pure _

private theorem unlink_relative_no_exclusive (uid : Nat) (root : UInt64) (parts : List String) (directory : Bool) :
    RequestProgram (fun request => ¬ ExclusiveFile request) (Publication.unlinkRelative uid root parts directory) := by
  unfold Publication.unlinkRelative
  split
  · apply request_bind
    · apply Publication.under_no_exclusive
      intro parent
      apply RequestProgram.call (by intro impossible; cases impossible.1)
      intro reply
      dsimp only [Filesystem.Program.bind]
      split <;> exact .pure _
    · intro ignored
      exact .pure _
  · exact .pure _

private theorem unit_loop_no_exclusive {α : Type} (items : List α)
    (action : α → Filesystem.Program Unit)
    (quiet : ∀ item ∈ items, RequestProgram (fun request => ¬ ExclusiveFile request) (action item)) :
    RequestProgram (fun request => ¬ ExclusiveFile request) (do
      for item in items do action item
      pure ()) := by
  apply request_bind
  · apply request_forIn
    intro item member state
    exact request_bind (quiet item member) (fun _ => .pure _)
  · intro ignored
    exact .pure _

private theorem cleanup_export_no_exclusive (uid : Nat) (root : Directories.Opened) (input : Publication.Input) :
    RequestProgram (fun request => ¬ ExclusiveFile request) (Publication.cleanupExport uid root input) := by
  unfold Publication.cleanupExport
  apply request_bind
  · exact unit_loop_no_exclusive _ _ (fun _ _ => unlink_relative_no_exclusive _ _ _ _)
  · intro ignored
    apply request_bind
    · exact unit_loop_no_exclusive _ _ (fun _ _ => unlink_relative_no_exclusive _ _ _ _)
    · intro ignored
      apply RequestProgram.call (by intro impossible; cases impossible.1)
      intro reply
      exact .pure _

private theorem cleanup_footer_no_exclusive (stage : Directories.Fresh) :
    RequestProgram (fun request => ¬ ExclusiveFile request) (Publication.cleanupFooter stage) := by
  unfold Publication.cleanupFooter
  apply request_bind
  · unfold Publication.cleanupStageFiles
    apply request_bind
    · apply request_forIn
      intro name member state
      apply RequestProgram.call (by intro impossible; cases impossible.1)
      intro reply
      exact .pure _
    · intro ignored
      exact .pure _
  · intro ignored
    repeat' first
      | exact .pure _
      | apply RequestProgram.call (by intro impossible; cases impossible.1); intro reply

theorem cleanup_no_exclusive (parent : Directories.Parent) (stage : Directories.Fresh) (input : Publication.Input) :
    RequestProgram (fun request => ¬ ExclusiveFile request) (Publication.cleanup parent stage input) := by
  rw [Publication.cleanup_source_shape]
  apply request_bind (readonly_no_exclusive (Retrieval.openAt_readOnly _ _ _))
  intro opened
  cases opened with
  | error => exact cleanup_footer_no_exclusive _
  | ok root =>
    exact request_bind (cleanup_export_no_exclusive _ _ _) (fun _ => cleanup_footer_no_exclusive _)

private theorem no_exclusive_last {α : Type} {program : Filesystem.Program α}
    (profile : RequestProgram (fun request => ¬ ExclusiveFile request) program)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix program (before ++ [(request, observed)])) (exclusive : ExclusiveFile request) : False :=
  request_prefix profile source (request, observed) (by simp) exclusive

-- §FS-host-boundary.ownership: Only the actual filling source can create
-- publisher files; selection, fresh-stage allocation and failed preparation
-- cleanup retain all real calls but cannot make an exclusive file request.
theorem preparing_of_exclusive {before : List Program.Event} {request : Request}
    (invocation : EntryPublicationCall before (.lost (.filesystem request))) (exclusive : ExclusiveFile request) :
    Nonempty (PublicationPreparing.Call before request) := by
  obtain ⟨host⟩ := PublicationOpening.host_opening_site invocation exclusive.1
  cases host.source.site with
  | selecting context inside active trace =>
    exact False.elim (no_exclusive_last (parent_no_exclusive _ _) active exclusive)
  | staging context inside active trace =>
    exact False.elim (no_exclusive_last (fresh_no_exclusive _) active exclusive)
  | filling context inside active trace =>
    exact ⟨PublicationPreparing.Call.of_opening_fill host context inside active trace⟩
  | cleaning context error preparing prepared inside active trace =>
    exact False.elim (no_exclusive_last (cleanup_no_exclusive _ _ _) active exclusive)

end LeanCage.Host.Kernel.PublicationExclusive
