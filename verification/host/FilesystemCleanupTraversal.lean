import FilesystemCleanupStageSegment
import FilesystemCleanupParents

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

private theorem cleanup_loop_borrow {kernel : Contract} (descriptors : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) {α : Type} (uid : Nat) (root : UInt64)
    (items : List α) (path : α → Artifacts.ExportPath) (directory : Bool) :
    BorrowPost kernel held handle (fun _ => True) (forIn items () (fun item _ => do
      Publication.unlinkRelative uid root (path item).components directory
      pure (ForInStep.yield ()))).lower := by
  apply borrow_forIn
  intro item state
  apply borrow_bind (publication_unlink_relative_borrow descriptors held handle _ _ _ _)
  intro ignored _
  exact .pure True.intro

-- §FS-host-boundary.ownership: Interpret the selected typed cleanup path
-- on its SAME recorded raw prefix. Earlier loop iterations preserve the
-- retained root; actual child opens determine the current parent scope.
theorem relative_cleanup_parent {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (descriptors : DescriptorContract kernel)
    (actor : ActorId) (origin : OperationOrigin) (limit : Nat) {family : Family}
    (opens : PrivateDirectoryOpens kernel (fun index request reply before after =>
      origin index Reply (.filesystem request) reply before after ∧ index < limit) family)
    {α : Type} {uid : Nat} {root : UInt64} {items : List α} {path : α → Artifacts.ExportPath} {directory : Bool}
    {before : List (Request × Option Reply)} {request : Request}
    (source : Publication.RelativeCleanup uid root items path directory before request none)
    {raw : List Program.Event} (chunks : PrimitiveFilesystem.Chunks (before.map Program.filesystemPrefixEvent) raw)
    {ordinal : Nat} {first after : World}
    (history : ActorHistoryWith runtime actor origin ordinal first raw after)
    (bounded : ordinal + raw.length ≤ limit) {rootHandle : Handle} {scope : ObjectId}
    (live : first.handles root = some rootHandle) (privateRoot : family rootHandle.object = some scope) :
    ∃ parent, after.handles request.first = some parent ∧ family parent.object = some scope := by
  have trace : before.map Program.filesystemPrefixEvent =
      source.completed.map Program.filesystemEvent ++ source.inside.map Program.filesystemPrefixEvent := by
    exact (congrArg (List.map Program.filesystemPrefixEvent) source.trace).trans
      (by rw [List.map_append, completed_filesystem_events])
  rw [trace] at chunks
  obtain ⟨loopRaw, openingRaw, loopChunks, openingChunks, rawTrace⟩ := PrimitiveFilesystem.chunks_split _ _ chunks
  obtain ⟨middle, loopHistory, openingHistory⟩ := actor_with_split loopRaw openingRaw (rawTrace ▸ history)
  obtain ⟨loopEvents, loopSource, loopTrace⟩ :=
    PrimitiveFilesystem.chunks_filesystem_returns source.prepared loopChunks
  have kept := (history_borrow _ _ (cleanup_loop_borrow descriptors root rootHandle uid root source.earlier path directory)
    ⟨loopSource, actor_recorded_filesystem (loopTrace ▸ loopHistory)⟩ live).1
  have insideEmpty := Publication.relative_unlink_inside_empty source.active
  have insideTrace : source.inside = Publication.completed source.active.opening := by
    simpa only [insideEmpty, List.append_nil] using source.active.trace
  have actualChunks : PrimitiveFilesystem.Chunks (source.active.opening.map Program.filesystemEvent) openingRaw := by
    simpa only [insideTrace, completed_filesystem_events] using openingChunks
  obtain ⟨parent, reference, scope⟩ := publication_chain_private descriptors actor origin limit opens source.active.chain
    actualChunks openingHistory (by rw [rawTrace, List.length_append] at bounded; omega) kept privateRoot
  have descriptor : request.first = source.active.parent := congrArg Request.first source.active.operation
  exact ⟨parent, descriptor ▸ reference, scope⟩

private theorem files_borrow {kernel : Contract} (descriptors : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (uid : Nat) (root : UInt64) (files : List Artifacts.ValidatedFile) :
    BorrowPost kernel held handle (fun _ => True) (Publication.cleanupFiles uid root files).lower := by
  unfold Publication.cleanupFiles
  apply borrow_bind (cleanup_loop_borrow descriptors held handle uid root files (·.path) false)
  intro ignored _
  exact .pure True.intro

theorem cleanup_export_parent {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (descriptors : DescriptorContract kernel)
    (actor : ActorId) (origin : OperationOrigin) (limit : Nat) {family : Family}
    (opens : PrivateDirectoryOpens kernel (fun index request reply before after =>
      origin index Reply (.filesystem request) reply before after ∧ index < limit) family)
    {uid : Nat} {root : Directories.Opened} {input : Publication.Input}
    {before : List (Request × Option Reply)} {request : Request}
    (source : Publication.CleanupExportFrontier uid root input before request none)
    {raw : List Program.Event} (chunks : PrimitiveFilesystem.Chunks (before.map Program.filesystemPrefixEvent) raw)
    {ordinal : Nat} {first after : World}
    (history : ActorHistoryWith runtime actor origin ordinal first raw after)
    (bounded : ordinal + raw.length ≤ limit) {rootHandle : Handle} {scope : ObjectId}
    (live : first.handles root.fd = some rootHandle) (privateRoot : family rootHandle.object = some scope) :
    ∃ parent, after.handles request.first = some parent ∧ family parent.object = some scope := by
  cases source with
  | files source => exact relative_cleanup_parent descriptors actor origin limit opens source chunks history bounded live privateRoot
  | directories files completed inside source trace =>
    have rawShape : before.map Program.filesystemPrefixEvent =
        files.map Program.filesystemEvent ++ inside.map Program.filesystemPrefixEvent := by
      exact (congrArg (List.map Program.filesystemPrefixEvent) trace).trans
        (by rw [List.map_append, completed_filesystem_events])
    rw [rawShape] at chunks
    obtain ⟨filesRaw, insideRaw, filesChunks, insideChunks, rawTrace⟩ := PrimitiveFilesystem.chunks_split _ _ chunks
    obtain ⟨middle, filesHistory, insideHistory⟩ := actor_with_split filesRaw insideRaw (rawTrace ▸ history)
    obtain ⟨filesEvents, filesSource, filesTrace⟩ := PrimitiveFilesystem.chunks_filesystem_returns completed filesChunks
    have kept := (history_borrow _ _ (files_borrow descriptors root.fd rootHandle uid root.fd input.outcome.files)
      ⟨filesSource, actor_recorded_filesystem (filesTrace ▸ filesHistory)⟩ live).1
    exact relative_cleanup_parent descriptors actor origin limit opens source insideChunks insideHistory
      (by rw [rawTrace, List.length_append] at bounded; omega) kept privateRoot

theorem cleanup_export_component {uid : Nat} {root : Directories.Opened} {input : Publication.Input}
    {before : List (Request × Option Reply)} {request : Request}
    (source : Publication.CleanupExportFrontier uid root input before request none) :
    Directories.component request.left = true := by
  cases source with
  | files source => exact Publication.relative_unlink_component source.active source.item.path.valid.2.2.2
  | directories files completed inside source trace =>
    exact Publication.relative_unlink_component source.active source.item.valid.2.2.2

def FinalStageRemoval (stage : Directories.Fresh) (request : Request) : Prop :=
  request = {op := .unlinkAt, first := stage.container.fd, second := 512, left := stage.name}

structure FinalCleanupFrontier (parent : Directories.Parent) (stage : Directories.Fresh) (input : Publication.Input)
    (before : List (Request × Option Reply)) (request : Request) where
  opened : Result Directories.Opened
  opening : List (Request × Reply)
  openingSource : Returns (Directories.openAt parent.uid stage.directory.fd "export".toUTF8) opening opened
  earlier : List (Request × Reply)
  prior : match opened with
    | .error _ => earlier = []
    | .ok root => Returns (Publication.cleanupExport parent.uid root input) earlier ()
  files : List (Request × Reply)
  completed : Returns (Publication.cleanupStageFiles stage Publication.cleanupNames) files ()
  exportReply : Reply
  closeReply : Reply
  trace : before = Publication.completed (opening ++ earlier ++ files ++ [
    ({op := .unlinkAt, first := stage.directory.fd, second := 512, left := "export".toUTF8}, exportReply),
    ({op := .close, first := stage.directory.fd}, closeReply)])
  operation : FinalStageRemoval stage request

-- §FS-host-boundary.ownership: Every actual precommit cleanup removal is
-- inside this retained stage family, or is the single final parent-relative
-- root removal. This classification follows the real loops and open replies.
theorem cleanup_parent_or_final_source {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (descriptors : DescriptorContract kernel)
    (actor : ActorId) (origin : OperationOrigin) (limit : Nat) {family : Family}
    (opens : PrivateDirectoryOpens kernel (fun index request reply before after =>
      origin index Reply (.filesystem request) reply before after ∧ index < limit) family)
    {parent : Directories.Parent} {stage : Directories.Fresh} {input : Publication.Input}
    {before : List (Request × Option Reply)} {request : Request}
    (source : Publication.CleanupFrontier parent stage input before request none)
    {raw : List Program.Event} (chunks : PrimitiveFilesystem.Chunks (before.map Program.filesystemPrefixEvent) raw)
    {ordinal : Nat} {first after : World}
    (history : ActorHistoryWith runtime actor origin ordinal first raw after)
    (bounded : ordinal + raw.length ≤ limit) {rootHandle : Handle} {scope : ObjectId}
    (live : first.handles stage.directory.fd = some rootHandle) (privateRoot : family rootHandle.object = some scope)
    (distinct : stage.directory.fd ≠ stage.container.fd)
    (held : request.first ≠ stage.container.fd → after.handles stage.directory.fd = some rootHandle) :
    (∃ handle, after.handles request.first = some handle ∧ family handle.object = some scope) ∨
      Nonempty (FinalCleanupFrontier parent stage input before request) := by
  cases source with
  | exports root opening opened inside source trace =>
    have rawShape : before.map Program.filesystemPrefixEvent =
        opening.map Program.filesystemEvent ++ inside.map Program.filesystemPrefixEvent := by
      exact (congrArg (List.map Program.filesystemPrefixEvent) trace).trans
        (by rw [List.map_append, completed_filesystem_events])
    rw [rawShape] at chunks
    obtain ⟨openingRaw, insideRaw, openingChunks, insideChunks, rawTrace⟩ := PrimitiveFilesystem.chunks_split _ _ chunks
    obtain ⟨middle, openingHistory, insideHistory⟩ := actor_with_split openingRaw insideRaw (rawTrace ▸ history)
    obtain ⟨openingEvents, openingSource, openingTrace⟩ := PrimitiveFilesystem.chunks_filesystem_returns opened openingChunks
    have openingBound : ordinal + openingEvents.length ≤ limit := by
      have length := congrArg List.length openingTrace
      simp only [List.length_map] at length
      rw [rawTrace, List.length_append] at bounded
      omega
    have boundedHistory := recorded_history_source_bound (actor_recorded_filesystem (openingTrace ▸ openingHistory)) limit openingBound
    obtain ⟨observation, privateObject⟩ := directory_open_private descriptors opens ordinal parent.uid stage.directory.fd
      "export".toUTF8 rootHandle scope ⟨openingSource, boundedHistory⟩ live privateRoot
      (by
        change Directories.component (ByteArray.mk #[101, 120, 112, 111, 114, 116]) = true
        simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem])
      (by decide) (by decide)
    exact .inl (cleanup_export_parent descriptors actor origin limit opens source insideChunks insideHistory
      (by rw [rawTrace, List.length_append] at bounded; omega) observation.live privateObject)
  | footer opened opening openingSource earlier prior inside source trace =>
    cases source with
    | root files completed exportReply closeReply footerTrace operation =>
      exact .inr ⟨⟨opened, opening, openingSource, earlier, prior, files, completed, exportReply, closeReply,
        trace.trans (by rw [footerTrace]; simp only [Publication.completed, List.map_append, List.append_assoc]), operation⟩⟩
    | files source =>
      have operand : request.first = stage.directory.fd := congrArg Request.first source.operation
      exact .inl ⟨rootHandle, operand ▸ held (operand ▸ distinct), privateRoot⟩
    | «export» files completed trace operation =>
      have operand : request.first = stage.directory.fd := congrArg Request.first operation
      exact .inl ⟨rootHandle, operand ▸ held (operand ▸ distinct), privateRoot⟩

-- §AR-host-boundary.interfaces: Preserve the current-parent projection;
-- the stronger sibling also retains the exact final source prefix.
theorem cleanup_parent_or_final {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (descriptors : DescriptorContract kernel)
    (actor : ActorId) (origin : OperationOrigin) (limit : Nat) {family : Family}
    (opens : PrivateDirectoryOpens kernel (fun index request reply before after =>
      origin index Reply (.filesystem request) reply before after ∧ index < limit) family)
    {parent : Directories.Parent} {stage : Directories.Fresh} {input : Publication.Input}
    {before : List (Request × Option Reply)} {request : Request}
    (source : Publication.CleanupFrontier parent stage input before request none)
    {raw : List Program.Event} (chunks : PrimitiveFilesystem.Chunks (before.map Program.filesystemPrefixEvent) raw)
    {ordinal : Nat} {first after : World}
    (history : ActorHistoryWith runtime actor origin ordinal first raw after)
    (bounded : ordinal + raw.length ≤ limit) {rootHandle : Handle} {scope : ObjectId}
    (live : first.handles stage.directory.fd = some rootHandle) (privateRoot : family rootHandle.object = some scope)
    (distinct : stage.directory.fd ≠ stage.container.fd)
    (held : request.first ≠ stage.container.fd → after.handles stage.directory.fd = some rootHandle) :
    (∃ handle, after.handles request.first = some handle ∧ family handle.object = some scope) ∨
      FinalStageRemoval stage request := by
  rcases cleanup_parent_or_final_source descriptors actor origin limit opens source chunks history bounded live privateRoot
      distinct held with privateParent | finalSource
  · exact .inl privateParent
  · obtain ⟨finalSource⟩ := finalSource
    exact .inr finalSource.operation

end LeanCage.Host.Kernel.Lowered
