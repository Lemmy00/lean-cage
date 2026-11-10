import FilesystemCleanupTraversal
import FilesystemCleanupBeforeRoot

namespace LeanCage.Host.Kernel
open Filesystem

def ObservedDirectory.mapOrigin {kernel : Contract} {origin target : FilesystemOrigin} {limit : Nat}
    {world : World} {uid : Nat} {directory : Directories.Opened}
    (source : ObservedDirectory kernel origin limit world uid directory)
    (maps : ∀ ordinal request reply before after, origin ordinal request reply before after →
      target ordinal request reply before after) : ObservedDirectory kernel target limit world uid directory := {
  source with sample := {source.sample with sampled := maps _ _ _ _ _ source.sample.sampled} }

structure ObservedUnlinkParent (kernel : Contract) (origin : FilesystemOrigin) (limit : Nat)
    (world : World) (uid : Nat) (request : Request) (family : Family) (scope : ObjectId) where
  directory : Directories.Opened
  operand : directory.fd = request.first
  observation : ObservedDirectory kernel origin limit world uid directory
  privateParent : family observation.handle.object = some scope
  component : Directories.component request.left = true

namespace Lowered

-- §FS-host-boundary.lookup: A nested cleanup parent keeps the actual fstat
-- sample that checked it, as well as its same-OFD reference and scope. A
-- private label does not replace the source's metadata observation.
theorem cleanup_chain_observed {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (descriptors : DescriptorContract kernel)
    (actor : ActorId) (origin : OperationOrigin) (limit : Nat) {family : Family}
    (opens : PrivateDirectoryOpens kernel (fun index request reply before after =>
      origin index Reply (.filesystem request) reply before after ∧ index < limit) family)
    {uid : Nat} {root leaf : UInt64} {names : List String} {logical : List (Request × Reply)}
    (source : Publication.DirectoryChain uid false root names logical leaf)
    {raw : List Program.Event} (chunks : PrimitiveFilesystem.Chunks (logical.map Program.filesystemEvent) raw)
    {ordinal : Nat} {before after : World}
    (history : ActorHistoryWith runtime actor origin ordinal before raw after)
    (bounded : ordinal + raw.length ≤ limit) {information : Stat}
    (starting : ObservedDirectory kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
      ordinal before uid {fd := root, information}) {scope : ObjectId}
    (privateRoot : family starting.handle.object = some scope) :
    ∃ directory : Directories.Opened, directory.fd = leaf ∧
      ∃ observation : ObservedDirectory kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
        (ordinal + raw.length) after uid directory, family observation.handle.object = some scope := by
  induction source generalizing raw ordinal before information with
  | root parent =>
    cases chunks
    have live : after.handles parent = some starting.handle := by
      rw [actor_retaining_event_handles descriptors history (by intro event impossible; cases impossible)]
      exact starting.live
    exact ⟨{fd := parent, information}, rfl, starting.advance live (by simp), privateRoot⟩
  | @child parent name names opened opening following last component actual below ih =>
    rw [List.map_append] at chunks
    obtain ⟨first, final, openingChunks, followingChunks, trace⟩ := PrimitiveFilesystem.chunks_split _ _ chunks
    obtain ⟨middle, initialHistory, lastHistory⟩ := actor_with_split first final (trace ▸ history)
    obtain ⟨events, openingSource, openingTrace⟩ := PrimitiveFilesystem.chunks_filesystem_returns actual openingChunks
    have openingHistory := actor_recorded_filesystem (openingTrace ▸ initialHistory)
    have openingBound : ordinal + events.length ≤ limit := by
      have length := congrArg List.length trace
      have openingLength := congrArg List.length openingTrace
      simp only [List.length_append, List.length_map] at length openingLength
      omega
    have boundedHistory := recorded_history_source_bound openingHistory limit openingBound
    have operands : Directories.component name.toUTF8 = true ∧ name.toUTF8 ≠ ".".toUTF8 ∧ name.toUTF8 ≠ "..".toUTF8 :=
      ⟨SourceReadForms.valid_component_form name component,
        fun same => component.2.2.1 (String.toByteArray_inj.mp same),
        fun same => component.2.2.2.1 (String.toByteArray_inj.mp same)⟩
    simp only [Publication.childOpening, Bool.false_eq_true, ↓reduceIte] at openingSource
    obtain ⟨observed, privateChild⟩ := directory_open_private descriptors opens ordinal uid parent name.toUTF8
      starting.handle scope ⟨openingSource, boundedHistory⟩ starting.live privateRoot operands.1 operands.2.1 operands.2.2
    let checked := observed.mapOrigin (fun _ _ _ _ _ evidence => evidence.1)
    let atChild : ObservedDirectory kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
        (ordinal + first.length) middle uid opened := checked.advance checked.live (by
      have length := congrArg List.length openingTrace
      simp only [List.length_map] at length
      omega)
    obtain ⟨directory, same, observation, privateParent⟩ :=
      ih followingChunks lastHistory (by rw [trace, List.length_append] at bounded; omega) atChild privateChild
    exact ⟨directory, same, observation.advance observation.live (by rw [trace, List.length_append]; omega), privateParent⟩

theorem relative_cleanup_observed {kernel : Contract} {sourceProgram : Program UInt32}
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
    (bounded : ordinal + raw.length ≤ limit) {information : Stat}
    (starting : ObservedDirectory kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
      ordinal first uid {fd := root, information}) {scope : ObjectId}
    (privateRoot : family starting.handle.object = some scope) :
    Nonempty (ObservedUnlinkParent kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
      (ordinal + raw.length) after uid request family scope) := by
  have trace : before.map Program.filesystemPrefixEvent =
      source.completed.map Program.filesystemEvent ++ source.inside.map Program.filesystemPrefixEvent := by
    exact (congrArg (List.map Program.filesystemPrefixEvent) source.trace).trans
      (by rw [List.map_append, completed_filesystem_events])
  rw [trace] at chunks
  obtain ⟨loopRaw, openingRaw, loopChunks, openingChunks, rawTrace⟩ := PrimitiveFilesystem.chunks_split _ _ chunks
  obtain ⟨middle, loopHistory, openingHistory⟩ := actor_with_split loopRaw openingRaw (rawTrace ▸ history)
  obtain ⟨loopEvents, loopSource, loopTrace⟩ := PrimitiveFilesystem.chunks_filesystem_returns source.prepared loopChunks
  have borrowed : BorrowPost kernel root starting.handle (fun _ => True)
      (forIn source.earlier () (fun item _ => do
        Publication.unlinkRelative uid root (path item).components directory
        pure (ForInStep.yield ()))).lower := by
    apply borrow_forIn
    intro item state
    apply borrow_bind (publication_unlink_relative_borrow descriptors root starting.handle _ _ _ _)
    intro ignored _
    exact .pure True.intro
  have kept := (history_borrow _ _ borrowed ⟨loopSource, actor_recorded_filesystem (loopTrace ▸ loopHistory)⟩ starting.live).1
  let updated := starting.advance kept (show ordinal ≤ ordinal + loopRaw.length by omega)
  have insideEmpty := Publication.relative_unlink_inside_empty source.active
  have insideTrace : source.inside = Publication.completed source.active.opening := by
    simpa only [insideEmpty, List.append_nil] using source.active.trace
  have actualChunks : PrimitiveFilesystem.Chunks (source.active.opening.map Program.filesystemEvent) openingRaw := by
    simpa only [insideTrace, completed_filesystem_events] using openingChunks
  obtain ⟨opened, same, observation, privateParent⟩ := cleanup_chain_observed descriptors actor origin limit opens source.active.chain
    actualChunks openingHistory (by rw [rawTrace, List.length_append] at bounded; omega) updated privateRoot
  have operand : opened.fd = request.first := same.trans (congrArg Request.first source.active.operation).symm
  refine ⟨⟨opened, operand, observation.advance observation.live ?_, privateParent, ?_⟩⟩
  · rw [rawTrace, List.length_append]
    omega
  · exact Publication.relative_unlink_component source.active (path source.item).valid.2.2.2

theorem cleanup_export_observed {kernel : Contract} {sourceProgram : Program UInt32}
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
    (bounded : ordinal + raw.length ≤ limit)
    (starting : ObservedDirectory kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
      ordinal first uid root) {scope : ObjectId}
    (privateRoot : family starting.handle.object = some scope) :
    Nonempty (ObservedUnlinkParent kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
      (ordinal + raw.length) after uid request family scope) := by
  cases source with
  | files source => exact relative_cleanup_observed descriptors actor origin limit opens source chunks history bounded starting privateRoot
  | directories files completed inside source trace =>
    have rawShape : before.map Program.filesystemPrefixEvent =
        files.map Program.filesystemEvent ++ inside.map Program.filesystemPrefixEvent := by
      exact (congrArg (List.map Program.filesystemPrefixEvent) trace).trans
        (by rw [List.map_append, completed_filesystem_events])
    rw [rawShape] at chunks
    obtain ⟨filesRaw, insideRaw, filesChunks, insideChunks, rawTrace⟩ := PrimitiveFilesystem.chunks_split _ _ chunks
    obtain ⟨middle, filesHistory, insideHistory⟩ := actor_with_split filesRaw insideRaw (rawTrace ▸ history)
    obtain ⟨filesEvents, filesSource, filesTrace⟩ := PrimitiveFilesystem.chunks_filesystem_returns completed filesChunks
    have kept := (history_borrow _ _ (cleanup_files_borrow descriptors root.fd starting.handle uid root.fd input.outcome.files)
      ⟨filesSource, actor_recorded_filesystem (filesTrace ▸ filesHistory)⟩ starting.live).1
    let updated := starting.advance kept (show ordinal ≤ ordinal + filesRaw.length by omega)
    obtain ⟨result⟩ := relative_cleanup_observed descriptors actor origin limit opens source insideChunks insideHistory
      (by rw [rawTrace, List.length_append] at bounded; omega) updated privateRoot
    exact ⟨{result with observation := result.observation.advance result.observation.live (by rw [rawTrace, List.length_append]; omega)}⟩

theorem cleanup_observed_or_final {kernel : Contract} {sourceProgram : Program UInt32}
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
    (bounded : ordinal + raw.length ≤ limit)
    (starting : ObservedDirectory kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
      ordinal first parent.uid stage.directory) {scope : ObjectId}
    (privateRoot : family starting.handle.object = some scope) (distinct : stage.directory.fd ≠ stage.container.fd)
    (held : request.first ≠ stage.container.fd → after.handles stage.directory.fd = some starting.handle) :
    Nonempty (ObservedUnlinkParent kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
      (ordinal + raw.length) after parent.uid request family scope) ∨
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
    obtain ⟨observed, privateObject⟩ := directory_open_private descriptors opens ordinal parent.uid stage.directory.fd
      "export".toUTF8 starting.handle scope ⟨openingSource, boundedHistory⟩ starting.live privateRoot
      (by
        change Directories.component (ByteArray.mk #[101, 120, 112, 111, 114, 116]) = true
        simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem])
      (by decide) (by decide)
    let checked := observed.mapOrigin (fun _ _ _ _ _ evidence => evidence.1)
    let updated : ObservedDirectory kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
        (ordinal + openingRaw.length) middle parent.uid root := checked.advance checked.live (by
      have length := congrArg List.length openingTrace
      simp only [List.length_map] at length
      omega)
    obtain ⟨result⟩ := cleanup_export_observed descriptors actor origin limit opens source insideChunks insideHistory
      (by rw [rawTrace, List.length_append] at bounded; omega) updated privateObject
    exact .inl ⟨{result with
      observation := result.observation.advance result.observation.live (by rw [rawTrace, List.length_append]; omega)}⟩
  | footer opened opening openingSource earlier prior inside source trace =>
    cases source with
    | root files completed exportReply closeReply footerTrace operation =>
      exact .inr ⟨⟨opened, opening, openingSource, earlier, prior, files, completed, exportReply, closeReply,
        trace.trans (by rw [footerTrace]; simp only [Publication.completed, List.map_append, List.append_assoc]), operation⟩⟩
    | files source =>
      have operand : request.first = stage.directory.fd := congrArg Request.first source.operation
      have member : source.loop.item ∈ Publication.cleanupNames :=
        Eq.mpr (congrArg (fun members : List String => source.loop.item ∈ members) source.loop.sequence) (by simp)
      refine .inl ⟨⟨stage.directory, operand.symm, starting.advance (held (operand ▸ distinct)) (by omega), privateRoot, ?_⟩⟩
      have name : request.left = source.loop.item.toUTF8 := congrArg Request.left source.operation
      rw [name]
      exact static_cleanup_components _ member
    | «export» files completed trace operation =>
      have operand : request.first = stage.directory.fd := congrArg Request.first operation
      refine .inl ⟨⟨stage.directory, operand.symm, starting.advance (held (operand ▸ distinct)) (by omega), privateRoot, ?_⟩⟩
      have name : request.left = "export".toUTF8 := congrArg Request.left operation
      rw [name]
      change Directories.component (ByteArray.mk #[101, 120, 112, 111, 114, 116]) = true
      simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem]

end Lowered
end LeanCage.Host.Kernel
