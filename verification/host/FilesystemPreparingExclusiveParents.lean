import PublicationProofs.ExclusiveFrontier
import FilesystemPreparingParents

namespace LeanCage.Host.Kernel
open Filesystem

structure ObservedExclusiveParent (kernel : Contract) (origin : FilesystemOrigin) (limit : Nat)
    (world : World) (uid : Nat) (request : Request) (family : Family) (scope : ObjectId) where
  parent : ObservedCreationParent kernel origin limit world uid request family scope
  fits : SourceReadForms.DescriptorFits request.first

namespace Lowered

-- §FS-host-boundary.ownership: A pending exported file has the SAME
-- checked parent from its real completed child chain. The actual source
-- descriptor fits the ABI and cannot be interpreted as the cwd sentinel.
theorem relative_exclusive_observed {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (descriptors : DescriptorContract kernel)
    (actor : ActorId) (origin : OperationOrigin) (limit : Nat) {family : Family}
    (opens : PrivateDirectoryOpens kernel (fun index query reply before after =>
      origin index Reply (.filesystem query) reply before after ∧ index < limit) family)
    {uid : Nat} {root : UInt64} {file : Artifacts.ValidatedFile}
    {before : List (Request × Option Reply)} {request : Request}
    (source : Publication.RelativeExclusiveFrontier uid root file before request)
    {raw : List Program.Event} (chunks : PrimitiveFilesystem.Chunks (before.map Program.filesystemPrefixEvent) raw)
    {ordinal : Nat} {first after : World}
    (history : ActorHistoryWith runtime actor origin ordinal first raw after)
    (bounded : ordinal + raw.length ≤ limit) {information : Stat}
    (starting : ObservedDirectory kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
      ordinal first uid {fd := root, information}) {scope : ObjectId}
    (privateRoot : family starting.handle.object = some scope) (fits : SourceReadForms.DescriptorFits root) :
    Nonempty (ObservedExclusiveParent kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
      (ordinal + raw.length) after uid request family scope) := by
  have logical : before.map Program.filesystemPrefixEvent = source.opening.map Program.filesystemEvent := by
    simpa only [completed_filesystem_events] using congrArg (List.map Program.filesystemPrefixEvent) source.trace
  have actualChunks : PrimitiveFilesystem.Chunks (source.opening.map Program.filesystemEvent) raw := logical ▸ chunks
  obtain ⟨directory, operand, observation, privateParent⟩ := preparing_chain_observed descriptors actor origin limit opens
    source.chain actualChunks history bounded starting privateRoot
  refine ⟨{
    parent := {
      directory
      operand := operand.trans (congrArg Request.first source.operation).symm
      observation
      privateParent
      component := ?_
      operation := .inr ⟨congrArg Request.op source.operation, congrArg Request.second source.operation⟩
      mode := fun making => by rw [congrArg Request.op source.operation] at making; cases making }
    fits := ?_ }⟩
  · rw [source.operation]
    exact SourceReadForms.valid_component_form source.name source.component
  · rw [source.operation]
    exact source.chain.leaf_fits fits

theorem relative_loop_exclusive_observed {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (descriptors : DescriptorContract kernel)
    (actor : ActorId) (origin : OperationOrigin) (limit : Nat) {family : Family}
    (opens : PrivateDirectoryOpens kernel (fun index query reply before after =>
      origin index Reply (.filesystem query) reply before after ∧ index < limit) family)
    {uid : Nat} {root : UInt64} {files : List Artifacts.ValidatedFile}
    {before : List (Request × Option Reply)} {request : Request}
    (source : Publication.RelativeLoopExclusiveFrontier uid root files before request)
    {raw : List Program.Event} (chunks : PrimitiveFilesystem.Chunks (before.map Program.filesystemPrefixEvent) raw)
    {ordinal : Nat} {first after : World}
    (history : ActorHistoryWith runtime actor origin ordinal first raw after)
    (bounded : ordinal + raw.length ≤ limit) {information : Stat}
    (starting : ObservedDirectory kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
      ordinal first uid {fd := root, information}) {scope : ObjectId}
    (privateRoot : family starting.handle.object = some scope) (fits : SourceReadForms.DescriptorFits root) :
    Nonempty (ObservedExclusiveParent kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
      (ordinal + raw.length) after uid request family scope) := by
  have logical : before.map Program.filesystemPrefixEvent =
      source.loop.completed.map Program.filesystemEvent ++ source.loop.inside.map Program.filesystemPrefixEvent := by
    simpa only [List.map_append, completed_filesystem_events] using
      congrArg (List.map Program.filesystemPrefixEvent) source.loop.trace
  rw [logical] at chunks
  obtain ⟨loopRaw, insideRaw, loopChunks, insideChunks, rawTrace⟩ := PrimitiveFilesystem.chunks_split _ _ chunks
  obtain ⟨middle, loopHistory, insideHistory⟩ := actor_with_split loopRaw insideRaw (rawTrace ▸ history)
  obtain ⟨loopEvents, loopReturned, loopTrace⟩ := PrimitiveFilesystem.chunks_filesystem_returns source.loop.prepared loopChunks
  have borrowed : BorrowPost kernel root starting.handle (fun _ => True)
      (forIn source.loop.earlier (none, ()) (Publication.actionBody (Publication.writeRelative uid root))).lower := by
    apply borrow_forIn
    intro file state
    unfold Publication.actionBody
    apply borrow_bind (publication_write_relative_borrow descriptors root starting.handle _ _ _)
    intro result _
    cases result <;> exact .pure True.intro
  have held := (history_borrow _ _ borrowed ⟨loopReturned, actor_recorded_filesystem (loopTrace ▸ loopHistory)⟩ starting.live).1
  let updated := starting.advance held (show ordinal ≤ ordinal + loopRaw.length by omega)
  obtain ⟨parent⟩ := relative_exclusive_observed descriptors actor origin limit opens source.current insideChunks insideHistory
    (by rw [rawTrace, List.length_append] at bounded; omega) updated privateRoot fits
  have later : ordinal + loopRaw.length + insideRaw.length ≤ ordinal + raw.length := by
    rw [rawTrace, List.length_append]
    omega
  exact ⟨{parent with parent := {parent.parent with
    observation := parent.parent.observation.advance parent.parent.observation.live later}}⟩

-- §FS-host-boundary.ownership: The selected new export file uses the real
-- export-open/stat, completed directory setup and its exact file-loop
-- cursor. Every actual raw operation remains in the shared history.
theorem exports_exclusive_observed {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (descriptors : DescriptorContract kernel)
    (actor : ActorId) (origin : OperationOrigin) (limit : Nat) {family : Family}
    (opens : PrivateDirectoryOpens kernel (fun index query reply before after =>
      origin index Reply (.filesystem query) reply before after ∧ index < limit) family)
    {uid : Nat} {stage : UInt64} {input : Publication.Input}
    {before : List (Request × Option Reply)} {request : Request}
    (source : Publication.ExportsExclusiveFrontier uid stage input before request)
    {raw : List Program.Event} (chunks : PrimitiveFilesystem.Chunks (before.map Program.filesystemPrefixEvent) raw)
    {ordinal : Nat} {first after : World}
    (history : ActorHistoryWith runtime actor origin ordinal first raw after)
    (bounded : ordinal + raw.length ≤ limit) {information : Stat}
    (starting : ObservedDirectory kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
      ordinal first uid {fd := stage, information}) {scope : ObjectId}
    (privateRoot : family starting.handle.object = some scope) :
    Nonempty (ObservedExclusiveParent kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
      (ordinal + raw.length) after uid request family scope) := by
  let make : Request := {op := .mkdirAt, first := stage, second := 448, left := "export".toUTF8}
  have logical : before.map Program.filesystemPrefixEvent =
      [(make, source.made)].map Program.filesystemEvent ++ (source.opening.map Program.filesystemEvent ++
        (source.making.map Program.filesystemEvent ++ source.inside.map Program.filesystemPrefixEvent)) := by
    simpa only [List.map_append, List.map_cons, List.map_nil, completed_filesystem_events,
      Program.filesystemPrefixEvent, Program.filesystemEvent, make, List.append_assoc] using
      congrArg (List.map Program.filesystemPrefixEvent) source.trace
  rw [logical] at chunks
  obtain ⟨madeRaw, remainingRaw, madeChunks, remainingChunks, firstTrace⟩ := PrimitiveFilesystem.chunks_split _ _ chunks
  obtain ⟨beforeOpen, madeHistory, remainingHistory⟩ := actor_with_split madeRaw remainingRaw (firstTrace ▸ history)
  have madeSource : Returns (Filesystem.Program.effect make) [(make, source.made)] source.made := .call _ _ _ _ _ (.pure _)
  obtain ⟨madeEvents, madeReturned, madeTrace⟩ := PrimitiveFilesystem.chunks_filesystem_returns madeSource madeChunks
  have borrowed : BorrowPost kernel stage starting.handle (fun _ => True) (Filesystem.Program.effect make).lower := by
    apply passive_call descriptors stage starting.handle (by simp [make, RetainsDescriptors])
    intro reply
    exact .pure True.intro
  have held := (history_borrow _ _ borrowed ⟨madeReturned, actor_recorded_filesystem (madeTrace ▸ madeHistory)⟩ starting.live).1
  obtain ⟨openingRaw, followingRaw, openingChunks, followingChunks, nextTrace⟩ := PrimitiveFilesystem.chunks_split _ _ remainingChunks
  obtain ⟨afterOpen, openingHistory, followingHistory⟩ := actor_with_split openingRaw followingRaw (nextTrace ▸ remainingHistory)
  obtain ⟨openingEvents, openingReturned, openingTrace⟩ := PrimitiveFilesystem.chunks_filesystem_returns source.opened openingChunks
  have openingBound : ordinal + madeRaw.length + openingEvents.length ≤ limit := by
    have count := congrArg List.length openingTrace
    simp only [List.length_map] at count
    rw [firstTrace, nextTrace, List.length_append, List.length_append] at bounded
    omega
  have boundedHistory := recorded_history_source_bound (actor_recorded_filesystem (openingTrace ▸ openingHistory)) limit openingBound
  obtain ⟨observed, privateChild⟩ := directory_open_private descriptors opens (ordinal + madeRaw.length) uid stage
    "export".toUTF8 starting.handle scope ⟨openingReturned, boundedHistory⟩ held privateRoot
    (by
      change Directories.component (ByteArray.mk #[101, 120, 112, 111, 114, 116]) = true
      simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem])
    (by decide) (by decide)
  obtain ⟨reply, informationReply, trace, recognized, parsed, trusted⟩ := Retrieval.directoryOpening_source _ _ _ source.opened
  have fits := SourceReadForms.descriptor_fits recognized
  let checked := observed.mapOrigin (fun _ _ _ _ _ evidence => evidence.1)
  let updated : ObservedDirectory kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
      (ordinal + madeRaw.length + openingRaw.length) afterOpen uid source.root := checked.advance checked.live (by
    have count := congrArg List.length openingTrace
    simp only [List.length_map] at count
    omega)
  obtain ⟨makingRaw, insideRaw, makingChunks, insideChunks, finalTrace⟩ := PrimitiveFilesystem.chunks_split _ _ followingChunks
  obtain ⟨afterMaking, makingHistory, insideHistory⟩ := actor_with_split makingRaw insideRaw (finalTrace ▸ followingHistory)
  obtain ⟨makingEvents, makingReturned, makingTrace⟩ := PrimitiveFilesystem.chunks_filesystem_returns source.madeDirectories makingChunks
  have rootHeld := (history_borrow _ _
    (publication_directories_borrow descriptors source.root.fd updated.handle _ _ _)
    ⟨makingReturned, actor_recorded_filesystem (makingTrace ▸ makingHistory)⟩ updated.live).1
  let atFiles := updated.advance rootHeld (show _ ≤ ordinal + madeRaw.length + openingRaw.length + makingRaw.length by omega)
  obtain ⟨parent⟩ := relative_loop_exclusive_observed descriptors actor origin limit opens source.current insideChunks insideHistory
    (by rw [firstTrace, nextTrace, finalTrace, List.length_append, List.length_append, List.length_append] at bounded; omega)
    atFiles privateChild fits
  have later : ordinal + madeRaw.length + openingRaw.length + makingRaw.length + insideRaw.length ≤ ordinal + raw.length := by
    rw [firstTrace, nextTrace, finalTrace, List.length_append, List.length_append, List.length_append]
    omega
  exact ⟨{parent with parent := {parent.parent with
    observation := parent.parent.observation.advance parent.parent.observation.live later}}⟩

end Lowered
end LeanCage.Host.Kernel
