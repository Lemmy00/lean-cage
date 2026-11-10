import FilesystemPrivateTraversal
import FilesystemLoweredPhases
import FilesystemSnapshotReadForms

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

private theorem component_operands {name : String} (valid : Snapshot.ValidComponent name) :
    Directories.component name.toUTF8 = true ∧ name.toUTF8 ≠ ".".toUTF8 ∧ name.toUTF8 ≠ "..".toUTF8 := by
  exact ⟨SourceReadForms.valid_component_form name valid,
    fun same => valid.2.2.1 (String.toByteArray_inj.mp same),
    fun same => valid.2.2.2.1 (String.toByteArray_inj.mp same)⟩

-- §FS-host-boundary.ownership: Execute the exact completed nested-opening chain
-- with its expanded probe chunks and global source origins. Its leaf descriptor
-- belongs to the retained root's current scope, without a traversal-frame input.
theorem publication_chain_private {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (descriptors : DescriptorContract kernel)
    (actor : ActorId) (origin : OperationOrigin) (limit : Nat) {family : Family}
    (opens : PrivateDirectoryOpens kernel
      (fun index request reply before after =>
        origin index Reply (.filesystem request) reply before after ∧ index < limit) family)
    {uid : Nat} {create : Bool} {root leaf : UInt64} {names : List String}
    {logical : List (Request × Reply)} (source : Publication.DirectoryChain uid create root names logical leaf)
    {raw : List Program.Event} (chunks : PrimitiveFilesystem.Chunks (logical.map Program.filesystemEvent) raw)
    {ordinal : Nat} {before after : World}
    (history : ActorHistoryWith runtime actor origin ordinal before raw after)
    (bounded : ordinal + raw.length ≤ limit)
    {rootHandle : Handle} {scope : ObjectId} (rootLive : before.handles root = some rootHandle)
    (rootScope : family rootHandle.object = some scope) :
    ∃ handle, after.handles leaf = some handle ∧ family handle.object = some scope := by
  induction source generalizing raw ordinal before rootHandle with
  | root parent =>
    cases chunks
    exact ⟨rootHandle, by
      rw [actor_retaining_event_handles descriptors history (by intro event member; cases member)]
      exact rootLive, rootScope⟩
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
    have observed : ∃ observation : ObservedDirectory kernel
        (fun index request reply before after =>
          origin index Reply (.filesystem request) reply before after ∧ index < limit)
        (ordinal + events.length) middle uid opened, family observation.handle.object = some scope := by
      obtain ⟨checked, notDot, notUp⟩ := component_operands component
      cases create <;> simp only [Publication.childOpening, Bool.false_eq_true, ↓reduceIte] at openingSource
      · exact directory_open_private descriptors opens ordinal uid parent name.toUTF8 rootHandle scope
          ⟨openingSource, boundedHistory⟩ rootLive rootScope checked notDot notUp
      · exact directory_ensure_private descriptors opens ordinal uid parent name.toUTF8 rootHandle scope
          ⟨openingSource, boundedHistory⟩ rootLive rootScope checked notDot notUp
    obtain ⟨openedDirectory, privateObject⟩ := observed
    exact ih followingChunks lastHistory (by rw [trace, List.length_append] at bounded; omega)
      openedDirectory.live privateObject

end LeanCage.Host.Kernel.Lowered
