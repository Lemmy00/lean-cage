import FilesystemLoweredPathGuards
import FilesystemPrimitiveChunks
import FilesystemPrimitiveFrames

namespace LeanCage.Host.PrimitiveFilesystem

-- §AR-host-boundary.interfaces: The same completed source bytes and raw chunks execute the
-- actual lowered filesystem helper; this is not an independent helper transcript.
theorem chunks_filesystem_returns {α : Type} {program : Filesystem.Program α}
    {logical : List (Filesystem.Request × Filesystem.Reply)} {raw : List Program.Event} {value : α}
    (source : Filesystem.Returns program logical value)
    (chunks : Chunks (logical.map Program.filesystemEvent) raw) :
    ∃ events, Filesystem.Returns program.lower events value ∧ raw = events.map Program.filesystemEvent := by
  have actual := chunks_returns (Program.lift_filesystem_returns source) chunks
  rw [lower_lift_filesystem] at actual
  exact Program.lift_filesystem_source program.lower actual

-- §AR-host-boundary.interfaces: Keep the exact raw-to-source relation for completed
-- filesystem helpers as well as for selected-call prefixes.
theorem lowered_filesystem_returns_chunks {α : Type} (program : Filesystem.Program α)
    {raw : List (Filesystem.Request × Filesystem.Reply)} {value : α}
    (run : Filesystem.Returns program.lower raw value) :
    ∃ logical, Filesystem.Returns program logical value ∧
      Chunks (logical.map Program.filesystemEvent) (raw.map Program.filesystemEvent) := by
  have actual := Program.lift_filesystem_returns run
  rw [← lower_lift_filesystem] at actual
  obtain ⟨logical, source, chunks⟩ := lowered_returns_chunks (Program.liftFilesystem program) actual
  obtain ⟨events, source, shape⟩ := Program.lift_filesystem_source program source
  exact ⟨events, source, shape ▸ chunks⟩

end LeanCage.Host.PrimitiveFilesystem

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

variable {sourceProgram : Program UInt32}

theorem open_phase_guard {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : DescriptorContract kernel) (actor : ActorId) (origin : OperationOrigin) (ordinal : Nat)
    (path : ByteArray) (directory : Bool)
    {logical : List (Request × Reply)} {raw : List Program.Event} {before after : World} {fd : UInt64}
    (source : Returns (SourcePaths.open path directory) logical (.ok fd))
    (chunks : PrimitiveFilesystem.Chunks (logical.map Program.filesystemEvent) raw)
    (history : ActorHistoryWith runtime actor origin ordinal before raw after) :
    Nonempty (GuardedHandle kernel (fun index request reply => origin index Reply (.filesystem request) reply)
      (ordinal + raw.length) after fd) := by
  obtain ⟨events, actual, trace⟩ := PrimitiveFilesystem.chunks_filesystem_returns source chunks
  have recorded := actor_recorded_filesystem (trace ▸ history)
  simpa only [trace, List.length_map] using source_path_guard_recorded laws _ ordinal path directory ⟨actual, recorded⟩

theorem open_at_phase_guard {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : DescriptorContract kernel) (actor : ActorId) (origin : OperationOrigin) (ordinal : Nat)
    (parent : UInt64) (name : ByteArray) (directory : Bool)
    {logical : List (Request × Reply)} {raw : List Program.Event} {before after : World} {fd : UInt64}
    (source : Returns (SourcePaths.openAt parent name directory) logical (.ok fd))
    (chunks : PrimitiveFilesystem.Chunks (logical.map Program.filesystemEvent) raw)
    (history : ActorHistoryWith runtime actor origin ordinal before raw after) :
    Nonempty (GuardedHandle kernel (fun index request reply => origin index Reply (.filesystem request) reply)
      (ordinal + raw.length) after fd) := by
  obtain ⟨events, actual, trace⟩ := PrimitiveFilesystem.chunks_filesystem_returns source chunks
  have recorded := actor_recorded_filesystem (trace ▸ history)
  simpa only [trace, List.length_map] using source_open_guard_recorded laws _ ordinal parent name directory ⟨actual, recorded⟩

-- §FS-host-boundary.snapshot: Both top-level and enumerated-child copies retain their own
-- accepted privacy check, with its genuine raw ordinal in the global source journal.
theorem guarded_start_recorded {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : DescriptorContract kernel) (actor : ActorId) (origin : OperationOrigin) (ordinal : Nat)
    {fd : UInt64} (start : GuardedCopyStart fd) {raw : List Program.Event} {before after : World}
    (chunks : PrimitiveFilesystem.Chunks (start.events.map Program.filesystemEvent) raw)
    (history : ActorHistoryWith runtime actor origin ordinal before raw after) :
    Nonempty (GuardedHandle kernel (fun index request reply => origin index Reply (.filesystem request) reply)
      (ordinal + raw.length) after fd) := by
  cases start with
  | path path fd opening opened => exact open_phase_guard laws actor origin ordinal path false opened chunks history
  | child parent name fd opening opened reply information parsed regular linked =>
    change PrimitiveFilesystem.Chunks
      ((opening ++ [(({op := .stat, first := fd} : Request), reply)]).map Program.filesystemEvent) raw at chunks
    rw [List.map_append] at chunks
    obtain ⟨first, last, initial, final, trace⟩ := PrimitiveFilesystem.chunks_split _ _ chunks
    obtain ⟨middle, leading, remaining⟩ := actor_with_split first last (trace ▸ history)
    obtain ⟨guarded⟩ := open_at_phase_guard laws actor origin ordinal parent name false opened initial leading
    have single : last = [.returned (.filesystem {op := .stat, first := fd}) reply] :=
      PrimitiveFilesystem.chunks_identity final (by
        intro event member
        have same := List.mem_singleton.mp member
        subst event
        exact PrimitiveFilesystem.stat_identity fd)
    have arranged := remaining
    rw [single] at arranged
    obtain ⟨actual, queried, environment, operation, recorded, tail⟩ := actor_with_head arranged
    have actualLive : actual.handles fd = some guarded.handle := by
      rw [actor_retaining_event_handles laws environment (by intro event member; cases member)]
      exact guarded.live
    have finalLive : after.handles fd = some guarded.handle := by
      rw [actor_retaining_event_handles laws tail (by intro event member; cases member),
        laws.retained _ _ _ _ operation (by simp [RetainsDescriptors])]
      exact actualLive
    refine ⟨⟨guarded.handle, finalLive, guarded.guard, ?_⟩⟩
    have earlier := guarded.earlier
    rw [trace, List.length_append]
    omega

end LeanCage.Host.Kernel.Lowered
