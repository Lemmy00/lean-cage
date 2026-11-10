import FilesystemCleanupAuthority

namespace LeanCage.Host.Kernel
open Filesystem

private theorem selected_split {α : Type} {events : List α} {offset : Nat} {event : α}
    (selected : events[offset]? = some event) :
    ∃ first last, events = first ++ event :: last ∧ first.length = offset := by
  induction events generalizing offset with
  | nil => cases selected
  | cons head tail ih =>
    cases offset with
    | zero => cases selected; exact ⟨[], tail, rfl, rfl⟩
    | succ offset =>
      obtain ⟨first, last, trace, count⟩ := ih selected
      exact ⟨head :: first, last, by rw [trace]; rfl, by simp only [List.length_cons, count]⟩

private theorem returned_pending {α : Type} {program : Filesystem.Program α}
    {events first last : List (Request × Reply)} {request : Request} {reply : Reply} {value : α}
    (source : Returns program events value) (trace : events = first ++ (request, reply) :: last) :
    Prefix program (Publication.completed first ++ [(request, none)]) := by
  subst events
  induction first generalizing program with
  | nil => cases source with | call _ _ _ _ _ rest => exact .lost _ _
  | cons event first ih => cases source with | call _ _ _ _ _ rest => exact .returned _ _ _ _ (ih rest)

private theorem recorded_as_actor {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId} {origin : OperationOrigin}
    {ordinal : Nat} {before after : World} {events : List (Request × Reply)}
    (history : RecordedHistory kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
      ordinal before events after) :
    ActorHistoryWith runtime actor origin ordinal before (events.map Program.filesystemEvent) after := by
  induction history with
  | nil => exact .nil _ _
  | environment actual tail ih => exact .environment actual ih
  | cons actual sampled tail ih => exact .returned actual sampled ih

structure CapturedPrivateUnlink {kernel : Contract} {origin : OperationOrigin} (family : Family)
    (scope ordinal : Nat) (request : Request) (reply : Reply) where
  before : World
  after : World
  actual : kernel.step before request (some reply) after
  sampled : origin ordinal Reply (.filesystem request) reply before after
  parent : Handle
  live : before.handles request.first = some parent
  privateParent : family parent.object = some scope
  component : Directories.component request.left = true

-- §FS-host-boundary.ownership: Every selected raw export cleanup removal
-- is interpreted from that actual completed helper and its fixed history.
-- Equal requests at other source ordinals cannot supply its parent.
theorem actual_export_cleanup_capture {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (descriptors : DescriptorContract kernel)
    (actor : ActorId) (origin : OperationOrigin) (limit : Nat) {family : Family}
    (opens : PrivateDirectoryOpens kernel (fun index request reply before after =>
      origin index Reply (.filesystem request) reply before after ∧ index < limit) family)
    {uid : Nat} {root : Directories.Opened} {input : Publication.Input}
    {ordinal : Nat} {before after : World} {events : List (Request × Reply)}
    (run : RecordedRun kernel (fun index request reply => origin index Reply (.filesystem request) reply)
      ordinal (Publication.cleanupExport uid root input).lower before events after ())
    (bounded : ordinal + events.length ≤ limit) {rootHandle : Handle} {scope : ObjectId}
    (live : before.handles root.fd = some rootHandle) (privateRoot : family rootHandle.object = some scope)
    {offset : Nat} {request : Request} {reply : Reply} (selected : events[offset]? = some (request, reply))
    (unlink : request.op = .unlinkAt) :
    Nonempty (CapturedPrivateUnlink (kernel := kernel) (origin := origin) family scope (ordinal + offset) request reply) := by
  obtain ⟨first, last, trace, count⟩ := selected_split selected
  obtain ⟨between, prefixHistory, suffixHistory⟩ := recorded_history_split first _ (trace ▸ run.2)
  obtain ⟨atCall, afterCall, leading, actual, sampled, following⟩ := recorded_history_head suffixHistory
  have prefixHistory : RecordedHistory kernel (fun index request reply => origin index Reply (.filesystem request) reply)
      ordinal before first atCall := by
    simpa only [List.append_nil] using recorded_history_append prefixHistory leading
  have rawSource := Program.lift_filesystem_prefix (returned_pending run.1 trace)
  have rawSource : Program.Prefix (PrimitiveFilesystem.lower (Program.liftFilesystem (Publication.cleanupExport uid root input)))
      (first.map Program.filesystemEvent ++ [Program.filesystemPrefixEvent (request, none)]) := by
    simpa only [PrimitiveFilesystem.lower_lift_filesystem, List.map_append, List.map_singleton,
      completed_filesystem_events] using rawSource
  obtain ⟨occurrence⟩ := PrimitiveFilesystem.lowered_filesystem_source _ rawSource
  have primary : request = occurrence.primary := PrimitiveFilesystem.filesystem_occurrence_primary occurrence
    (by rw [unlink]; decide) (by rw [unlink]; decide) (by rw [unlink]; decide)
  have logical := PrimitiveFilesystem.filesystem_occurrence_logical occurrence
  rw [← primary] at logical
  have logical : Program.Prefix (Program.liftFilesystem (Publication.cleanupExport uid root input))
      (occurrence.logicalBefore ++ [Program.filesystemPrefixEvent (request, none)]) := logical
  obtain ⟨logicalBefore, logicalSource, logicalTrace⟩ := selected_filesystem_source logical
  obtain ⟨frontier⟩ := Publication.cleanup_export_frontier uid root input logicalSource unlink
  have chunks : PrimitiveFilesystem.Chunks (logicalBefore.map Program.filesystemPrefixEvent) occurrence.rawBefore := by
    exact Eq.mp (congrArg (fun logical => PrimitiveFilesystem.Chunks logical occurrence.rawBefore) logicalTrace)
      (PrimitiveFilesystem.reached_chunks occurrence.reached)
  have rawHistory : ActorHistoryWith runtime actor origin ordinal before
      (occurrence.rawBefore ++ occurrence.inside.map Program.filesystemPrefixEvent) atCall := by
    exact Eq.mp (congrArg (fun raw => ActorHistoryWith runtime actor origin ordinal before raw atCall)
      occurrence.trace) (recorded_as_actor prefixHistory)
  obtain ⟨atGuards, bodyHistory, guardsHistory⟩ := actor_with_split occurrence.rawBefore _ rawHistory
  have bodyBound : ordinal + occurrence.rawBefore.length ≤ limit := by
    have rawCount := congrArg List.length occurrence.trace
    have wholeCount := congrArg List.length trace
    simp only [List.length_map, List.length_append, List.length_cons] at rawCount wholeCount
    omega
  obtain ⟨parent, reference, scope⟩ := Lowered.cleanup_export_parent descriptors actor origin limit opens frontier
    chunks bodyHistory bodyBound live privateRoot
  have guardsFrame := actor_retaining_event_handles descriptors guardsHistory (by
    have probes := guarded_namespace_last occurrence.adapter (.inr (.inr (.inl unlink)))
    obtain ⟨checks, checked, same, inside⟩ := probes
    intro event member
    rw [inside, List.map_map] at member
    obtain ⟨⟨query, answer⟩, occurs, rfl⟩ := List.mem_map.mp member
    have role := checked_parents_probes checked (query, answer) occurs
    change RetainsDescriptors query.op
    rcases role with magic | flags
    · rw [magic]; simp [RetainsDescriptors]
    · rw [flags]; simp [RetainsDescriptors])
  refine ⟨⟨atCall, afterCall, actual, ?_, parent, ?_, scope, Lowered.cleanup_export_component frontier⟩⟩
  · simpa only [count] using sampled
  · rw [guardsFrame]
    exact reference

end LeanCage.Host.Kernel
