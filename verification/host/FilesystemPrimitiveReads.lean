import FilesystemLoweredReads
import FilesystemReadSources.Recording

namespace LeanCage.Host.Kernel
open Filesystem

structure PrimitiveGuardedRead {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (ticks : List (ActorTick runtime)) (actor : ActorId) (position : Nat) (engine : EngineState)
    (request : Request) where
  handle : Handle
  live : engine.references request.first = some handle
  guard : PublicGuard kernel (fun ordinal request reply =>
    SourceReturnAt runtime ticks actor ordinal Reply (.filesystem request) reply) request.first handle
  guardPosition : Nat
  guardTick : ActorTick runtime
  selected : ticks[guardPosition]? = some guardTick
  action : guardTick.action = .returned actor (.filesystem {
    op := .getAttribute, first := request.first, second := 1, left := PrivateNames.attributeName }) guard.reply
  earlier : guardPosition < position

-- §FS-host-boundary.snapshot: Raw snapshot reads retain their same source-produced privacy
-- guard. Opening probes and arbitrary intervening actor ticks remain in the shared history.
theorem primitive_guarded_copy_read {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) {initial : World} {final : Population}
    {ticks : List (ActorTick runtime)} (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (selected : ticks[position]? = some tick) (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed)
    {context : List Program.Event} {before : List (Request × Option Reply)}
    (source : GuardedCopyCall before request none)
    (trace : adapter.occurrence.logicalBefore = context ++ before.map Program.filesystemPrefixEvent)
    (reading : request.op = .read) :
    Nonempty (PrimitiveGuardedRead runtime ticks actor position engine request) := by
  have primary := PrimitiveFilesystem.filesystem_occurrence_primary adapter.occurrence
    (by intro wrong; rw [reading] at wrong; cases wrong)
    (by intro wrong; rw [reading] at wrong; cases wrong)
    (by intro wrong; rw [reading] at wrong; cases wrong)
  have adapterSource : Prefix (guardedCall request)
      (adapter.occurrence.inside ++ [(request, observed)]) := by simpa only [← primary] using adapter.occurrence.adapter
  have empty := Lowered.read_adapter_empty adapterSource reading
  obtain ⟨inside, insideShape⟩ := prefix_prior_replies source.active
  let earlier := context ++ source.context.map Program.filesystemPrefixEvent
  have logicalTrace : adapter.occurrence.logicalBefore = earlier ++
      source.start.events.map Program.filesystemEvent ++ inside.map Program.filesystemEvent := by
    rw [trace]
    conv => lhs; rw [source.trace, insideShape]
    simp only [earlier, List.map_append, completed_filesystem_events, List.append_assoc]
  have chunks := PrimitiveFilesystem.reached_chunks adapter.occurrence.reached
  rw [logicalTrace, List.append_assoc] at chunks
  obtain ⟨rawEarlier, rest, firstChunks, laterChunks, firstShape⟩ := PrimitiveFilesystem.chunks_split earlier _ chunks
  obtain ⟨rawOpening, rawCopy, openingChunks, copyChunks, lastShape⟩ :=
    PrimitiveFilesystem.chunks_split (source.start.events.map Program.filesystemEvent) _ laterChunks
  have rawTrace : engine.events = rawEarlier ++ rawOpening ++ rawCopy := by
    rw [adapter.occurrence.trace, empty, List.map_nil, List.append_nil, firstShape, lastShape, ← List.append_assoc]
  have history := adapter.source.history
  rw [rawTrace, List.append_assoc] at history
  obtain ⟨openingBefore, leading, following⟩ := actor_with_split rawEarlier _ history
  obtain ⟨copyBefore, opening, copying⟩ := actor_with_split rawOpening rawCopy following
  obtain ⟨guarded⟩ := Lowered.guarded_start_recorded descriptors actor (SourceReturnAt runtime ticks actor)
    rawEarlier.length source.start openingChunks (by simpa only [Nat.zero_add] using opening)
  have copyingSource : Prefix (copyOpened source.fd source.limit)
      (Publication.completed inside ++ [(request, none)]) := by simpa only [insideShape] using source.active
  have copyTrace : rawCopy = inside.map Program.filesystemEvent :=
    PrimitiveFilesystem.chunks_identity copyChunks (Lowered.copy_prefix_identity _ _ copyingSource)
  have copiedHistory := actor_recorded_filesystem (copyTrace ▸ copying)
  have sourcePrefix := prefix_before_last copyingSource
  have physical := physical_prefix_from_history (recorded_history_erase copiedHistory) sourcePrefix
  have live := borrow_prefix (copyOpened_borrow descriptors source.fd guarded.handle source.fd source.limit)
    physical guarded.live
  have requestFd := guarded_copy_call_descriptor source reading
  have requestLive : engine.references request.first = some guarded.handle := by rw [requestFd]; exact live
  obtain ⟨guardPosition, guardTick, guardEngine, nextEngine, guardAt, guardAction, guardPresent,
    afterPresent, count, beforeShape, afterShape⟩ := guarded.guard.sampled
  have earlierSource : guardEngine.events.length < engine.events.length := by
    have bounded := guarded.earlier
    rw [rawTrace]
    simp only [List.length_append] at bounded ⊢
    omega
  let sameGuard : PublicGuard kernel (fun ordinal request reply =>
      SourceReturnAt runtime ticks actor ordinal Reply (.filesystem request) reply) request.first guarded.handle := {
    ordinal := guarded.guard.ordinal
    before := guarded.guard.before
    after := guarded.guard.after
    reply := guarded.guard.reply
    actual := by simpa only [requestFd] using guarded.guard.actual
    sampled := by simpa only [requestFd] using guarded.guard.sampled
    live := by simpa only [requestFd] using guarded.guard.live
    accepted := guarded.guard.accepted
    absent := guarded.guard.absent }
  refine ⟨⟨guarded.handle, requestLive, sameGuard, guardPosition, guardTick, guardAt, ?_,
    source_ordinal_orders_positions journal guardAt selected actor guardEngine engine guardPresent present earlierSource⟩⟩
  simpa only [sameGuard, requestFd] using guardAction

theorem primitive_snapshot_guarded_read {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : ticks[position]? = some tick)
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed)
    (workspace : Option ByteArray) (stdin : Snapshot.Stdin) (limits : Snapshot.Limits)
    {context : List Program.Event} {before : List (Request × Option Reply)}
    (source : Prefix (Snapshot.freeze workspace stdin limits) (before ++ [(request, none)]))
    (sourceTrace : adapter.occurrence.logicalBefore = context ++ before.map Program.filesystemPrefixEvent)
    (reading : request.op = .read) :
    Nonempty (PrimitiveGuardedRead runtime ticks actor position engine request) := by
  obtain ⟨guarded⟩ := freeze_read_sources workspace stdin limits _ _ _ source reading
  exact primitive_guarded_copy_read descriptors journal selected present adapter guarded sourceTrace reading

end LeanCage.Host.Kernel
