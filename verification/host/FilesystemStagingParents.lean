import FilesystemPublicationCreation
import FilesystemLoweredAliases
import FilesystemPrimitivePhases
import FilesystemPrimitiveFrames

namespace LeanCage.Host.Kernel
open Filesystem

structure StagingCall (before : List Program.Event) (request : Request) where
  source : PublicationCreation.HostSite before request none
  selection : PublicationCreation.Selected source.source.target
  inside : List (Request × Option Reply)
  child : FreshChildCall selection.parent inside request
  siteTrace : source.source.inside = Publication.completed
    (selection.displaying ++ selection.selecting) ++ inside
  site : source.source.site = .staging selection inside child siteTrace

def StagingCall.selectingContext {before : List Program.Event} {request : Request}
    (call : StagingCall before request) : List Program.Event :=
  call.source.invocation.packet.events ++ call.source.invocation.authenticated.events ++
    call.source.invocation.run.context.events ++
    (call.source.source.identifying ++ call.source.source.selecting ++ call.selection.displaying).map Program.filesystemEvent

-- §FS-host-boundary.ownership: This prefix is the actual public selection, dot alias and
-- bounded random calls of the same staging branch, ending immediately before its mkdir.
theorem staging_parent_trace {before : List Program.Event} {request : Request}
    (call : StagingCall before request) :
    before = call.selectingContext ++ call.selection.selecting.map Program.filesystemEvent ++
      (call.child.opening ++ call.child.child.randomEvents).map Program.filesystemEvent := by
  conv =>
    lhs
    rw [call.source.invocation.trace, call.source.invocation.run.trace, call.source.projection,
      call.source.source.trace, call.siteTrace, call.child.trace, call.child.child.trace]
  simp only [StagingCall.selectingContext, List.map_append, completed_filesystem_events, List.append_assoc]

structure PrimitiveStagingParent {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (ticks : List (ActorTick runtime)) (tick : ActorTick runtime)
    (actor : ActorId) (engine : EngineState) (request : Request) (observed : Option Reply) where
  adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed
  source : StagingCall adapter.occurrence.logicalBefore request
  parent : ObservedParent kernel (fun ordinal request reply => SourceReturnAt runtime ticks actor ordinal Reply
    (.filesystem request) reply) engine.events.length (tick.before.project engine) source.selection.parent
  container : ObservedDirectory kernel (fun ordinal request reply => SourceReturnAt runtime ticks actor ordinal Reply
    (.filesystem request) reply) engine.events.length (tick.before.project engine)
    source.selection.parent.uid source.child.container
  sameParent : container.handle.object = parent.directory.handle.object
  parentBeforeGuard : parent.directory.sample.ordinal < adapter.occurrence.rawBefore.length
  selection : PrimitivePhaseAt runtime initial ticks tick actor engine
    (Directories.parent source.source.source.target true) (.ok source.selection.parent)
  parentAtSelection : selection.after.handles source.selection.parent.directory.fd = some parent.directory.handle
  selectionLimit : selection.rawBefore.length + selection.events.length ≤ engine.events.length

-- §FS-host-boundary.ownership: The actual selected staging mkdir keeps both real aliases
-- and the original checked public parent. Raw probes and all prior callback rows stay intact.
theorem primitive_staging_parent {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed)
    (source : StagingCall adapter.occurrence.logicalBefore request)
    (mkdir : request.op = .mkdirAt) :
    Nonempty (PrimitiveStagingParent runtime initial ticks tick actor engine request observed) := by
  obtain ⟨selection⟩ := primitive_filesystem_phase adapter source.selection.selected (staging_parent_trace source)
  let phase := selection.phase
  obtain ⟨parent⟩ := Lowered.parent_recorded descriptors _ phase.rawBefore.length
    source.source.source.target true phase.actual
  have chunks : PrimitiveFilesystem.Chunks
      (source.child.opening.map Program.filesystemEvent ++ source.child.child.randomEvents.map Program.filesystemEvent)
      selection.rawTail := by simpa only [List.map_append] using selection.chunks
  obtain ⟨openingRaw, randomRaw, openingChunks, randomChunks, rawTrace⟩ :=
    PrimitiveFilesystem.chunks_split _ _ chunks
  have randomSame : randomRaw = source.child.child.randomEvents.map Program.filesystemEvent :=
    PrimitiveFilesystem.chunks_identity randomChunks (random_events_identity source.child.child.randomness)
  have history := phase.tail
  rw [selection.suffix, rawTrace, randomSame, List.append_assoc] at history
  obtain ⟨openedWorld, openingHistory, remaining⟩ := actor_with_split openingRaw _ history
  obtain ⟨openingEvents, openingSource, openingTrace⟩ :=
    PrimitiveFilesystem.chunks_filesystem_returns source.child.opened openingChunks
  have opening : RecordedRun kernel (fun ordinal request reply => SourceReturnAt runtime ticks actor ordinal Reply
      (.filesystem request) reply) (phase.rawBefore.length + phase.events.length)
      (Directories.openAt source.selection.parent.uid source.selection.parent.directory.fd ".".toUTF8).lower
      phase.after openingEvents openedWorld (.ok source.child.container) :=
    ⟨openingSource, actor_recorded_filesystem (openingTrace ▸ openingHistory)⟩
  obtain ⟨container, sameObject⟩ := Lowered.directory_open_alias_recorded descriptors aliases _ _ _ _
    parent.directory.handle opening parent.directory.live
  have parentKept := (Lowered.history_borrow source.selection.parent.directory.fd parent.directory.handle
    (Lowered.directoryOpen_borrow descriptors _ _ _ _ _) opening parent.directory.live).1
  have trailing : ∀ event ∈ source.child.child.randomEvents.map Program.filesystemEvent ++
      adapter.occurrence.inside.map Program.filesystemPrefixEvent, RetainingEvent event := by
    intro event member
    rcases List.mem_append.mp member with random | guard
    · exact random_events_retaining source.child.child.randomness event random
    · exact adapter_namespace_prefix_retaining adapter (.inr (.inl mkdir)) event guard
  have handles := actor_retaining_event_handles descriptors remaining trailing
  have parentLive : (tick.before.project engine).handles source.selection.parent.directory.fd =
      some parent.directory.handle := by rw [handles]; exact parentKept
  have containerLive : (tick.before.project engine).handles source.child.container.fd = some container.handle := by
    rw [handles]
    exact container.live
  have totalLength := congrArg List.length adapter.occurrence.trace
  have suffixLength := congrArg List.length selection.suffix
  have phaseLength := congrArg List.length phase.trace
  have phaseSuffix : phase.rawAfter.length = selection.phase.rawAfter.length := rfl
  simp only [List.length_append, List.length_map] at totalLength suffixLength phaseLength
  have parentLimit : phase.rawBefore.length + phase.events.length ≤ engine.events.length := by omega
  have containerLimit : phase.rawBefore.length + phase.events.length + openingEvents.length ≤ engine.events.length := by
    have rawLength := congrArg List.length rawTrace
    have openingLength := congrArg List.length openingTrace
    simp only [List.length_append, List.length_map] at rawLength openingLength
    omega
  refine ⟨⟨adapter, source,
    ⟨parent.directory.advance parentLive parentLimit, parent.identity,
      Nat.lt_of_lt_of_le parent.identityEarlier parentLimit⟩,
    container.advance containerLive containerLimit, sameObject, ?_, phase, parent.directory.live, parentLimit⟩⟩
  have earlier := parent.directory.earlier
  change parent.directory.sample.ordinal < adapter.occurrence.rawBefore.length
  omega

end LeanCage.Host.Kernel
