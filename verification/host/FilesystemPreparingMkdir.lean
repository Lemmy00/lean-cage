import FilesystemPreparingParents
import FilesystemPreparingSplits

namespace LeanCage.Host.Kernel
open Filesystem

structure PreparingMkdirParent {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed}
    {call : PublicationPreparing.Call adapter.occurrence.logicalBefore request} {position : Nat}
    (resources : PreparingStageResources adapter call position) (family : Family) (scope : ObjectId) where
  current : ObservedCreationParent kernel (fun ordinal query reply =>
    SourceReturnAt runtime all actor ordinal Reply (.filesystem query) reply) engine.events.length
    (tick.before.project engine) call.context.parent.uid request family scope
  beforeGuard : current.observation.sample.ordinal < adapter.occurrence.rawBefore.length

-- §FS-host-boundary.ownership: Join the exact in-progress preparation
-- grammar, raw source chunks and held original stage. Every selected mkdir
-- obtains its actual checked parent without a future fill/cleanup result.
theorem PreparingStageResources.mkdir_parent {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel)
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed}
    {call : PublicationPreparing.Call adapter.occurrence.logicalBefore request} {position : Nat}
    (resources : PreparingStageResources adapter call position) (primary : request = adapter.occurrence.primary)
    (mkdir : request.op = .mkdirAt) {family : Family} {scope : ObjectId}
    (opens : PrivateDirectoryOpens kernel (fun ordinal query reply before after =>
      SourceReturnAt runtime all resources.source.earlier.source.inputActor ordinal Reply (.filesystem query) reply before after ∧
        ordinal < engine.events.length) family)
    (privateRoot : family resources.source.earlier.source.opening.handle.object = some scope) :
    Nonempty (PreparingMkdirParent resources family scope) := by
  obtain ⟨frontier⟩ := Publication.preparing_mkdir_frontier call.host.invocation.authenticated.bundle call.host.source.effective
    call.context.display call.host.source.stdoutHash call.host.source.stderrHash call.context.parent call.context.stage call.active mkdir
  let leading := frontier.hashing ++ frontier.authenticating ++ frontier.current.writing
  have trace : call.inside = Publication.completed leading ++ frontier.current.inside := by
    exact frontier.trace.trans ((congrArg (fun last => Publication.completed frontier.hashing ++
      Publication.completed frontier.authenticating ++ last) frontier.current.trace).trans (by
        simp only [leading, Publication.completed, List.map_append, List.append_assoc]))
  have logical : call.inside.map Program.filesystemPrefixEvent =
      leading.map Program.filesystemEvent ++ frontier.current.inside.map Program.filesystemPrefixEvent := by
    simpa only [List.map_append, completed_filesystem_events] using
      congrArg (List.map Program.filesystemPrefixEvent) trace
  have chunks := resources.point.chunks
  rw [logical] at chunks
  obtain ⟨leadingRaw, exportRaw, leadingChunks, exportChunks, rawTrace⟩ := PrimitiveFilesystem.chunks_split _ _ chunks
  have splitTrace : resources.point.followingRaw ++ resources.source.earlier.guards =
      leadingRaw ++ (exportRaw ++ resources.source.earlier.guards) := by rw [rawTrace, List.append_assoc]
  obtain ⟨point⟩ := resources.split_at descriptors primary splitTrace
  obtain ⟨beforeGuard, exportHistory, guardHistory⟩ :=
    actor_with_split exportRaw resources.source.earlier.guards point.following
  let ordinal := resources.source.earlier.source.input.events.length + 1 +
    (resources.source.earlier.post.map Program.filesystemEvent).length + resources.point.inspectionRaw.length
  have total : ordinal + leadingRaw.length + exportRaw.length + resources.source.earlier.guards.length = engine.events.length := by
    have count := congrArg List.length resources.eventTrace
    have rest := congrArg List.length resources.point.trace
    have inside := congrArg List.length rawTrace
    simp only [List.length_append, List.length_cons, List.length_map] at count rest inside
    dsimp only [ordinal]
    simp only [List.length_map]
    omega
  have starting : family point.observation.handle.object = some scope := by
    rw [point.sameObserved]
    exact privateRoot
  obtain ⟨parent⟩ := Lowered.exports_mkdir_observed descriptors resources.source.earlier.source.inputActor
    (SourceReturnAt runtime all resources.source.earlier.source.inputActor) engine.events.length opens
    frontier.current.current exportChunks exportHistory (by dsimp only [ordinal] at total; omega) point.observation starting
  have retaining := actor_retaining_event_handles descriptors guardHistory (by
    rw [resources.guards]
    exact adapter_namespace_prefix_retaining adapter (.inr (.inl mkdir)))
  have live : (tick.before.project engine).handles parent.directory.fd = some parent.observation.handle := by
    rw [retaining]
    exact parent.observation.live
  let current := parent.observation.advance live (show _ ≤ engine.events.length by dsimp only [ordinal] at total; omega)
  let actual := current.mapOrigin (fun ordinal query reply before after evidence =>
    Eq.mp (congrArg (fun who => SourceReturnAt runtime all who ordinal Reply (.filesystem query) reply before after)
      resources.sameActor) evidence)
  refine ⟨{
    current := {parent with observation := actual}
    beforeGuard := ?_ }⟩
  change parent.observation.sample.ordinal < adapter.occurrence.rawBefore.length
  have earlier := parent.observation.earlier
  have actualTotal := congrArg List.length adapter.occurrence.trace
  have guards := congrArg List.length resources.guards
  simp only [List.length_append, List.length_map] at actualTotal guards
  dsimp only [ordinal] at total
  omega

end LeanCage.Host.Kernel
