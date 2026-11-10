import FilesystemPublicationChains
import PublicationProofs.CleanupSource
import FilesystemPrimitiveRecording

namespace LeanCage.Host.Kernel
open Filesystem

structure PrimitiveRelativeUnlinkParent {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (all : List (ActorTick runtime)) (tick : ActorTick runtime)
    (actor : ActorId) (engine : EngineState) (request : Request) (observed : Option Reply)
    {uid : Nat} {root : UInt64} {components : List String} {directory : Bool}
    {before : List (Request × Option Reply)}
    (source : Publication.RelativeUnlinkFrontier uid root components directory before request none) where
  adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed
  rawBefore : List Program.Event
  opening : List Program.Event
  before : World
  after : World
  trace : engine.events = rawBefore ++ opening ++ adapter.occurrence.inside.map Program.filesystemPrefixEvent
  chunks : PrimitiveFilesystem.Chunks (source.opening.map Program.filesystemEvent) opening
  leading : ActorHistoryWith runtime actor (SourceReturnAt runtime all actor) 0
    (adapter.source.launch.tick.after.project (.initialFrom (PrimitiveFilesystem.lower Entrypoint.run)
      adapter.source.launch.references adapter.source.launch.closeExec adapter.source.launch.workingDirectory)) rawBefore before
  actual : ActorHistoryWith runtime actor (SourceReturnAt runtime all actor) rawBefore.length before opening after
  guarded : ActorHistoryWith runtime actor (SourceReturnAt runtime all actor) (rawBefore.length + opening.length)
    after (adapter.occurrence.inside.map Program.filesystemPrefixEvent) (tick.before.project engine)

-- §FS-host-boundary.ownership: The actual recursive source frontier selects its
-- real chain in the SAME raw history. No future unlink reply, helper return,
-- independent descriptor table or guessed object identity is used.
theorem primitive_relative_unlink_parent {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {uid : Nat} {root : UInt64} {components : List String} {directory : Bool}
    {before : List (Request × Option Reply)}
    (source : Publication.RelativeUnlinkFrontier uid root components directory before request none)
    {context : List Program.Event}
    (trace : adapter.occurrence.logicalBefore = context ++ before.map Program.filesystemPrefixEvent) :
    Nonempty (PrimitiveRelativeUnlinkParent runtime initial all tick actor engine request observed source) := by
  have insideEmpty := Publication.relative_unlink_inside_empty source
  have sourceTrace : before = Publication.completed source.opening := by
    simpa only [insideEmpty, List.append_nil] using source.trace
  have logical : adapter.occurrence.logicalBefore = context ++ source.opening.map Program.filesystemEvent := by
    exact trace.trans (congrArg (context ++ ·)
      ((congrArg (List.map Program.filesystemPrefixEvent) sourceTrace).trans (completed_filesystem_events _)))
  have chunks := PrimitiveFilesystem.reached_chunks adapter.occurrence.reached
  rw [logical] at chunks
  obtain ⟨rawBefore, opening, leadingChunks, openingChunks, rawTrace⟩ := PrimitiveFilesystem.chunks_split _ _ chunks
  have full : engine.events = rawBefore ++ opening ++ adapter.occurrence.inside.map Program.filesystemPrefixEvent :=
    adapter.occurrence.trace.trans (congrArg (· ++ adapter.occurrence.inside.map Program.filesystemPrefixEvent) rawTrace)
  have history := adapter.source.history
  rw [full, List.append_assoc] at history
  obtain ⟨before, leading, following⟩ := actor_with_split rawBefore _ history
  obtain ⟨after, actual, guarded⟩ := actor_with_split opening _ following
  exact ⟨⟨adapter, rawBefore, opening, before, after, full, openingChunks, leading,
    by simpa only [Nat.zero_add] using actual, by simpa only [Nat.zero_add] using guarded⟩⟩

-- §FS-host-boundary.ownership: An actual retained starting root and the constructed
-- current scope journal establish this unlink's current nested parent. Every
-- intervening guard is separately proved descriptor-preserving.
theorem PrimitiveRelativeUnlinkParent.current_scope {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) {family : Family}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {uid : Nat} {root : UInt64} {components : List String} {directory : Bool}
    {before : List (Request × Option Reply)}
    {source : Publication.RelativeUnlinkFrontier uid root components directory before request none}
    (physical : PrimitiveRelativeUnlinkParent runtime initial all tick actor engine request observed source)
    (opens : PrivateDirectoryOpens kernel (fun ordinal request reply before after =>
      SourceReturnAt runtime all actor ordinal Reply (.filesystem request) reply before after ∧ ordinal < engine.events.length) family)
    {rootHandle : Handle} {scope : ObjectId} (live : physical.before.handles root = some rootHandle)
    (privateRoot : family rootHandle.object = some scope) :
    ∃ parent, engine.references request.first = some parent ∧ family parent.object = some scope := by
  have bound : physical.rawBefore.length + physical.opening.length ≤ engine.events.length := by
    have length := congrArg List.length physical.trace
    simp only [List.length_append, List.length_map] at length
    omega
  obtain ⟨parent, parentLive, parentScope⟩ := Lowered.publication_chain_private descriptors actor
    (SourceReturnAt runtime all actor) engine.events.length opens source.chain physical.chunks physical.actual bound live privateRoot
  have removing : request.op = .unlinkAt := by rw [source.operation]
  have kept := actor_retaining_event_handles descriptors physical.guarded
    (adapter_namespace_prefix_retaining physical.adapter (.inr (.inr (.inl removing))))
  have finalLive : (tick.before.project engine).handles source.parent = some parent := by rw [kept]; exact parentLive
  have descriptor : request.first = source.parent := congrArg Request.first source.operation
  exact ⟨parent, by rw [descriptor]; exact finalLive, parentScope⟩

end LeanCage.Host.Kernel
