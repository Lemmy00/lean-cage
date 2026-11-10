import FilesystemTraversalParents
import FilesystemStagingParents
import FilesystemPrimitiveParents

namespace LeanCage.Host.Kernel
open Filesystem

structure ContentMkdirCall (before : List Program.Event) (request : Request) where
  source : PublicationCreation.HostSite before request none
  context : PublicationCreation.Staged source.source.target
  inside : List (Request × Option Reply)
  active : Prefix (Publication.prepare source.invocation.authenticated.bundle source.source.effective context.display
    source.source.stdoutHash source.source.stderrHash context.parent context.stage) (inside ++ [(request, none)])
  trace : source.source.inside = Publication.completed
    (context.displaying ++ context.selecting ++ context.creating) ++ inside
  site : source.source.site = .filling context inside active trace

-- §FS-host-boundary.ownership: These roles come from the maintained caller's exact branch;
-- a reserved name by itself does not make a native/public callback creation application-owned.
inductive PrimitiveMkdirRole {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed) : Type 1 where
  | run (source : RunCreationPrefix adapter.occurrence.logicalBefore request none)
  | traversal (source : TraversalCall adapter.occurrence.logicalBefore request)
  | staging (source : StagingCall adapter.occurrence.logicalBefore request)
  | content (source : ContentMkdirCall adapter.occurrence.logicalBefore request)

-- §FS-host-boundary.ownership: This universal producer classifies the SAME actual raw mkdir,
-- preserving committed failure/loss and the concrete source invocation, input and path choices.
theorem actual_primitive_mkdir_role {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (mkdir : request.op = .mkdirAt) :
    ∃ adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed,
      Nonempty (PrimitiveMkdirRole adapter) := by
  obtain ⟨site⟩ := actual_primitive_mkdir_site descriptors lifetimes references environment journal selected action present mkdir
  cases site.site with
  | creating source => exact ⟨site.adapter, ⟨.run source⟩⟩
  | publishing invocation =>
    obtain ⟨source⟩ := PublicationCreation.host_mkdir_site invocation mkdir
    cases classified : source.source.site with
    | selecting context inside cursor trace =>
      exact ⟨site.adapter, ⟨.traversal ⟨source, context, inside, cursor, trace, classified⟩⟩⟩
    | staging context inside child trace =>
      exact ⟨site.adapter, ⟨.staging ⟨source, context, inside, child, trace, classified⟩⟩⟩
    | filling context inside active trace =>
      exact ⟨site.adapter, ⟨.content ⟨source, context, inside, active, trace, classified⟩⟩⟩

end LeanCage.Host.Kernel
