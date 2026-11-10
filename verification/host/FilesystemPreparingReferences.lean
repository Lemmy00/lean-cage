import FilesystemPreparingStageReferences
import FilesystemPendingBorrowing

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.publication: Every earlier raw preparation call keeps
-- the original stage/container. The selected call is still pending; a
-- future prepare return or publication result supplies no resource premise.
theorem PreparingStagePoint.current_reference {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel)
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {call : PublicationPreparing.Call adapter.occurrence.logicalBefore request} {limit : Nat}
    {source : PreparingStageContinuation runtime initial all call limit (tick.before.project engine)}
    (point : PreparingStagePoint source) (primary : request = adapter.occurrence.primary)
    (guards : source.earlier.guards = adapter.occurrence.inside.map Program.filesystemPrefixEvent)
    (held : UInt64) (handle : Handle) (live : point.world.handles held = some handle) :
    (tick.before.project engine).handles held = some handle := by
  have rawAdapter : Program.Prefix (PrimitiveFilesystem.lowerEffect (.filesystem request))
      (adapter.occurrence.inside.map Program.filesystemPrefixEvent ++ [Program.filesystemPrefixEvent (request, none)]) := by
    have active := Program.lift_filesystem_prefix (prefix_last_pending adapter.occurrence.adapter)
    rw [← primary] at active
    simpa only [PrimitiveFilesystem.lowerEffect, List.map_append, List.map_singleton] using active
  have original := Program.lift_filesystem_prefix call.active
  simp only [List.map_append, List.map_singleton] at original
  have lowered := PrimitiveFilesystem.pending_chunks_prefix (.filesystem request) original point.chunks rawAdapter
  rw [PrimitiveFilesystem.lower_lift_filesystem] at lowered
  have lowered : Program.Prefix (Program.liftFilesystem
      (Publication.prepare call.host.invocation.authenticated.bundle call.host.source.effective call.context.display
        call.host.source.stdoutHash call.host.source.stderrHash call.context.parent call.context.stage).lower)
      ((point.followingRaw ++ source.earlier.guards) ++ [Program.filesystemPrefixEvent (request, none)]) := by
    simpa only [guards, List.append_assoc] using lowered
  exact actor_borrow_recorded_prefix (actor_borrow_lift source.earlier.source.inputActor
    (Lowered.publication_prepare_borrow descriptors held handle _ _ _ _ _ _ _)) point.history
    (Program.prefix_before_last lowered) live

structure PreparingStageResources {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (call : PublicationPreparing.Call adapter.occurrence.logicalBefore request) (position : Nat) where
  source : PreparingStageContinuation runtime initial all call position (tick.before.project engine)
  point : PreparingStagePoint source
  sameActor : source.earlier.source.inputActor = actor
  guards : source.earlier.guards = adapter.occurrence.inside.map Program.filesystemPrefixEvent
  eventTrace : engine.events = source.earlier.source.input.events ++
    .returned (.filesystem source.opening.request) source.opening.reply ::
      (source.earlier.post.map Program.filesystemEvent ++ source.earlier.remaining ++ source.earlier.guards)
  directory : engine.references call.context.stage.directory.fd = some source.earlier.source.opening.handle
  container : engine.references call.context.stage.container.fd = some source.root.use.parent

-- §FS-host-boundary.ownership: This in-progress source consumer derives
-- both current references from its actual earlier fresh stage and stat.
-- It does not require a successful or failed future preparation.
theorem actual_preparing_stage_resources {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (call : PublicationPreparing.Call adapter.occurrence.logicalBefore request)
    (primary : request = adapter.occurrence.primary) : Nonempty (PreparingStageResources adapter call position) := by
  obtain ⟨source, sameActor, guards, eventTrace⟩ := primitive_preparing_stage_continuation descriptors aliases lifetimes references
    environment journal selected present adapter call
  obtain ⟨point⟩ := source.allocation descriptors
  exact ⟨⟨source, point, sameActor, guards, eventTrace,
    point.current_reference descriptors adapter primary guards _ _ point.directory,
    point.current_reference descriptors adapter primary guards _ _ point.container⟩⟩

end LeanCage.Host.Kernel
