import FilesystemPreparingReferences
import FilesystemStageReference

namespace LeanCage.Host.Kernel
open Filesystem

private theorem source_prefix_left {α : Type} {program : Program α} {first last : List Program.Event}
    (source : Program.Prefix program (first ++ last)) : Program.Prefix program first := by
  induction first generalizing program with
  | nil => exact .empty _
  | cons event first ih =>
    cases first with
    | nil =>
      cases source with
      | returned effect continuation reply events following => exact .returned _ _ _ _ (.empty _)
      | lost effect continuation => exact .lost _ _
    | cons next rest =>
      cases source with
      | returned effect continuation reply events following => exact .returned _ _ _ _ (ih following)

theorem PreparingStageResources.lowered_before {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed}
    {call : PublicationPreparing.Call adapter.occurrence.logicalBefore request} {position : Nat}
    (resources : PreparingStageResources adapter call position) (primary : request = adapter.occurrence.primary) :
    Program.Prefix (Program.liftFilesystem
      (Publication.prepare call.host.invocation.authenticated.bundle call.host.source.effective call.context.display
        call.host.source.stdoutHash call.host.source.stderrHash call.context.parent call.context.stage).lower)
      (resources.point.followingRaw ++ resources.source.earlier.guards) := by
  have rawAdapter : Program.Prefix (PrimitiveFilesystem.lowerEffect (.filesystem request))
      (adapter.occurrence.inside.map Program.filesystemPrefixEvent ++ [Program.filesystemPrefixEvent (request, none)]) := by
    have active := Program.lift_filesystem_prefix (prefix_last_pending adapter.occurrence.adapter)
    rw [← primary] at active
    simpa only [PrimitiveFilesystem.lowerEffect, List.map_append, List.map_singleton] using active
  have original := Program.lift_filesystem_prefix call.active
  simp only [List.map_append, List.map_singleton] at original
  have lowered := PrimitiveFilesystem.pending_chunks_prefix (.filesystem request) original resources.point.chunks rawAdapter
  rw [PrimitiveFilesystem.lower_lift_filesystem] at lowered
  have lowered : Program.Prefix (Program.liftFilesystem
      (Publication.prepare call.host.invocation.authenticated.bundle call.host.source.effective call.context.display
        call.host.source.stdoutHash call.host.source.stderrHash call.context.parent call.context.stage).lower)
      ((resources.point.followingRaw ++ resources.source.earlier.guards) ++ [Program.filesystemPrefixEvent (request, none)]) := by
    simpa only [resources.guards, List.append_assoc] using lowered
  exact Program.prefix_before_last lowered

structure PreparingSplitPoint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed}
    {call : PublicationPreparing.Call adapter.occurrence.logicalBefore request} {position : Nat}
    (resources : PreparingStageResources adapter call position) (first last : List Program.Event) where
  world : World
  earlier : ActorHistoryWith runtime resources.source.earlier.source.inputActor
    (SourceReturnAt runtime all resources.source.earlier.source.inputActor)
    (resources.source.earlier.source.input.events.length + 1 +
      (resources.source.earlier.post.map Program.filesystemEvent).length + resources.point.inspectionRaw.length)
    resources.point.world first world
  following : ActorHistoryWith runtime resources.source.earlier.source.inputActor
    (SourceReturnAt runtime all resources.source.earlier.source.inputActor)
    (resources.source.earlier.source.input.events.length + 1 +
      (resources.source.earlier.post.map Program.filesystemEvent).length + resources.point.inspectionRaw.length + first.length)
    world last (tick.before.project engine)
  directory : world.handles call.context.stage.directory.fd = some resources.source.earlier.source.opening.handle
  container : world.handles call.context.stage.container.fd = some resources.source.root.use.parent
  observation : ObservedDirectory kernel (fun ordinal query reply =>
    SourceReturnAt runtime all resources.source.earlier.source.inputActor ordinal Reply (.filesystem query) reply)
    (resources.source.earlier.source.input.events.length + 1 +
      (resources.source.earlier.post.map Program.filesystemEvent).length + resources.point.inspectionRaw.length + first.length)
    world call.context.parent.uid call.context.stage.directory
  sameObserved : observation.handle = resources.source.earlier.source.opening.handle

-- §FS-host-boundary.ownership: Any actual preparation subphase keeps the
-- same original stage/container at its precise global source cut. All
-- intervening returned calls, probes and peer effects remain recorded.
theorem PreparingStageResources.split_at {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel)
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed}
    {call : PublicationPreparing.Call adapter.occurrence.logicalBefore request} {position : Nat}
    (resources : PreparingStageResources adapter call position) (primary : request = adapter.occurrence.primary)
    {first last : List Program.Event}
    (trace : resources.point.followingRaw ++ resources.source.earlier.guards = first ++ last) :
    Nonempty (PreparingSplitPoint resources first last) := by
  have history := resources.point.history
  rw [trace] at history
  obtain ⟨world, earlier, following⟩ := actor_with_split first last history
  have active := resources.lowered_before primary
  rw [trace] at active
  have firstActive := source_prefix_left active
  have preserve : ∀ held handle, resources.point.world.handles held = some handle → world.handles held = some handle := by
    intro held handle live
    exact actor_borrow_recorded_prefix (actor_borrow_lift resources.source.earlier.source.inputActor
      (Lowered.publication_prepare_borrow descriptors held handle _ _ _ _ _ _ _)) earlier firstActive live
  have live := preserve _ _ resources.point.directory
  have observedLive : world.handles call.context.stage.directory.fd = some resources.point.observation.handle := by
    rw [resources.point.sameObserved]
    exact live
  exact ⟨{
    world
    earlier
    following
    directory := live
    container := preserve _ _ resources.point.container
    observation := resources.point.observation.advance observedLive (by omega)
    sameObserved := resources.point.sameObserved }⟩

end LeanCage.Host.Kernel
