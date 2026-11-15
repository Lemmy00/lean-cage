import FilesystemRunFiles
import FilesystemPendingBorrowing
import FilesystemCleanupObservations

namespace LeanCage.Host.Kernel
open Filesystem

structure RunFileResources {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (call : RunFileCall adapter.occurrence.logicalBefore request) (position : Nat) where
  source : CreatedRunContinuation runtime initial all call.outside call.creating call.directory
    (call.inside.map Program.filesystemPrefixEvent) position (tick.before.project engine)
  point : RunAllocationPoint source
  sameActor : source.earlier.source.inputActor = actor
  guards : source.earlier.guards = adapter.occurrence.inside.map Program.filesystemPrefixEvent
  eventTrace : engine.events = source.earlier.source.input.events ++
    .returned (.filesystem source.opening.request) source.opening.reply ::
      (source.earlier.post.map Program.filesystemEvent ++ source.earlier.remaining ++ source.earlier.guards)
  directory : engine.references call.directory.directory.fd = some source.earlier.source.opening.handle
  container : engine.references call.directory.container.fd = some source.root.use.parent

private theorem kept_reference {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel)
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (call : RunFileCall adapter.occurrence.logicalBefore request) {position : Nat}
    {source : CreatedRunContinuation runtime initial all call.outside call.creating call.directory
      (call.inside.map Program.filesystemPrefixEvent) position (tick.before.project engine)}
    (point : RunAllocationPoint source) (primary : request = adapter.occurrence.primary)
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
  have lowered : Program.Prefix (Program.liftFilesystem (call.kind.program call.directory.directory.fd).lower)
      ((point.followingRaw ++ source.earlier.guards) ++ [Program.filesystemPrefixEvent (request, none)]) := by
    simpa only [guards, List.append_assoc] using lowered
  exact actor_borrow_recorded_prefix (actor_borrow_lift source.earlier.source.inputActor
    (call.kind.borrowed descriptors held handle call.directory.directory.fd)) point.history
    (Program.prefix_before_last lowered) live

-- §FS-host-boundary.ownership: This real validator/archive file call
-- derives both current raw references from its SAME actual earlier run
-- allocation; the selected open or helper need never return in the future.
theorem actual_run_file_resources {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (call : RunFileCall adapter.occurrence.logicalBefore request)
    (primary : request = adapter.occurrence.primary) : Nonempty (RunFileResources adapter call position) := by
  obtain ⟨source, sameActor, guards, eventTrace⟩ := primitive_created_run_continuation descriptors lifetimes references
    environment journal selected present adapter call.created call.trace
  obtain ⟨point⟩ := source.allocation descriptors
  exact ⟨⟨source, point, sameActor, guards, eventTrace,
    kept_reference descriptors adapter call point primary guards _ _ point.directory,
    kept_reference descriptors adapter call point primary guards _ _ point.container⟩⟩

theorem RunFileResources.observed {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed}
    {call : RunFileCall adapter.occurrence.logicalBefore request} {position : Nat}
    (resources : RunFileResources adapter call position) :
    ∃ observation : ObservedDirectory kernel (fun ordinal query reply =>
        SourceReturnAt runtime all actor ordinal Reply (.filesystem query) reply)
        engine.events.length (tick.before.project engine) resources.source.opening.uid call.directory.directory,
      observation.handle = resources.source.earlier.source.opening.handle ∧
        observation.sample.ordinal < adapter.occurrence.rawBefore.length := by
  have total := congrArg List.length resources.eventTrace
  have rest := congrArg List.length resources.point.trace
  have actual := congrArg List.length adapter.occurrence.trace
  have guards := congrArg List.length resources.guards
  simp only [List.length_append, List.length_cons, List.length_map] at total rest actual guards
  let original := resources.point.observation.mapOrigin (fun ordinal query reply before after evidence =>
    Eq.mp (congrArg (fun who => SourceReturnAt runtime all who ordinal Reply (.filesystem query) reply before after)
      resources.sameActor) evidence)
  have live : (tick.before.project engine).handles call.directory.directory.fd = some original.handle := by
    change engine.references call.directory.directory.fd = some resources.point.observation.handle
    rw [resources.point.sameObserved]
    exact resources.directory
  have earlier := resources.point.observation.earlier
  have bounded : resources.source.earlier.source.input.events.length + 1 +
      resources.source.earlier.post.length + resources.point.createdAfter.length ≤ engine.events.length := by omega
  refine ⟨original.advance live (by simpa only [List.length_map] using bounded), resources.point.sameObserved, ?_⟩
  change resources.point.observation.sample.ordinal < adapter.occurrence.rawBefore.length
  simp only [List.length_map] at earlier
  omega

end LeanCage.Host.Kernel
