import FilesystemPublicationCreation
import FilesystemPublicParents
import FilesystemPrimitivePhases
import FilesystemPrimitiveFrames

namespace LeanCage.Host.Kernel
open Filesystem

structure TraversalCall (before : List Program.Event) (request : Request) where
  source : PublicationCreation.HostSite before request none
  display : PublicationCreation.Displayed source.source.target
  inside : List (Request × Option Reply)
  cursor : ParentTraversal.ParentMkdir source.source.target true inside request
  siteTrace : source.source.inside = Publication.completed display.displaying ++ inside
  site : source.source.site = .selecting display inside cursor siteTrace

private theorem started_components (path : ByteArray) {events : List (Request × Reply)} {selected : SourcePaths.Started}
    (run : Returns (SourcePaths.start path) events (.ok selected)) : SourcePaths.components path = .ok selected.parts := by
  have observation := Snapshot.sourceStart_source path run
  cases observation <;> assumption

def TraversalCall.startingContext {before : List Program.Event} {request : Request}
    (call : TraversalCall before request) : List Program.Event :=
  call.source.invocation.packet.events ++ call.source.invocation.authenticated.events ++
    call.source.invocation.run.context.events ++
    (call.source.source.identifying ++ call.source.source.selecting ++ call.display.displaying).map Program.filesystemEvent

theorem TraversalCall.arguments {before : List Program.Event} {request : Request}
    (call : TraversalCall before request) :
    request.op = .mkdirAt ∧ request.first = call.cursor.cursor.current.fd ∧ request.second = 448 ∧
      Directories.component request.left = true ∧ PrivateNames.reservedBytes request.left = false := by
  have parsed := started_components call.source.source.target call.cursor.started
  have fields := source_components_are_components call.source.source.target call.cursor.selected.parts parsed
    call.cursor.cursor.name (List.dropLast_subset _ call.cursor.cursor.member)
  simpa only [call.cursor.cursor.operation] using (show
    Op.mkdirAt = .mkdirAt ∧ call.cursor.cursor.current.fd = call.cursor.cursor.current.fd ∧
      (448 : UInt64) = 448 ∧ Directories.component call.cursor.cursor.name = true ∧
      PrivateNames.reservedBytes call.cursor.cursor.name = false from ⟨rfl, rfl, rfl, fields⟩)

-- §FS-host-boundary.ownership: This exact source prefix names the retained base, its UID
-- check and completed visited components before an in-progress public path mkdir.
theorem traversal_parent_trace {before : List Program.Event} {request : Request}
    (call : TraversalCall before request) :
    before = call.startingContext ++ call.cursor.selecting.map Program.filesystemEvent ++
      [.returned (.filesystem {op := .euid}) call.cursor.identity] ++
      call.cursor.inspecting.map Program.filesystemEvent ++ call.cursor.cursor.events.map Program.filesystemEvent := by
  conv =>
    lhs
    rw [call.source.invocation.trace, call.source.invocation.run.trace, call.source.projection,
      call.source.source.trace, call.siteTrace, call.cursor.trace, call.cursor.cursor.trace]
  simp only [TraversalCall.startingContext, List.map_append, completed_filesystem_events,
    List.map_cons, Program.filesystemPrefixEvent, List.append_assoc, List.cons_append, List.nil_append]

structure PrimitiveTraversalParent {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (ticks : List (ActorTick runtime)) (tick : ActorTick runtime)
    (actor : ActorId) (engine : EngineState) (request : Request) (observed : Option Reply) where
  adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed
  source : TraversalCall adapter.occurrence.logicalBefore request
  starting : PrimitivePhaseAt runtime initial ticks tick actor engine
    (SourcePaths.start source.source.source.target) (.ok source.cursor.selected)
  base : GuardedHandle kernel (fun ordinal request reply => SourceReturnAt runtime ticks actor ordinal Reply
    (.filesystem request) reply) (starting.rawBefore.length + starting.events.length) starting.after source.cursor.selected.base
  visited : List ByteArray
  parts : source.cursor.selected.parts.dropLast = visited ++ source.cursor.cursor.name :: source.cursor.cursor.rest
  walkBefore : World
  walkAfter : World
  walkOrdinal : Nat
  walkEvents : List (Request × Reply)
  walked : RecordedRun kernel (fun ordinal request reply => SourceReturnAt runtime ticks actor ordinal Reply
    (.filesystem request) reply) walkOrdinal
    (Directories.descend source.cursor.identity.1.toNat true source.cursor.base visited).lower
    walkBefore walkEvents walkAfter (.ok source.cursor.cursor.current)
  inspected : ObservedDirectory kernel (fun ordinal request reply => SourceReturnAt runtime ticks actor ordinal Reply
    (.filesystem request) reply) walkOrdinal walkBefore source.cursor.identity.1.toNat source.cursor.base
  sameBase : inspected.handle = base.handle
  identity : UidSample kernel (fun ordinal request reply => SourceReturnAt runtime ticks actor ordinal Reply
    (.filesystem request) reply) source.cursor.identity.1.toNat
  current : ObservedDirectory kernel (fun ordinal request reply => SourceReturnAt runtime ticks actor ordinal Reply
    (.filesystem request) reply) engine.events.length (tick.before.project engine)
    source.cursor.identity.1.toNat source.cursor.cursor.current
  currentAtWalk : walkAfter.handles source.cursor.cursor.current.fd = some current.handle
  parentBeforeGuard : current.sample.ordinal < adapter.occurrence.rawBefore.length
  startingLimit : starting.rawBefore.length + starting.events.length ≤ engine.events.length
  walkLimit : walkOrdinal + walkEvents.length ≤ engine.events.length

-- §FS-host-boundary.ownership: The source cursor is interpreted through its SAME raw chunks,
-- retaining every probe/interference step and the last real checked directory before mkdir.
theorem primitive_traversal_parent {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel)
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed)
    (source : TraversalCall adapter.occurrence.logicalBefore request) (mkdir : request.op = .mkdirAt) :
    Nonempty (PrimitiveTraversalParent runtime initial ticks tick actor engine request observed) := by
  have trace : adapter.occurrence.logicalBefore = source.startingContext ++
      source.cursor.selecting.map Program.filesystemEvent ++
      [.returned (.filesystem {op := .euid}) source.cursor.identity] ++
      (source.cursor.inspecting.map Program.filesystemEvent ++ source.cursor.cursor.events.map Program.filesystemEvent) := by
    simpa only [List.append_assoc] using traversal_parent_trace source
  obtain ⟨selection⟩ := primitive_filesystem_phase adapter source.cursor.started (context := source.startingContext)
    (following := [.returned (.filesystem {op := .euid}) source.cursor.identity] ++
      (source.cursor.inspecting.map Program.filesystemEvent ++ source.cursor.cursor.events.map Program.filesystemEvent))
    (by simpa only [List.append_assoc] using trace)
  let phase := selection.phase
  obtain ⟨base⟩ := Lowered.source_start_guard_recorded descriptors _ phase.rawBefore.length
    source.source.source.target phase.actual
  obtain ⟨visited, parts, walkSource⟩ := source.cursor.cursor.walk.source
  have chunks : PrimitiveFilesystem.Chunks
      ([.returned (.filesystem {op := .euid}) source.cursor.identity] ++
        (source.cursor.inspecting.map Program.filesystemEvent ++ source.cursor.cursor.events.map Program.filesystemEvent))
      selection.rawTail := selection.chunks
  obtain ⟨uidRaw, restRaw, uidChunks, restChunks, rawTrace⟩ := PrimitiveFilesystem.chunks_split _ _ chunks
  obtain ⟨inspectRaw, walkRaw, inspectChunks, walkChunks, restTrace⟩ := PrimitiveFilesystem.chunks_split _ _ restChunks
  have uidSame : uidRaw = [.returned (.filesystem {op := .euid}) source.cursor.identity] :=
    PrimitiveFilesystem.chunks_identity uidChunks (by
      intro event member
      have same := List.mem_singleton.mp member
      subst event
      exact PrimitiveFilesystem.euid_identity)
  obtain ⟨inspectEvents, inspectSource, inspectTrace⟩ :=
    PrimitiveFilesystem.chunks_filesystem_returns source.cursor.inspected inspectChunks
  obtain ⟨walkEvents, walkedSource, walkTrace⟩ :=
    PrimitiveFilesystem.chunks_filesystem_returns walkSource walkChunks
  have history := phase.tail
  rw [selection.suffix, rawTrace, restTrace, uidSame, inspectTrace, walkTrace] at history
  simp only [List.cons_append, List.append_assoc] at history
  obtain ⟨identityBefore, identityAfter, beforeIdentity, operation, sampled, afterUid⟩ := actor_with_head history
  have identityLive : identityBefore.handles source.cursor.selected.base = some base.handle := by
    rw [actor_retaining_event_handles descriptors beforeIdentity (by intro event member; cases member)]
    exact base.live
  have afterIdentityLive : identityAfter.handles source.cursor.selected.base = some base.handle := by
    rw [descriptors.retained _ _ _ _ operation (by simp [RetainsDescriptors])]
    exact identityLive
  obtain ⟨inspectAfter, inspectHistory, afterInspect⟩ :=
    actor_with_split (inspectEvents.map Program.filesystemEvent) _ afterUid
  obtain ⟨walkAfter, walkHistory, guards⟩ :=
    actor_with_split (walkEvents.map Program.filesystemEvent) _ afterInspect
  have inspected : RecordedRun kernel (fun ordinal request reply => SourceReturnAt runtime ticks actor ordinal Reply
      (.filesystem request) reply) (phase.rawBefore.length + phase.events.length + 1)
      (Directories.inspect source.cursor.identity.1.toNat source.cursor.selected.base).lower
      identityAfter inspectEvents inspectAfter (.ok source.cursor.base) :=
    ⟨inspectSource, actor_recorded_filesystem inspectHistory⟩
  have baseRaw : base.handle.rawOwned = true := by
    apply descriptors.after_raw _ _ _ _ base.guard.actual source.cursor.selected.base base.handle
    rw [(kernel.attribute_frame _ _ _ _ base.guard.actual rfl).1]
    exact base.guard.live
  obtain ⟨initialObserved⟩ := Kernel.directory_inspect_recorded descriptors _ _ _ _ base.handle
    ⟨Lowered.directory_inspect_identity _ _ ▸ inspected.1, inspected.2⟩ afterIdentityLive baseRaw
  have sameBase : initialObserved.handle = base.handle := by
    obtain ⟨sameFd, reply, inspectionSource, parsed, trusted⟩ := Retrieval.directoryInspection_source _ _
      (Lowered.directory_inspect_identity _ _ ▸ inspected.1)
    have handles := Lowered.recorded_retaining_handles descriptors inspected.2 (by
      intro event member
      have same : event = ({op := .stat, first := source.cursor.selected.base}, reply) := by
        simpa only [inspectionSource, List.mem_singleton] using member
      rw [same]
      simp [RetainsDescriptors])
    have live : inspectAfter.handles source.cursor.base.fd = some base.handle := by
      rw [sameFd, handles]
      exact afterIdentityLive
    exact Option.some.inj (initialObserved.live.symm.trans live)
  have walked : RecordedRun kernel (fun ordinal request reply => SourceReturnAt runtime ticks actor ordinal Reply
      (.filesystem request) reply) (phase.rawBefore.length + phase.events.length + 1 + inspectEvents.length)
      (Directories.descend source.cursor.identity.1.toNat true source.cursor.base visited).lower
      inspectAfter walkEvents walkAfter (.ok source.cursor.cursor.current) :=
    ⟨walkedSource, by simpa only [List.length_map] using actor_recorded_filesystem walkHistory⟩
  obtain ⟨current⟩ := Lowered.directory_descend_recorded descriptors _ _ _ true source.cursor.base visited initialObserved walked
  have currentLive : (tick.before.project engine).handles source.cursor.cursor.current.fd = some current.handle := by
    rw [actor_retaining_event_handles descriptors guards
      (adapter_namespace_prefix_retaining adapter (.inr (.inl mkdir)))]
    exact current.live
  have firstLength := congrArg List.length adapter.occurrence.trace
  have phaseLength := congrArg List.length phase.trace
  have suffixLength := congrArg List.length selection.suffix
  have rawLength := congrArg List.length rawTrace
  have restLength := congrArg List.length restTrace
  have uidLength := congrArg List.length uidSame
  have inspectLength := congrArg List.length inspectTrace
  have walkLength := congrArg List.length walkTrace
  have phaseSuffix : phase.rawAfter.length = selection.phase.rawAfter.length := rfl
  simp only [List.length_append, List.length_map, List.length_singleton] at firstLength phaseLength suffixLength rawLength restLength uidLength inspectLength walkLength
  have startLimit : phase.rawBefore.length + phase.events.length ≤ engine.events.length := by omega
  have walkLimit : phase.rawBefore.length + phase.events.length + 1 + inspectEvents.length + walkEvents.length ≤
      engine.events.length := by omega
  have beforeGuard : current.sample.ordinal < adapter.occurrence.rawBefore.length := by
    have earlier := current.earlier
    omega
  refine ⟨⟨adapter, source, phase, base, visited, parts, inspectAfter, walkAfter,
    phase.rawBefore.length + phase.events.length + 1 + inspectEvents.length, walkEvents, walked,
    initialObserved, sameBase,
    ⟨phase.rawBefore.length + phase.events.length, identityBefore, identityAfter, source.cursor.identity,
      operation, sampled, source.cursor.successful, source.cursor.empty, rfl⟩,
    current.advance currentLive walkLimit, current.live, beforeGuard, startLimit, walkLimit⟩⟩

-- §FS-host-boundary.ownership: Even before the selected public-path mkdir returns, its real
-- checked parent is public in the completed custody prefix; no caller-provided FD role is used.
theorem PrimitiveTraversalParent.public_parent {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {semantics : NameSemanticsView} {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime)
    (lookup : DynamicDataLookupContract kernel semantics initialObjects dataObjects)
    (cwdLookup : WorkingDirectoryContract kernel initialObjects dataObjects)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    (selected : ticks[position]? = some tick) (present : tick.before.actors actor = some engine)
    {leading trailing : List (ActorTick runtime)} {first family : Family}
    (shape : ticks = leading ++ tick :: trailing) (count : leading.length = position)
    (prefixLabels : ScopeJournal runtime initialObjects dataObjects semantics
      (Population.empty initial) first leading tick.before family)
    {request : Request} {observed : Option Reply}
    (resources : PrimitiveTraversalParent runtime initial ticks tick actor engine request observed) :
    family resources.current.handle.object = none := by
  obtain ⟨handle, live, publicObject, parsed⟩ := Lowered.source_start_history_public descriptors lifetimes lookup cwdLookup
    journal selected present shape count prefixLabels.family resources.source.source.source.target
    resources.starting.rawBefore.length resources.starting.actual resources.startingLimit
  have sameBase : resources.base.handle = handle := Option.some.inj (resources.base.live.symm.trans live)
  have initialPublic : family resources.inspected.handle.object = none := by
    rw [resources.sameBase, sameBase]
    exact publicObject
  have names : ∀ component ∈ resources.visited,
      Directories.component component = true ∧ PrivateNames.reservedBytes component = false := by
    intro component member
    have inDrop : component ∈ resources.source.cursor.selected.parts.dropLast := by
      rw [resources.parts]
      exact List.mem_append.mpr (.inl member)
    exact source_components_are_components resources.source.source.source.target resources.source.cursor.selected.parts
      parsed component (List.dropLast_subset _ inDrop)
  have recorded := recorded_history_source_bound resources.walked.2 engine.events.length resources.walkLimit
  have opens := actual_public_directory_opens descriptors aliases lifetimes lookup journal selected present shape count prefixLabels
  obtain ⟨current, currentLive, currentPublic⟩ := Lowered.directory_descend_public descriptors opens resources.walkOrdinal
    resources.source.cursor.identity.1.toNat true resources.source.cursor.base resources.visited resources.inspected.handle
    ⟨resources.walked.1, recorded⟩ resources.inspected.live initialPublic names
  have same : current = resources.current.handle := Option.some.inj (currentLive.symm.trans resources.currentAtWalk)
  simpa only [same] using currentPublic

end LeanCage.Host.Kernel
