import FilesystemPrimitiveParents
import FilesystemPrimitiveIntervals
import FilesystemParentLeases
import FilesystemNativeAuthority

namespace LeanCage.Host.Kernel
open Filesystem

structure PrimitiveParentInterval {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (process : ProcessContract runtime) (child : ChildPrimitive kernel) (native : NativePrimitive kernel)
    (hostUid : Nat) (initial : World) (ticks : List (ActorTick runtime)) (tick : ActorTick runtime)
    (actor : ActorId) (engine : EngineState) (request : Request) where
  source : PrimitiveRunParent runtime initial ticks tick actor engine request
  parent : Handle
  reference : engine.references request.first = some parent
  raw : parent.rawOwned = true
  samplePosition : Nat
  sampleTick : ActorTick runtime
  sampleAt : ticks[samplePosition]? = some sampleTick
  sampleAction : sampleTick.action = .returned actor
    (.filesystem {op := .stat, first := source.container.fd}) source.statReply
  sampleEngine : EngineState
  samplePresent : sampleTick.before.actors actor = some sampleEngine
  sampleCount : sampleEngine.events.length = source.inspected.rawBefore.length
  position : Nat
  selected : ticks[position]? = some tick
  present : tick.before.actors actor = some engine
  leading : List (ActorTick runtime)
  events : List (ActorTick runtime)
  trailing : List (ActorTick runtime)
  trace : ticks = leading ++ sampleTick :: events ++ tick :: trailing
  leadingCount : leading.length = samplePosition
  limitCount : leading.length + 1 + events.length = position
  journal : ActorJournal runtime sampleTick.after events tick.before
  beforeProcesses : Processes
  afterProcesses : Processes
  beforeNative : NativeProcesses
  afterNative : NativeProcesses
  recording : NativeExternalJournal process child native hostUid beforeProcesses beforeNative events afterProcesses afterNative
  safe : NativeAuthorityJournal recording
  information : Stat
  known : sampleTick.after.shared.information parent.object = some information
  trusted : Directories.trusted hostUid information = true
  owner : information.uid = hostUid ∨ information.uid = 0
  old : sampleTick.after.shared.allocated parent.object = true
  included : ∀ current ∈ events, current ∈ ticks
  held : ∀ current ∈ events, GloballyHeld current.after parent.object
  leases : ∀ current ∈ events, Nonempty (ActiveParentLease runtime ticks current.before hostUid parent.object)

-- §FS-host-boundary.ownership: Current authority is derived from the actual checked open/stat,
-- every intervening source/native/child operation, and the same retained parent reference.
theorem primitive_run_parent_interval {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (raw : RawReferenceLifetimeContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (backend : PrimitiveChildAuthorityProducer child ticks)
    {prior last : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid prior callers ticks last next)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request}
    (selected : ticks[position]? = some tick) (present : tick.before.actors actor = some engine)
    (source : PrimitiveRunParent runtime initial ticks tick actor engine request) :
    Nonempty (PrimitiveParentInterval process child native hostUid initial ticks tick actor engine request) := by
  obtain ⟨parent, currentLive, rawParent⟩ := primitive_run_parent_reference descriptors source
  obtain ⟨atStat, initialKnown, initialTrusted⟩ :=
    primitive_run_parent_observed descriptors accounts source currentLive
  let sample := source.inspected
  obtain ⟨samplePosition, sampleTick, sampleEngine, afterEngine, sampleAt, sampleAction,
    samplePresent, afterPresent, count, beforeShape, afterShape⟩ := sample.sampled
  have currentCount : sampleEngine.events.length < engine.events.length := by
    have trace := sample.trace
    have length := congrArg List.length trace
    simp only [List.length_append, List.length_cons] at length
    omega
  have ordered := source_ordinal_orders_positions journal sampleAt selected actor sampleEngine engine
    samplePresent present currentCount
  obtain ⟨leading, inside, trailing, shape, leadingCount, limitCount, interval⟩ :=
    journal_between_after_counted journal sampleAt selected ordered
  have statOperation : ActorStep runtime
      (.returned actor (.filesystem {op := .stat, first := source.container.fd}) source.statReply)
      sampleTick.before sampleTick.after := sampleAction ▸ sampleTick.operation
  have eventTrace := returned_action_events statOperation samplePresent afterPresent
  have afterLive : sample.after.handles source.container.fd = some parent := by
    rw [descriptors.retained _ _ _ _ sample.actual (by simp [RetainsDescriptors])]
    exact atStat
  have afterReferences : afterEngine.references source.container.fd = some parent := by
    simpa only [afterShape, Population.project] using afterLive
  let lease : ActiveParentLease runtime ticks sampleTick.after hostUid parent.object := {
    actor, engine := afterEngine, descriptor := source.container.fd, handle := parent
    present := afterPresent, live := afterReferences, identity := rfl, ordinal := sample.rawBefore.length
    before := sample.before, after := sample.after, reply := source.statReply
    information := source.container.information, sampled := sample.sampled, held := atStat
    parsed := source.parsed, trusted := initialTrusted, earlier := by
      rw [eventTrace, List.length_append, List.length_singleton, count]
      omega }
  have statMember : sampleTick ∈ ticks := List.mem_iff_getElem.mpr
    ⟨samplePosition, (List.getElem?_eq_some_iff.mp sampleAt).1, (List.getElem?_eq_some_iff.mp sampleAt).2⟩
  have consistent := (actor_journal_consistent descriptors lifetimes references journal
    (empty_population_consistent initial)).2 sampleTick statMember
  have beforeReferences : sampleEngine.references source.container.fd = some parent := by
    have atSample : sample.before.handles source.container.fd = some parent := atStat
    simpa only [beforeShape, Population.project] using atSample
  have oldBefore : sampleTick.before.shared.descriptionAllocated parent.description = true :=
    (consistent.1 actor sampleEngine samplePresent source.container.fd parent beforeReferences).2.1
  have oldAfter := actor_step_description_allocated references sampleTick.operation parent.description oldBefore
  have objectBefore : sampleTick.before.shared.allocated parent.object = true :=
    (consistent.1 actor sampleEngine samplePresent source.container.fd parent beforeReferences).1
  have objectAfter := actor_step_allocated lifetimes sampleTick.operation parent.object objectBefore
  have endReferences : engine.references source.container.fd = some parent := by
    simpa only [source.parentArgument] using currentLive
  have leases := active_parent_lease_snapshots raw sdk references interval lease present endReferences oldAfter
  have retained : AuthorityRetained sample.after parent.object := .inl (.inl ⟨source.container.fd, parent, afterLive, rfl⟩)
  obtain ⟨afterInformation, knownAfter, firstSame⟩ := accounts.authority_existing _ _ _ _ _ _ sample.actual
    (by intro setting; cases setting) initialKnown retained
  have actualKnown : sampleTick.after.shared.information parent.object = some afterInformation := by
    simpa only [afterShape, Population.project] using knownAfter
  have afterTrusted : Directories.trusted hostUid afterInformation = true :=
    (same_authority_trusted hostUid firstSame).trans initialTrusted
  have owner : afterInformation.uid = hostUid ∨ afterInformation.uid = 0 := by
    have fields : afterInformation.directory = true ∧ (afterInformation.uid = hostUid ∨ afterInformation.uid = 0) ∧
        (afterInformation.mode &&& 18 = 0 ∨ (afterInformation.uid = 0 ∧ afterInformation.mode &&& 512 ≠ 0)) := by
      simpa [Directories.trusted, and_assoc] using afterTrusted
    exact fields.2.1
  have safe := actual_native_authority_journal journal backend recording
  have arranged : ∃ actual : NativeExternalJournal process child native hostUid prior callers ticks last next,
      NativeAuthorityJournal actual := ⟨recording, safe⟩
  rw [shape, List.append_assoc] at arranged
  obtain ⟨actual, actualSafe⟩ := arranged
  obtain ⟨atSample, nativeAtSample, first, rest, firstSafe, restSafe⟩ := native_safe_split leading _ actual actualSafe
  cases rest with
  | cons sampled remaining =>
    obtain ⟨atEnd, nativeAtEnd, region, following, regionSafe, followingSafe⟩ :=
      native_safe_split inside _ remaining restSafe.2
    have included : ∀ current ∈ inside, current ∈ ticks := by
      intro current member
      simp [shape, member]
    have held : ∀ current ∈ inside, GloballyHeld current.after parent.object := by
      intro current member
      obtain ⟨heldLease⟩ := (leases current member).2
      exact .inl ⟨heldLease.actor, heldLease.engine, heldLease.descriptor, heldLease.handle,
        heldLease.present, heldLease.live, heldLease.identity⟩
    exact ⟨{
      source
      parent
      reference := currentLive
      raw := rawParent
      samplePosition
      sampleTick
      sampleAt
      sampleAction
      sampleEngine
      samplePresent
      sampleCount := count
      position
      selected
      present
      leading
      events := inside
      trailing
      trace := shape
      leadingCount
      limitCount
      journal := interval
      beforeProcesses := _
      afterProcesses := _
      beforeNative := _
      afterNative := _
      recording := region
      safe := regionSafe
      information := afterInformation
      known := actualKnown
      trusted := afterTrusted
      owner
      old := objectAfter
      included
      held
      leases := fun current member => (leases current member).1 }⟩

theorem primitive_run_parent_current {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (raw : RawReferenceLifetimeContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (metadata : GlobalAuthorityContract runtime child) (nativeMetadata : NativeMetadataContract native)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (backend : PrimitiveChildAuthorityProducer child ticks)
    (profile : NativeAuthorityProfile native ticks hostUid)
    {prior last : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid prior callers ticks last next)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request}
    (selected : ticks[position]? = some tick) (present : tick.before.actors actor = some engine)
    (source : PrimitiveRunParent runtime initial ticks tick actor engine request) :
    ∃ parent information, engine.references request.first = some parent ∧ parent.rawOwned = true ∧
      tick.before.shared.information parent.object = some information ∧
      Directories.trusted hostUid information = true := by
  obtain ⟨interval⟩ := primitive_run_parent_interval descriptors lifetimes references raw sdk accounts journal backend
    recording selected present source
  obtain ⟨information, known, same⟩ := native_parent_authority_interval metadata nativeMetadata profile interval.journal
    interval.included interval.recording interval.safe interval.known interval.owner interval.held interval.leases
  exact ⟨interval.parent, information, interval.reference, interval.raw, known,
    (same_authority_trusted hostUid same).trans interval.trusted⟩

end LeanCage.Host.Kernel
