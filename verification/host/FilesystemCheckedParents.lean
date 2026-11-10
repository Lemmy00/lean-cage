import FilesystemParentState
import FilesystemProbeBounds
import FilesystemLoweredParentObservations

namespace LeanCage.Host.Kernel
open Filesystem

structure CheckedParentInterval {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (process : ProcessContract runtime) (child : ChildPrimitive kernel) (native : NativePrimitive kernel)
    (hostUid : Nat) (initial : World) (ticks : List (ActorTick runtime)) (tick : ActorTick runtime)
    (actor : ActorId) (engine : EngineState) (fd : UInt64) where
  parent : Handle
  reference : engine.references fd = some parent
  raw : parent.rawOwned = true
  sampledInformation : Stat
  sample : StatSample kernel (fun ordinal request reply => SourceReturnAt runtime ticks actor ordinal Reply
    (.filesystem request) reply) fd parent sampledInformation
  samplePosition : Nat
  sampleTick : ActorTick runtime
  sampleAt : ticks[samplePosition]? = some sampleTick
  sampleEngine : EngineState
  samplePresent : sampleTick.before.actors actor = some sampleEngine
  sampleCount : sampleEngine.events.length = sample.ordinal
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

-- §FS-host-boundary.ownership: One genuine source fstat and the actual current same OFD
-- produce this interval; no helper/current-authority/closed callback-frame input is accepted.
theorem checked_parent_interval_owned {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (raw : RawReferenceLifetimeContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {prior last : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid prior callers ticks last next)
    {backend : NativeAuthorityJournal recording}
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    (selected : ticks[position]? = some tick) (present : tick.before.actors actor = some engine)
    {limit : Nat} {world : World} {directory : Directories.Opened}
    (observed : ObservedDirectory kernel (fun ordinal request reply =>
      SourceReturnAt runtime ticks actor ordinal Reply (.filesystem request) reply) limit world hostUid directory)
    (live : engine.references directory.fd = some observed.handle)
    (earlier : observed.sample.ordinal < engine.events.length) :
    ∃ interval : CheckedParentInterval process child native hostUid initial ticks tick actor engine directory.fd,
      interval.parent = observed.handle ∧ interval.sample.ordinal = observed.sample.ordinal := by
  let sample := observed.sample
  obtain ⟨samplePosition, sampleTick, sampleEngine, afterEngine, sampleAt, sampleAction,
    samplePresent, afterPresent, count, beforeShape, afterShape⟩ := sample.sampled
  have currentCount : sampleEngine.events.length < engine.events.length := count ▸ earlier
  have ordered := source_ordinal_orders_positions journal sampleAt selected actor sampleEngine engine
    samplePresent present currentCount
  obtain ⟨leading, inside, trailing, shape, leadingCount, limitCount, interval⟩ :=
    journal_between_after_counted journal sampleAt selected ordered
  have statOperation : ActorStep runtime
      (.returned actor (.filesystem {op := .stat, first := directory.fd}) sample.reply)
      sampleTick.before sampleTick.after := sampleAction ▸ sampleTick.operation
  have eventTrace := returned_action_events statOperation samplePresent afterPresent
  have afterLive : sample.after.handles directory.fd = some observed.handle := by
    rw [descriptors.retained _ _ _ _ sample.actual (by simp [RetainsDescriptors])]
    exact sample.live
  have afterReferences : afterEngine.references directory.fd = some observed.handle := by
    simpa only [afterShape, Population.project] using afterLive
  let lease : ActiveParentLease runtime ticks sampleTick.after hostUid observed.handle.object := {
    actor, engine := afterEngine, descriptor := directory.fd, handle := observed.handle
    present := afterPresent, live := afterReferences, identity := rfl, ordinal := sample.ordinal
    before := sample.before, after := sample.after, reply := sample.reply
    information := directory.information, sampled := sample.sampled, held := sample.live
    parsed := sample.parsed, trusted := observed.trusted, earlier := by
      rw [eventTrace, List.length_append, List.length_singleton, count]
      omega }
  have statMember : sampleTick ∈ ticks := List.mem_iff_getElem.mpr
    ⟨samplePosition, (List.getElem?_eq_some_iff.mp sampleAt).1, (List.getElem?_eq_some_iff.mp sampleAt).2⟩
  have consistent := (actor_journal_consistent descriptors lifetimes references journal
    (empty_population_consistent initial)).2 sampleTick statMember
  have beforeReferences : sampleEngine.references directory.fd = some observed.handle := by
    simpa only [beforeShape, Population.project] using sample.live
  have oldBefore : sampleTick.before.shared.descriptionAllocated observed.handle.description = true :=
    (consistent.1 actor sampleEngine samplePresent directory.fd observed.handle beforeReferences).2.1
  have oldAfter := actor_step_description_allocated references sampleTick.operation observed.handle.description oldBefore
  have objectBefore : sampleTick.before.shared.allocated observed.handle.object = true :=
    (consistent.1 actor sampleEngine samplePresent directory.fd observed.handle beforeReferences).1
  have objectAfter := actor_step_allocated lifetimes sampleTick.operation observed.handle.object objectBefore
  have leases := active_parent_lease_snapshots raw sdk references interval lease present live oldAfter
  have retained : AuthorityRetained sample.after observed.handle.object :=
    .inl (.inl ⟨directory.fd, observed.handle, afterLive, rfl⟩)
  have initialKnown := descriptors.stat_actual _ _ _ _ _ _ sample.actual rfl sample.live sample.parsed
  obtain ⟨afterInformation, knownAfter, firstSame⟩ := accounts.authority_existing _ _ _ _ _ _ sample.actual
    (by intro setting; cases setting) initialKnown retained
  have actualKnown : sampleTick.after.shared.information observed.handle.object = some afterInformation := by
    simpa only [afterShape, Population.project] using knownAfter
  have afterTrusted : Directories.trusted hostUid afterInformation = true :=
    (same_authority_trusted hostUid firstSame).trans observed.trusted
  have owner : afterInformation.uid = hostUid ∨ afterInformation.uid = 0 := by
    have fields : afterInformation.directory = true ∧ (afterInformation.uid = hostUid ∨ afterInformation.uid = 0) ∧
        (afterInformation.mode &&& 18 = 0 ∨ (afterInformation.uid = 0 ∧ afterInformation.mode &&& 512 ≠ 0)) := by
      simpa [Directories.trusted, and_assoc] using afterTrusted
    exact fields.2.1
  have safe := backend
  have arranged : ∃ actual : NativeExternalJournal process child native hostUid prior callers ticks last next,
      NativeAuthorityJournal actual := ⟨recording, safe⟩
  rw [shape, List.append_assoc] at arranged
  obtain ⟨actual, actualSafe⟩ := arranged
  obtain ⟨atSample, nativeAtSample, first, rest, firstSafe, restSafe⟩ := native_safe_split leading _ actual actualSafe
  cases rest with
  | cons sampled remaining =>
    obtain ⟨atEnd, nativeAtEnd, region, following, regionSafe, followingSafe⟩ :=
      native_safe_split inside _ remaining restSafe.2
    have included : ∀ current ∈ inside, current ∈ ticks := by intro current member; simp [shape, member]
    have held : ∀ current ∈ inside, GloballyHeld current.after observed.handle.object := by
      intro current member
      obtain ⟨heldLease⟩ := (leases current member).2
      exact .inl ⟨heldLease.actor, heldLease.engine, heldLease.descriptor, heldLease.handle,
        heldLease.present, heldLease.live, heldLease.identity⟩
    exact ⟨{
      parent := observed.handle
      reference := live
      raw := observed.raw
      sampledInformation := directory.information
      sample
      samplePosition
      sampleTick
      sampleAt
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
      leases := fun current member => (leases current member).1 }, rfl, rfl⟩

-- §AR-host-boundary.interfaces: Preserve the original existence interface. Dependent users
-- consume the sibling above, which retains the SAME sampled handle and ordinal explicitly.
theorem checked_parent_interval {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (raw : RawReferenceLifetimeContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {prior last : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid prior callers ticks last next)
    {backend : NativeAuthorityJournal recording}
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    (selected : ticks[position]? = some tick) (present : tick.before.actors actor = some engine)
    {limit : Nat} {world : World} {directory : Directories.Opened}
    (observed : ObservedDirectory kernel (fun ordinal request reply =>
      SourceReturnAt runtime ticks actor ordinal Reply (.filesystem request) reply) limit world hostUid directory)
    (live : engine.references directory.fd = some observed.handle)
    (earlier : observed.sample.ordinal < engine.events.length) :
    Nonempty (CheckedParentInterval process child native hostUid initial ticks tick actor engine directory.fd) := by
  obtain ⟨interval, parent, ordinal⟩ := checked_parent_interval_owned (backend := backend) descriptors lifetimes references raw sdk accounts
    journal recording selected present observed live earlier
  exact ⟨interval⟩

theorem CheckedParentInterval.inside_selected {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {fd : UInt64}
    (interval : CheckedParentInterval process child native hostUid initial ticks tick actor engine fd)
    {position : Nat} {current : ActorTick runtime} (selected : ticks[position]? = some current)
    (afterStart : interval.samplePosition < position) (beforeLimit : position < interval.position) :
    current ∈ interval.events := by
  have trace : ticks = (interval.leading ++ [interval.sampleTick]) ++ (interval.events ++ tick :: interval.trailing) := by
    simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using interval.trace
  have lower : (interval.leading ++ [interval.sampleTick]).length ≤ position := by
    simp only [List.length_append, List.length_singleton]
    have count := interval.leadingCount
    omega
  have bounded : position - (interval.leading ++ [interval.sampleTick]).length < interval.events.length := by
    simp only [List.length_append, List.length_singleton]
    have first := interval.leadingCount
    have last := interval.limitCount
    omega
  have occurs : interval.events[position - (interval.leading ++ [interval.sampleTick]).length]? = some current := by
    have same : ((interval.leading ++ [interval.sampleTick]) ++ (interval.events ++ tick :: interval.trailing))[position]? =
        some current := trace ▸ selected
    rw [List.getElem?_append_right lower, List.getElem?_append_left bounded] at same
    exact same
  exact List.mem_iff_getElem.mpr ⟨_, bounded, (List.getElem?_eq_some_iff.mp occurs).2⟩

-- §FS-host-boundary.lookup: A second FD may alias the checked parent. The actual namespace
-- operand probe is joined by object identity, while the retained original OFD supplies custody.
theorem checked_parent_comparison {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    (lifetimes : LifetimeContract runtime) (metadata : GlobalAuthorityContract runtime child)
    (nativeMetadata : NativeMetadataContract native) (lookup : LookupMutationContract (runtime := runtime) child native)
    (probes : LookupPrimitiveContract kernel.step kernel.interference semantics)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (authorityProfile : NativeAuthorityProfile native ticks hostUid) (lookupProfile : NativeLookupProfile native ticks hostUid)
    {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {fd : UInt64}
    (interval : CheckedParentInterval process child native hostUid initial ticks tick actor engine fd)
    {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed)
    (kind : NamespaceRequest request) (guardFd : UInt64) (member : guardFd ∈ Lookup.parents request)
    (operand : Handle) (reference : engine.references guardFd = some operand)
    (identity : operand.object = interval.parent.object)
    (earlier : interval.sample.ordinal < adapter.occurrence.rawBefore.length) :
    ∃ information, tick.before.shared.information interval.parent.object = some information ∧
      Directories.trusted hostUid information = true ∧ (semantics.at tick.before.shared interval.parent.object).byteExact := by
  obtain ⟨⟨information, known, authority, currentBits⟩, snapshots⟩ := native_parent_state_snapshots lifetimes metadata
    nativeMetadata lookup authorityProfile lookupProfile interval.journal interval.included interval.recording interval.safe
    interval.known interval.owner interval.old interval.held interval.leases
  obtain ⟨bounded⟩ := primitive_adapter_parent_probes_bounded adapter probes kind guardFd member operand reference
  obtain ⟨probePosition, probeTick, probeEngine, probeAt, probePresent, probeCount, probeWorld⟩ :=
    checked_directory_global_sample bounded.checked
  have afterStat : interval.sampleEngine.events.length < probeEngine.events.length := by
    rw [interval.sampleCount, probeCount]
    exact Nat.lt_of_lt_of_le earlier bounded.lower
  have beforeCall : probeEngine.events.length < engine.events.length := by rw [probeCount]; exact bounded.upper
  have afterStart := source_ordinal_orders_positions journal interval.sampleAt probeAt actor interval.sampleEngine
    probeEngine interval.samplePresent probePresent afterStat
  have beforeLimit := source_ordinal_orders_positions journal probeAt interval.selected actor probeEngine engine
    probePresent interval.present beforeCall
  have inside := interval.inside_selected probeAt afterStart beforeLimit
  have probeBits := (snapshots probeTick inside).1
  have same : LookupBitsEqual bounded.checked.observedAt tick.before.shared interval.parent.object := by
    have physical : LookupBitsEqual probeTick.before.shared tick.before.shared interval.parent.object :=
      currentBits.trans probeBits.symm
    simpa only [LookupBitsEqual, probeWorld, Population.project] using physical
  have names : (semantics.at bounded.checked.observedAt interval.parent.object).byteExact := by
    rw [← identity]
    exact checked_directory_observed_exact bounded.checked
  exact ⟨information, known, (same_authority_trusted hostUid authority).trans interval.trusted,
    byte_exact_after_lookup_bits names same⟩

end LeanCage.Host.Kernel
