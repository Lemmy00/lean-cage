import FilesystemParentState
import FilesystemProbeBounds

namespace LeanCage.Host.Kernel
open Filesystem

theorem PrimitiveParentInterval.inside_selected {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request}
    (interval : PrimitiveParentInterval process child native hostUid initial ticks tick actor engine request)
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

-- §FS-host-boundary.lookup: This uses the accepted probe in this same raw guard, its genuine
-- global position, and source-produced active-parent effects through the selected mkdir.
theorem parent_interval_state_comparison {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    (lifetimes : LifetimeContract runtime) (metadata : GlobalAuthorityContract runtime child)
    (nativeMetadata : NativeMetadataContract native) (lookup : LookupMutationContract (runtime := runtime) child native)
    (probes : LookupPrimitiveContract kernel.step kernel.interference semantics)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (authorityProfile : NativeAuthorityProfile native ticks hostUid) (lookupProfile : NativeLookupProfile native ticks hostUid)
    {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request}
    (interval : PrimitiveParentInterval process child native hostUid initial ticks tick actor engine request) :
    ∃ information, tick.before.shared.information interval.parent.object = some information ∧
      Directories.trusted hostUid information = true ∧ (semantics.at tick.before.shared interval.parent.object).byteExact := by
  obtain ⟨⟨information, known, authority, currentBits⟩, snapshots⟩ := native_parent_state_snapshots lifetimes metadata
    nativeMetadata lookup authorityProfile lookupProfile interval.journal interval.included interval.recording interval.safe
    interval.known interval.owner interval.old interval.held interval.leases
  have kind : NamespaceRequest request := .inr (.inl interval.source.mkdir)
  have member : request.first ∈ Lookup.parents request := by simp only [Lookup.parents, interval.source.mkdir, List.mem_singleton]
  obtain ⟨bounded⟩ := primitive_adapter_parent_probes_bounded interval.source.adapter probes kind request.first member
    interval.parent interval.reference
  obtain ⟨probePosition, probeTick, probeEngine, probeAt, probePresent, probeCount, probeWorld⟩ :=
    checked_directory_global_sample bounded.checked
  have afterStat : interval.sampleEngine.events.length < probeEngine.events.length := by
    rw [interval.sampleCount, probeCount]
    exact Nat.lt_of_lt_of_le interval.source.statBeforeGuard bounded.lower
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
  exact ⟨information, known, (same_authority_trusted hostUid authority).trans interval.trusted,
    byte_exact_after_lookup_bits (checked_directory_observed_exact bounded.checked) same⟩

theorem primitive_run_mkdir_safe_parent {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (raw : RawReferenceLifetimeContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (metadata : GlobalAuthorityContract runtime child) (nativeMetadata : NativeMetadataContract native)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    (probes : LookupPrimitiveContract kernel.step kernel.interference semantics)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (backend : PrimitiveChildAuthorityProducer child ticks)
    (authorityProfile : NativeAuthorityProfile native ticks hostUid) (lookupProfile : NativeLookupProfile native ticks hostUid)
    {prior last : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid prior callers ticks last next)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request}
    (selected : ticks[position]? = some tick) (present : tick.before.actors actor = some engine)
    (source : PrimitiveRunParent runtime initial ticks tick actor engine request) :
    ∃ parent information, engine.references request.first = some parent ∧ parent.rawOwned = true ∧
      tick.before.shared.information parent.object = some information ∧ Directories.trusted hostUid information = true ∧
      (semantics.at tick.before.shared parent.object).byteExact ∧ request.op = .mkdirAt ∧ request.second = 448 ∧
      Directories.component request.left = true ∧ PrivateNames.reservedBytes request.left = true := by
  obtain ⟨interval⟩ := primitive_run_parent_interval descriptors lifetimes references raw sdk accounts journal backend
    recording selected present source
  obtain ⟨information, known, trusted, exactNames⟩ := parent_interval_state_comparison lifetimes metadata nativeMetadata lookup
    probes journal authorityProfile lookupProfile interval
  exact ⟨interval.parent, information, interval.reference, interval.raw, known, trusted, exactNames,
    source.mkdir, source.privateMode, source.component, source.reserved⟩

end LeanCage.Host.Kernel
