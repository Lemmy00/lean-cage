import FilesystemRunCustody
import FilesystemRemovalCustody
import FilesystemCheckedParents

namespace LeanCage.Host.Kernel
open Filesystem

private theorem cleanup_directory_reference {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {actor : ActorId} {events outside : List Program.Event}
    {created : List (Request × Reply)} {run : RunDirectory.Owned} {work : List Program.Event}
    {inside : List (Request × Option Reply)} {request : Request} {guardOrdinal limit : Nat} {current : World}
    (source : RunCleanupParent runtime initial all actor events outside created run work inside request guardOrdinal limit current)
    (inner : request.first = run.directory.fd) :
    current.handles run.directory.fd = some source.allocation.earlier.source.opening.handle := by
  rcases source.origin with child | root
  · have live := source.reference
    exact Eq.mp (congrArg (fun fd => current.handles fd = some source.allocation.earlier.source.opening.handle) inner)
      (child.2 ▸ live)
  · have impossible := source.point.distinct (inner.symm.trans root.1)
    exact False.elim impossible

-- §FS-host-boundary.lookup: The selected inner cleanup's current comparison
-- comes from this run's real euid/fstat, actual retained OFD and SAME raw
-- namespace guard. A private-directory label never substitutes for the probe.
theorem actual_run_inner_unlink_comparison {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {semantics : NameSemanticsView}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (raw : RawReferenceLifetimeContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (metadata : GlobalAuthorityContract runtime child) (nativeMetadata : NativeMetadataContract native)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    (probes : LookupPrimitiveContract kernel.step kernel.interference semantics)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    (authorityProfile : NativeAuthorityProfile native all hostUid) (lookupProfile : NativeLookupProfile native all hostUid)
    {before after : Processes} {first last : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid before first all after last)
    {backend : NativeAuthorityJournal recording}
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} (present : tick.before.actors actor = some engine)
    {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {outside : List Program.Event} {created : List (Request × Reply)} {run : RunDirectory.Owned}
    {work : List Program.Event} {inside : List (Request × Option Reply)}
    (source : RunCleanupParent runtime initial all actor engine.events outside created run work inside request
      adapter.occurrence.rawBefore.length position (tick.before.project engine))
    (inner : request.first = run.directory.fd) (unlink : request.op = .unlinkAt) :
    (semantics.at tick.before.shared source.allocation.earlier.source.opening.handle.object).byteExact := by
  obtain ⟨identity⟩ := source.allocation.uid_sample
  have uid := sampled_uid_is_host accounts identity
  let original := source.point.observation
  let observation : ObservedDirectory kernel (fun ordinal request reply =>
      SourceReturnAt runtime all actor ordinal Reply (.filesystem request) reply)
      (source.allocation.earlier.source.input.events.length + 1 +
        (source.allocation.earlier.post.map Program.filesystemEvent).length + source.point.createdAfter.length)
      source.point.world hostUid run.directory := {
    handle := original.handle
    live := original.live
    raw := original.raw
    sample := {
      ordinal := original.sample.ordinal
      before := original.sample.before
      after := original.sample.after
      reply := original.sample.reply
      actual := original.sample.actual
      sampled := Eq.mp (congrArg (fun who => SourceReturnAt runtime all who original.sample.ordinal Reply
        (.filesystem {op := .stat, first := run.directory.fd}) original.sample.reply original.sample.before
        original.sample.after) source.sameActor) original.sample.sampled
      live := original.sample.live
      parsed := original.sample.parsed }
    earlier := original.earlier
    trusted := uid ▸ original.trusted }
  have live : engine.references run.directory.fd = some observation.handle := by
    rw [source.point.sameObserved]
    exact cleanup_directory_reference source inner
  have earlier : observation.sample.ordinal < engine.events.length := by
    have beforeGuard := source.statBeforeGuard
    have count := congrArg List.length adapter.occurrence.trace
    simp only [List.length_append, List.length_map] at count
    change source.point.observation.sample.ordinal < engine.events.length
    omega
  obtain ⟨interval, sameHandle, sameOrdinal⟩ := checked_parent_interval_owned (backend := backend) descriptors lifetimes
    references raw sdk accounts journal recording selected present observation live earlier
  have parentLive : engine.references request.first = some source.allocation.earlier.source.opening.handle := by
    rw [inner]
    exact cleanup_directory_reference source inner
  have parent : interval.parent = source.allocation.earlier.source.opening.handle :=
    sameHandle.trans source.point.sameObserved
  have member : request.first ∈ Lookup.parents request := by simp only [Lookup.parents, unlink, List.mem_singleton]
  obtain ⟨information, known, trusted, names⟩ := checked_parent_comparison lifetimes metadata nativeMetadata lookup probes
    journal authorityProfile lookupProfile interval adapter (.inr (.inr (.inl unlink))) request.first member
    source.allocation.earlier.source.opening.handle parentLive (by rw [parent]) (by
      rw [sameOrdinal]
      exact source.statBeforeGuard)
  simpa only [parent] using names

-- §FS-host-boundary.ownership: The real inner unlink's directory is the
-- SAME currently private recorded root; all actual descendants share its
-- source owner. This advances the cumulative publication state on error/loss.
theorem actual_run_inner_unlink_publication {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (frames : ByteNamespaceFrameContract kernel semantics)
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (raw : RawReferenceLifetimeContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (authority : GlobalAuthorityContract runtime child) (nativeMetadata : NativeMetadataContract native)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    (probes : LookupPrimitiveContract kernel.step kernel.interference semantics)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (mounts : MountContract kernel initial.allocated)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    (authorityProfile : NativeAuthorityProfile native all hostUid) (lookupProfile : NativeLookupProfile native all hostUid)
    {before after : Processes} {first last : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid before first all after last)
    {backend : NativeAuthorityJournal recording}
    {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {foreignReferences : ForeignReferences} {nativeCurrent : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before nativeCurrent)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ tick :: trailing)
    {outside : List Program.Event} {created : List (Request × Reply)} {run : RunDirectory.Owned}
    {work : List Program.Event} {inside : List (Request × Option Reply)}
    (source : RunCleanupParent runtime initial all actor engine.events outside created run work inside request
      adapter.occurrence.rawBefore.length processed.length (tick.before.project engine))
    (inner : request.first = run.directory.fd) (unlink : request.op = .unlinkAt) :
    Nonempty (RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after nativeCurrent) := by
  have selected : all[processed.length]? = some tick := by
    rw [whole, List.getElem?_append_right (by omega)]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  obtain ⟨root⟩ := actual_run_cleanup_root descriptors lifetimes mounts journal prior whole present source
  have live : engine.references request.first = some source.allocation.earlier.source.opening.handle := by
    rw [inner]
    exact cleanup_directory_reference source inner
  have names := actual_run_inner_unlink_comparison (backend := backend) descriptors lifetimes references raw sdk accounts
    authority nativeMetadata lookup probes journal authorityProfile lookupProfile recording selected present adapter source inner unlink
  have actual := selected_filesystem_step tick action present
  have change : DataChange dataObjects request (tick.before.project engine) tick.after.shared := by
    apply namespaceLaws.mutation _ _ _ _ actual (.inr (.inl unlink))
    · simpa only [ComponentRequest, unlink] using source.component
    · simp only [DirectoryOperands, unlink]
      change ∃ parent : Handle, engine.references request.first = some parent
      exact ⟨source.allocation.earlier.source.opening.handle, live⟩
    · intro fd member handle current
      have sameFd : fd = request.first := by simpa only [Lookup.parents, unlink, List.mem_singleton] using member
      subst fd
      have same := Option.some.inj (current.symm.trans live)
      subst handle
      exact names
  apply private_parent_unlink_registered_publication frames descriptors lifetimes references sdk accounts objects metadata
    lookup journal selected action present unlink live source.component names change prior
  rw [root.directory]
  exact root.privateRoot

end LeanCage.Host.Kernel
