import FilesystemRunBoundary
import FilesystemRunUnlink

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: Retain the SAME actual deletion certificate
-- when advancing both the publication state and its joint prefix history.
theorem owned_unlink_publication_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (frames : ByteNamespaceFrameContract kernel semantics) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} {parent : Handle}
    (selected : all[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (unlink : request.op = .unlinkAt)
    (live : engine.references request.first = some parent)
    (component : Directories.component request.left = true)
    (comparison : (semantics.at tick.before.shared parent.object).byteExact)
    (change : DataChange dataObjects request (tick.before.project engine) tick.after.shared)
    {foreignReferences : ForeignReferences} {currentNative : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    (joint : JointPublicationPrefix prior)
    (authorized : ∀ object scope, tick.before.shared.entries parent.object request.left = some object →
      prior.custody.current.source.custody.caps.family object = some scope →
      prior.custody.current.source.custody.catalogue.Owns actor scope) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
        foreignReferences (processed ++ [tick]) tick.after currentNative,
      next.custody.current.source.custody.catalogue = prior.custody.current.source.custody.catalogue ∧
      next.custody.current.source.custody.caps.family = prior.custody.current.source.custody.caps.family ∧
      JointPublicationPrefix next := by
  obtain ⟨custody, catalogue, labels, ownership⟩ := owned_unlink_registered_custody_with_step frames descriptors
    lifetimes references sdk accounts objects metadata lookup journal selected action present unlink live component
    comparison (by intro parent name object bound; exact unlink_delta_deletes change unlink parent name object bound)
    prior.custody authorized
  let next := prior.preserved custody catalogue (by intro object allocated; rw [labels])
  refine ⟨next, catalogue, labels, joint.advance next ?_ ?_⟩
  · change ∀ record ∈ prior.custody.current.source.custody.catalogue, record ∈ custody.current.source.custody.catalogue
    rw [catalogue]
    exact fun _ member => member
  · refine ⟨ownership, ?_⟩
    change ExistingLabels tick.before.shared tick.after.shared prior.custody.current.source.custody.caps.family
      custody.current.source.custody.caps.family
    rw [labels]
    exact unchanged_existing_labels _ _ _

private theorem outer_cleanup_name {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {actor : ActorId} {events outside : List Program.Event}
    {created : List (Request × Reply)} {run : RunDirectory.Owned} {work : List Program.Event}
    {inside : List (Request × Option Reply)} {request : Request} {guardOrdinal limit : Nat} {current : World}
    (source : RunCleanupParent runtime initial all actor events outside created run work inside request guardOrdinal limit current)
    (outer : request.first = run.container.fd) (unlink : request.op = .unlinkAt) : request.left = run.name := by
  have role := RunDirectory.cleanup_request_prefix run source.cleanupSource (request, none) (by simp)
  simp only [RunDirectory.CleanupRequest, unlink] at role
  rcases role with inner | root
  · exact False.elim (source.point.distinct (inner.1.symm.trans outer))
  · exact root.2.2

-- §FS-host-boundary.ownership: Every selected cleanup unlink of a completed
-- actual run advances the joint source prefix. Final removal is bound to the
-- original root lifetime; current error/loss never asserts cleanup success.
theorem actual_run_cleanup_unlink_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (frames : ByteNamespaceFrameContract kernel semantics) (otherDirectories : UnlinkDirectoryFrameContract kernel)
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
    {foreignReferences : ForeignReferences} {currentNative : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    (joint : JointPublicationPrefix prior)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ tick :: trailing)
    {outside : List Program.Event} {created : List (Request × Reply)} {run : RunDirectory.Owned}
    {work : List Program.Event} {inside : List (Request × Option Reply)}
    (source : RunCleanupParent runtime initial all actor engine.events outside created run work inside request
      adapter.occurrence.rawBefore.length processed.length (tick.before.project engine))
    (unlink : request.op = .unlinkAt) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
        foreignReferences (processed ++ [tick]) tick.after currentNative,
      next.custody.current.source.custody.catalogue = prior.custody.current.source.custody.catalogue ∧
      next.custody.current.source.custody.caps.family = prior.custody.current.source.custody.caps.family ∧
      JointPublicationPrefix next := by
  have selected : all[processed.length]? = some tick := by
    rw [whole, List.getElem?_append_right (by omega)]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  obtain ⟨root⟩ := actual_run_cleanup_root descriptors lifetimes mounts journal prior whole present source
  have currentBound := actual_run_cleanup_root_bound descriptors lifetimes otherDirectories journal prior joint whole
    present adapter source root unlink
  obtain ⟨birthScope⟩ := prior.custody.current.births (Sigma.mk root.root root.birth) root.member
  have live : engine.references request.first = some source.handle := source.reference
  have comparison : (semantics.at tick.before.shared source.handle.object).byteExact := by
    rcases source.origin with inner | outer
    · rw [inner.2]
      exact actual_run_inner_unlink_comparison (backend := backend) descriptors lifetimes references raw sdk accounts
        authority nativeMetadata lookup probes journal authorityProfile lookupProfile recording selected present adapter source
        inner.1 unlink
    · rw [outer.2, root.container]
      exact registered_boundaries_exact prior.custody.current.source.custody.namespaceState.boundaries
        prior.custody.current.source.custody.names _ _ _ _ currentBound root.privateRoot birthScope.parentPublic
  have actual := selected_filesystem_step tick action present
  have change : DataChange dataObjects request (tick.before.project engine) tick.after.shared := by
    apply namespaceLaws.mutation _ _ _ _ actual (.inr (.inl unlink))
    · simpa only [ComponentRequest, unlink] using source.component
    · simp only [DirectoryOperands, unlink]
      exact ⟨source.handle, live⟩
    · intro fd member handle reference
      have sameFd : fd = request.first := by simpa only [Lookup.parents, unlink, List.mem_singleton] using member
      subst fd
      have same := Option.some.inj (reference.symm.trans live)
      subst handle
      exact comparison
  apply owned_unlink_publication_joint frames descriptors lifetimes references sdk accounts objects metadata lookup
    journal selected action present unlink live source.component comparison change prior joint
  intro object scope bound label
  rcases source.origin with inner | outer
  · have privateParent : prior.custody.current.source.custody.caps.family source.handle.object = some root.root.object := by
      rw [inner.2, root.directory]
      exact root.privateRoot
    have owner := prior.custody.current.source.custody.references actor engine present request.first source.handle
      root.root.object live privateParent
    have descendant := prior.custody.current.source.custody.namespaceState.graph.descendants _ _ _ _ bound privateParent
    have same : root.root.object = scope := Option.some.inj (descendant.symm.trans label)
    exact same ▸ owner
  · have name := outer_cleanup_name source outer.1 unlink
    rw [outer.2, root.container, name, root.name] at bound
    have sameObject : root.root.object = object := Option.some.inj (currentBound.symm.trans bound)
    subst object
    have sameScope : root.root.object = scope := Option.some.inj (root.privateRoot.symm.trans label)
    exact sameScope ▸ root.owned

end LeanCage.Host.Kernel
