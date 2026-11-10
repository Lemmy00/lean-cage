import FilesystemCreationOwnership
import FilesystemCreationStateJoin
import FilesystemOwnershipRetention
import FilesystemRootUseAuthority

namespace LeanCage.Host.Kernel
open Filesystem

private theorem root_creation_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (sdk : RuntimeDescriptorContract runtime) (lifetimes : LifetimeContract runtime)
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {native : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before native) (joint : JointPublicationPrefix prior)
    (source : OwnershipPrefix runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after)
    (choice : CurrentRootCreation prior.custody.current.source.custody.caps prior.custody.current.source.custody.catalogue
      source.custody.caps source.custody.catalogue tick processed.length)
    (ownership : CustodyOwnershipStep source.custody.catalogue tick
      prior.custody.current.source.custody.caps.family source.custody.caps.family)
    (notLaunch : ∀ actor references closeExec directory, tick.action ≠ .launch actor references closeExec directory) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after native, JointPublicationPrefix next := by
  have labels : ExistingLabels tick.before.shared tick.after.shared
      prior.custody.current.source.custody.caps.family source.custody.caps.family :=
    fun object allocated => .inl (choice.labels object allocated)
  let custody := prior.custody.current.application sdk lifetimes source notLaunch labels choice.included
    (choice.catalogue_members rfl source.custody.namespaceState.registry) ownership
  let next := prior.creation custody choice
  exact ⟨next, joint.advance next choice.included ⟨ownership, labels⟩⟩

-- §FS-host-boundary.ownership: Actual run-root creation extends both the
-- source registry and the SAME retained-ownership journal, even if its
-- mkdir result is an error or its acknowledgement is lost.
theorem run_creation_registered_publication_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (raw : RawReferenceLifetimeContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (liveMetadata : LiveMetadataContract runtime child)
    (types : CreationTypeContract kernel directories)
    (metadata : GlobalAuthorityContract runtime child) (nativeMetadata : NativeMetadataContract native)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    (probes : LookupPrimitiveContract kernel.step kernel.interference semantics)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    (anchor : TemporaryAnchor initial) (anchorLookup : TemporaryLookupContract kernel anchor)
    (anchors : SystemAnchorJournal runtime anchor semantics (Population.empty initial) all final)
    (authorityProfile : NativeAuthorityProfile native all hostUid) (lookupProfile : NativeLookupProfile native all hostUid)
    {first last : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid first callers all last next)
    {backend : NativeAuthorityJournal recording}
    {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (selected : all[processed.length]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (source : PrimitiveRunParent runtime initial all tick actor engine request)
    {foreignReferences : ForeignReferences} {currentNative : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative) (joint : JointPublicationPrefix prior) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative, JointPublicationPrefix next := by
  obtain ⟨nextSource, choice, ownership⟩ := run_creation_ownership_prefix_catalogued (backend := backend)
    namespaceLaws descriptors lifetimes references raw sdk accounts objects liveMetadata types metadata nativeMetadata lookup
    probes journal anchor anchorLookup anchors authorityProfile lookupProfile recording selected action present source
    prior.custody.current.source
  apply root_creation_joint sdk lifetimes prior joint nextSource choice ownership
  intro owner references closeExec directory impossible
  rw [impossible] at action
  cases action

-- §FS-host-boundary.publication: The actual selected publication parent and
-- current birth receipt extend the joint registry on this same mkdir row.
theorem staging_creation_registered_publication_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (accounts : AccountContract kernel hostUid) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (objects : ObjectLifetimeContract runtime)
    (liveMetadata : LiveMetadataContract runtime child) (types : CreationTypeContract kernel directories)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    (dataLookup : DynamicDataLookupContract kernel semantics initial.allocated dataObjects)
    (cwdLookup : WorkingDirectoryContract kernel initial.allocated dataObjects)
    {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (selected : all[processed.length]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (authority : PrimitiveStagingAuthority runtime initial all tick actor engine request observed hostUid semantics)
    (mkdir : request.op = .mkdirAt) {trailing : List (ActorTick runtime)}
    (whole : all = processed ++ tick :: trailing)
    {foreignReferences : ForeignReferences} {currentNative : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative) (joint : JointPublicationPrefix prior)
    (sdk : RuntimeDescriptorContract runtime) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative, JointPublicationPrefix next := by
  obtain ⟨nextSource, choice, ownership⟩ := staging_creation_ownership_prefix_catalogued namespaceLaws descriptors aliases
    accounts lifetimes references objects liveMetadata types lookup journal dataLookup cwdLookup selected action present
    authority mkdir whole rfl prior.custody.current.source
  apply root_creation_joint sdk lifetimes prior joint nextSource choice ownership
  intro owner references closeExec directory impossible
  rw [impossible] at action
  cases action

-- §FS-host-boundary.ownership: Caller-selected public ancestor creation
-- remains outside the private catalogue. Its actual nonreserved operand
-- excludes root registration and its real delta retains prior bindings.
theorem public_creation_registered_publication_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (accounts : AccountContract kernel hostUid) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (objects : ObjectLifetimeContract runtime)
    (liveMetadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (dataLookup : DynamicDataLookupContract kernel semantics initial.allocated dataObjects)
    (cwdLookup : WorkingDirectoryContract kernel initial.allocated dataObjects)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request}
    {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (authority : PrimitiveTraversalAuthority runtime initial ticks tick actor engine request observed hostUid semantics)
    {processed trailing : List (ActorTick runtime)} {foreignReferences : ForeignReferences}
    {nativeCurrent : NativeProcesses}
    (shape : ticks = processed ++ tick :: trailing) (count : processed.length = position)
    (prior : RegisteredPublicationState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before nativeCurrent) (joint : JointPublicationPrefix prior)
    (sdk : RuntimeDescriptorContract runtime) :
    ∃ next : RegisteredPublicationState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after nativeCurrent, JointPublicationPrefix next := by
  let old := prior.custody.current.source.custody
  obtain ⟨state, coverage, valid, names, update⟩ := actual_primitive_public_creation namespaceLaws descriptors aliases
    accounts lifetimes objects liveMetadata lookup journal dataLookup cwdLookup selected action present authority
      old.namespaceState old.names shape count old.history old.catalogue old.coverage old.valid
  have mkdir := authority.resources.source.arguments.1
  have change := authority.namespace_delta namespaceLaws (selected_filesystem_step tick action present)
  have ownership : CustodyOwnershipStep old.catalogue tick old.caps.family (old.caps.retain tick.after.shared).family :=
    nonremoving_ownership_step _ (creation_retains_bindings (before := tick.before.project engine) change (.inl mkdir))
      (by intro object allocated; rfl)
  let next := old.advance_retained descriptors lifetimes references (old.caps.retain tick.after.shared) old.catalogue
    state names coverage valid update (by intro record member; exact member) action
    (by simp only [mkdir, RetainsDescriptors]; decide)
  let nextSource := prior.custody.current.source.advance next (by intro record member; exact member) ownership
  have noRoot : ¬ Nonempty (PrimitiveRootUse runtime initial ticks tick) := by
    rintro ⟨use⟩
    obtain ⟨sameActor, sameRequest, sameObserved⟩ := filesystem_action_origin_unique action use.action
    have reserved := use.reserved
    have publicName := authority.resources.source.arguments.2.2.2.2
    rw [← sameRequest, publicName] at reserved
    cases reserved
  let registered := prior.custody.sourceStep sdk lifetimes nextSource (by
    intro owner references closeExec directory impossible
    rw [impossible] at action
    cases action) (unchanged_existing_labels _ _ _) rfl ownership noRoot
  let result := prior.preserved registered rfl (by intro object allocated; rfl)
  exact ⟨result, joint.preserved registered rfl (by intro object allocated; rfl) ownership⟩

end LeanCage.Host.Kernel
