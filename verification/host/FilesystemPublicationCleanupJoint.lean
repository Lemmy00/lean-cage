import FilesystemCleanupRootBoundary
import FilesystemRunRemoval
import FilesystemCleanupObservationSource
import FilesystemCheckedParents

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: Actual failed-publication cleanup derives
-- its own final root/parent binding and advances the SAME joint prefix on
-- every syscall result, including a committed removal with a lost reply.
theorem actual_publication_cleanup_final_unlink_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (frames : ByteNamespaceFrameContract kernel semantics) (otherDirectories : UnlinkDirectoryFrameContract kernel)
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (environment : InterferenceContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (accounts : AccountContract kernel hostUid) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child) (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (targets : OpenTargetContract kernel semantics initial.allocated dataObjects)
    (mounts : MountContract kernel initial.allocated)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {foreignReferences : ForeignReferences} {currentNative : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    (joint : JointPublicationPrefix prior)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ tick :: trailing)
    (call : PublicationCleanup.Host adapter.occurrence.logicalBefore request)
    (unlink : request.op = .unlinkAt)
    (outer : request.first = call.source.attempt.context.stage.container.fd) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
        foreignReferences (processed ++ [tick]) tick.after currentNative,
      next.custody.current.source.custody.catalogue = prior.custody.current.source.custody.catalogue ∧
      next.custody.current.source.custody.caps.family = prior.custody.current.source.custody.caps.family ∧
      JointPublicationPrefix next := by
  have selected : all[processed.length]? = some tick := by
    rw [whole, List.getElem?_append_right (by omega)]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  obtain ⟨source, sameActor, guards, eventTrace⟩ := primitive_cleanup_stage_continuation descriptors aliases lifetimes
    references environment journal selected present adapter call
  obtain ⟨segment⟩ := actual_cleanup_stage_segment descriptors adapter source guards unlink
  obtain ⟨root⟩ := actual_cleanup_stage_root descriptors lifetimes mounts journal prior whole present adapter
    source sameActor guards eventTrace unlink
  obtain ⟨birthScope⟩ := prior.custody.current.births (Sigma.mk root.root root.birth) root.member
  have live : engine.references request.first = some source.root.use.parent := by
    rw [outer]
    exact segment.current_container descriptors unlink
  have currentOpens := actual_private_directory_opens descriptors lifetimes targets journal selected present whole rfl
    prior.custody.current.source.custody.history
  have opens : PrivateDirectoryOpens kernel (fun ordinal query reply before after =>
      SourceReturnAt runtime all source.earlier.source.inputActor ordinal Reply (.filesystem query) reply before after ∧
        ordinal < engine.events.length) prior.custody.current.source.custody.caps.family := by
    simpa only [sameActor] using currentOpens
  have privateRoot : prior.custody.current.source.custody.caps.family source.earlier.source.opening.handle.object =
      some root.root.object := by rw [root.directory]; exact root.privateRoot
  have actualFinal : Nonempty (Lowered.FinalCleanupFrontier call.source.attempt.context.parent
      call.source.attempt.context.stage call.source.effective call.source.attempt.inside request) := by
    rcases segment.parent_or_final_source descriptors adapter guards eventTrace unlink opens privateRoot with privateParent | finalSource
    · obtain ⟨parent, reference, privateParent⟩ := privateParent
      have same := Option.some.inj (reference.symm.trans live)
      subst parent
      rw [root.container, birthScope.parentPublic] at privateParent
      cases privateParent
    · exact finalSource
  obtain ⟨finalSource⟩ := actualFinal
  have bound := actual_publication_cleanup_root_bound descriptors lifetimes otherDirectories targets journal prior joint whole
    present adapter source sameActor guards eventTrace segment root finalSource unlink
  have name : request.left = root.root.name := (congrArg Request.left finalSource.operation).trans root.name
  have component : Directories.component request.left = true := by
    rw [name, ← root.birth.name]
    exact root.birth.component
  have comparison : (semantics.at tick.before.shared source.root.use.parent.object).byteExact := by
    rw [root.container]
    exact registered_boundaries_exact prior.custody.current.source.custody.namespaceState.boundaries
      prior.custody.current.source.custody.names _ _ _ _ bound root.privateRoot birthScope.parentPublic
  have actual := selected_filesystem_step tick action present
  have change : DataChange dataObjects request (tick.before.project engine) tick.after.shared := by
    apply namespaceLaws.mutation _ _ _ _ actual (.inr (.inl unlink))
    · simpa only [ComponentRequest, unlink] using component
    · simp only [DirectoryOperands, unlink]
      exact ⟨source.root.use.parent, live⟩
    · intro fd member handle reference
      have sameFd : fd = request.first := by simpa only [Lookup.parents, unlink, List.mem_singleton] using member
      subst fd
      have same := Option.some.inj (reference.symm.trans live)
      subst handle
      exact comparison
  apply owned_unlink_publication_joint frames descriptors lifetimes references sdk accounts objects metadata lookup
    journal selected action present unlink live component comparison change prior joint
  intro object scope binding label
  rw [root.container, name] at binding
  have sameObject : root.root.object = object := Option.some.inj (bound.symm.trans binding)
  subst object
  have sameScope : root.root.object = scope := Option.some.inj (root.privateRoot.symm.trans label)
  exact sameScope ▸ root.owned

-- §FS-host-boundary.ownership: Every actual publisher cleanup unlink now
-- advances the joint state. Nested comparison comes from its actual fstat
-- and guard; the final branch retains the original root lifetime/name.
theorem actual_publication_cleanup_unlink_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (frames : ByteNamespaceFrameContract kernel semantics) (otherDirectories : UnlinkDirectoryFrameContract kernel)
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime) (raw : RawReferenceLifetimeContract kernel)
    (environment : InterferenceContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (accounts : AccountContract kernel hostUid) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child) (authority : GlobalAuthorityContract runtime child)
    (nativeMetadata : NativeMetadataContract native) (lookup : LookupMutationContract (runtime := runtime) child native)
    (probes : LookupPrimitiveContract kernel.step kernel.interference semantics)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (targets : OpenTargetContract kernel semantics initial.allocated dataObjects)
    (mounts : MountContract kernel initial.allocated)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    (authorityProfile : NativeAuthorityProfile native all hostUid) (lookupProfile : NativeLookupProfile native all hostUid)
    {before after : Processes} {first last : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid before first all after last)
    {backend : NativeAuthorityJournal recording}
    {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {foreignReferences : ForeignReferences} {currentNative : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    (joint : JointPublicationPrefix prior)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ tick :: trailing)
    (call : PublicationCleanup.Host adapter.occurrence.logicalBefore request) (unlink : request.op = .unlinkAt) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
        foreignReferences (processed ++ [tick]) tick.after currentNative,
      next.custody.current.source.custody.catalogue = prior.custody.current.source.custody.catalogue ∧
      next.custody.current.source.custody.caps.family = prior.custody.current.source.custody.caps.family ∧
      JointPublicationPrefix next := by
  have selected : all[processed.length]? = some tick := by
    rw [whole, List.getElem?_append_right (by omega)]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  obtain ⟨source, sameActor, guards, eventTrace⟩ := primitive_cleanup_stage_continuation descriptors aliases lifetimes
    references environment journal selected present adapter call
  obtain ⟨segment⟩ := actual_cleanup_stage_segment descriptors adapter source guards unlink
  obtain ⟨root⟩ := actual_cleanup_stage_root descriptors lifetimes mounts journal prior whole present adapter
    source sameActor guards eventTrace unlink
  have currentOpens := actual_private_directory_opens descriptors lifetimes targets journal selected present whole rfl
    prior.custody.current.source.custody.history
  have opens : PrivateDirectoryOpens kernel (fun ordinal query reply before after =>
      SourceReturnAt runtime all source.earlier.source.inputActor ordinal Reply (.filesystem query) reply before after ∧
        ordinal < engine.events.length) prior.custody.current.source.custody.caps.family := by
    simpa only [sameActor] using currentOpens
  have privateRoot : prior.custody.current.source.custody.caps.family source.earlier.source.opening.handle.object =
      some root.root.object := by rw [root.directory]; exact root.privateRoot
  rcases segment.observed_parent_or_final descriptors adapter guards eventTrace unlink opens privateRoot with inner | outer
  · obtain ⟨parent⟩ := inner
    obtain ⟨identity⟩ := cleanup_stage_uid_sample descriptors adapter call
    have uid := sampled_uid_is_host accounts identity
    let original := parent.observation.mapOrigin (fun ordinal query reply before after sampled =>
      Eq.mp (congrArg (fun who => SourceReturnAt runtime all who ordinal Reply (.filesystem query) reply before after) sameActor) sampled)
    let observation : ObservedDirectory kernel (fun ordinal query reply =>
        SourceReturnAt runtime all actor ordinal Reply (.filesystem query) reply)
        (segment.beforeRaw.length + segment.cleanupRaw.length) (tick.before.project engine) hostUid parent.directory := {
      handle := original.handle
      live := original.live
      raw := original.raw
      sample := original.sample
      earlier := original.earlier
      trusted := uid ▸ original.trusted }
    have beforeGuard : observation.sample.ordinal < adapter.occurrence.rawBefore.length := by
      rw [← segment.guard_count adapter guards eventTrace]
      exact observation.earlier
    have beforeCall : observation.sample.ordinal < engine.events.length := by
      have count := congrArg List.length adapter.occurrence.trace
      simp only [List.length_append, List.length_map] at count
      omega
    have live : engine.references parent.directory.fd = some observation.handle := observation.live
    obtain ⟨interval, sameHandle, sameOrdinal⟩ := checked_parent_interval_owned (backend := backend) descriptors lifetimes
      references raw sdk accounts journal recording selected present observation live beforeCall
    have operandLive : engine.references request.first = some observation.handle := parent.operand ▸ live
    have member : request.first ∈ Lookup.parents request := by simp only [Lookup.parents, unlink, List.mem_singleton]
    obtain ⟨information, known, trusted, names⟩ := checked_parent_comparison lifetimes authority nativeMetadata lookup probes
      journal authorityProfile lookupProfile interval adapter (.inr (.inr (.inl unlink))) request.first member
      observation.handle operandLive (by rw [sameHandle]) (by rw [sameOrdinal]; exact beforeGuard)
    have comparison : (semantics.at tick.before.shared observation.handle.object).byteExact := by
      simpa only [sameHandle] using names
    have actual := selected_filesystem_step tick action present
    have change : DataChange dataObjects request (tick.before.project engine) tick.after.shared := by
      apply namespaceLaws.mutation _ _ _ _ actual (.inr (.inl unlink))
      · simpa only [ComponentRequest, unlink] using parent.component
      · simp only [DirectoryOperands, unlink]
        exact ⟨observation.handle, operandLive⟩
      · intro fd member handle reference
        have sameFd : fd = request.first := by simpa only [Lookup.parents, unlink, List.mem_singleton] using member
        subst fd
        have same := Option.some.inj (reference.symm.trans operandLive)
        subst handle
        exact comparison
    apply owned_unlink_publication_joint frames descriptors lifetimes references sdk accounts objects metadata lookup
      journal selected action present unlink operandLive parent.component comparison change prior joint
    intro object scope bound label
    have privateParent : prior.custody.current.source.custody.caps.family observation.handle.object = some root.root.object :=
      parent.privateParent
    have owner := prior.custody.current.source.custody.references actor engine present request.first observation.handle
      root.root.object operandLive privateParent
    have descendant := prior.custody.current.source.custody.namespaceState.graph.descendants _ _ _ _ bound privateParent
    have sameScope : root.root.object = scope := Option.some.inj (descendant.symm.trans label)
    exact sameScope ▸ owner
  · obtain ⟨finalSource⟩ := outer
    exact actual_publication_cleanup_final_unlink_joint namespaceLaws frames otherDirectories descriptors aliases lifetimes
      references environment sdk accounts objects metadata lookup targets mounts journal action present adapter prior joint whole
      call unlink (congrArg Request.first finalSource.operation)

end LeanCage.Host.Kernel
