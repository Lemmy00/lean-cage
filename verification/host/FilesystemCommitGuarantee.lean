import FilesystemCommitCustody
import FilesystemCommitExposure

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.publication: This application result joins custody and actual
-- exposed authentication at the SAME source rename. The effect choice is physical;
-- an error or missing acknowledgement does not select the unchanged branch.
structure AuthenticatedCommitResult {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    (actor : ActorId) (engine : EngineState) (request : Request) (observed : Option Reply)
    (hmac : ByteArray → ByteArray → ByteArray) where
  authority : PrimitiveCommitAuthority runtime initial all tick actor engine request observed hostUid semantics
  root : CommitRootAt runtime authority.resources prior.current.source.custody.caps.family
    prior.current.source.custody.catalogue
  updated : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
    foreignReferences (processed ++ [tick]) tick.after currentNative
  sameCatalogue : updated.current.source.custody.catalogue = prior.current.source.custody.catalogue
  effect :
    (tick.after.shared.entries = tick.before.shared.entries ∧
      updated.current.source.custody.caps = prior.current.source.custody.caps.retain tick.after.shared) ∨
    (∃ _delta : CommitDelta authority.resources root.root.object,
      ∃ marker : CommitMarkerAt (position := processed.length) runtime root hmac,
        Nonempty (ExposedSourceQuery runtime initial all hmac marker.receipt.key marker.receipt.message
          (processed.length + 1)) ∧
        updated.current.source.custody.caps = prior.current.source.custody.caps.published tick.after.shared root.root.object)

-- §FS-host-boundary.publication: Actual source and primitive producers supply the
-- root/authority/MAC/marker fields and extend the constructed custody history.
-- That history remains an application induction result, never a primitive premise.
theorem actual_authenticated_commit {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray}
    (crypto : CryptographicContract kernel sha256 hmac)
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (namespaceFrames : NamespaceContract kernel)
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (environment : InterferenceContract kernel) (raw : RawReferenceLifetimeContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (liveMetadata : LiveMetadataContract runtime child)
    (metadata : GlobalAuthorityContract runtime child) (nativeMetadata : NativeMetadataContract native)
    (attributes : ExistingAttributeContract runtime child) (foreign : ForeignContract runtime)
    (nativeAttributes : NativeExistingAttributeContract native)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    (probes : LookupPrimitiveContract kernel.step kernel.interference semantics)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (mounts : MountContract kernel initial.allocated)
    (authorityProfile : NativeAuthorityProfile native all hostUid) (lookupProfile : NativeLookupProfile native all hostUid)
    {firstProcesses lastProcesses : Processes} {firstNative lastNative : NativeProcesses}
    {recording : NativeExternalJournal process child native hostUid firstProcesses firstNative all lastProcesses lastNative}
    {backend : NativeAuthorityJournal recording}
    (execution : RegisteredCustodyExecution runtime initial all hostUid dataObjects directories semantics recording
      [] (Population.empty initial) final)
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ tick :: trailing)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (moving : request.op = .renameNew) :
    Nonempty (AuthenticatedCommitResult runtime prior actor engine request observed hmac) := by
  obtain ⟨authority, root, updated, catalogue, choice⟩ := actual_commit_registered_custody (backend := backend) namespaceLaws namespaceFrames
    descriptors aliases lifetimes references environment raw sdk accounts objects liveMetadata metadata nativeMetadata
    lookup probes mounts execution.actual authorityProfile lookupProfile recording prior whole action present adapter moving
  refine ⟨⟨authority, root, updated, catalogue, ?_⟩⟩
  rcases choice with unchanged | ⟨⟨delta⟩, published⟩
  · exact .inl unchanged
  · have selected : all[processed.length]? = some tick := by
      rw [whole, List.getElem?_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem?_cons_zero]
    obtain ⟨marker, exposed⟩ := actual_commit_source_exposure (backend := backend) crypto namespaceFrames descriptors lifetimes objects
      attributes foreign nativeAttributes execution selected action present root moving delta (Nat.lt_succ_self _)
    exact .inr ⟨delta, marker, exposed, published⟩

end LeanCage.Host.Kernel
