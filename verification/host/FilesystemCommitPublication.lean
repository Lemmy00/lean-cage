import FilesystemCommitCustody
import FilesystemPublicationProgress

namespace LeanCage.Host.Kernel
open Filesystem

structure PublicationCommitStep {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {currentNative : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    (actor : ActorId) (engine : EngineState) (request : Request) (observed : Option Reply) where
  authority : PrimitiveCommitAuthority runtime initial all tick actor engine request observed hostUid semantics
  root : CommitRootAt runtime authority.resources prior.custody.current.source.custody.caps.family
    prior.custody.current.source.custody.catalogue
  updated : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
    foreignReferences (processed ++ [tick]) tick.after currentNative
  sameCatalogue : updated.custody.current.source.custody.catalogue = prior.custody.current.source.custody.catalogue
  effect :
    (tick.after.shared.entries = tick.before.shared.entries ∧
      updated.custody.current.source.custody.caps = prior.custody.current.source.custody.caps.retain tick.after.shared) ∨
    (Nonempty (CommitDelta authority.resources root.root.object) ∧
      updated.custody.current.source.custody.caps =
        prior.custody.current.source.custody.caps.published tick.after.shared root.root.object)

-- §FS-host-boundary.publication: This is the actual commit case of the cumulative
-- induction. It derives the same root and updates release history from the real
-- physical delta, without assuming the complete future custody execution.
theorem actual_commit_registered_publication {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects) (namespaceFrames : ByteNamespaceFrameContract kernel semantics)
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (environment : InterferenceContract kernel) (raw : RawReferenceLifetimeContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (liveMetadata : LiveMetadataContract runtime child)
    (metadata : GlobalAuthorityContract runtime child) (nativeMetadata : NativeMetadataContract native)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    (probes : LookupPrimitiveContract kernel.step kernel.interference semantics)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (mounts : MountContract kernel initial.allocated)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    (authorityProfile : NativeAuthorityProfile native all hostUid) (lookupProfile : NativeLookupProfile native all hostUid)
    {priorProcesses afterProcesses : Processes} {firstNative lastNative : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid priorProcesses firstNative all afterProcesses lastNative)
    {backend : NativeAuthorityJournal recording}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {currentNative : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ tick :: trailing)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (moving : request.op = .renameNew) :
    Nonempty (PublicationCommitStep runtime prior actor engine request observed) := by
  obtain ⟨authority, root, updated, catalogue, choice⟩ := actual_commit_registered_custody_byte (backend := backend)
    namespaceLaws namespaceFrames descriptors aliases lifetimes references environment raw sdk accounts objects liveMetadata
    metadata nativeMetadata lookup probes mounts journal authorityProfile lookupProfile recording prior.custody whole action
    present adapter moving
  rcases choice with unchanged | committed
  · let next := prior.preserved updated catalogue (by
      intro object allocated
      have label := congrArg (fun caps : Capabilities => caps.family object) unchanged.2
      exact label)
    exact ⟨⟨authority, root, next, catalogue, .inl unchanged⟩⟩
  · have release : PublicationReleaseStep updated.current.source.custody.catalogue tick
        prior.custody.current.source.custody.caps.family updated.current.source.custody.caps.family := by
      have exactFamily := congrArg Capabilities.family committed.2
      change updated.current.source.custody.caps.family =
        clearFamily prior.custody.current.source.custody.caps.family root.root.object at exactFamily
      apply Eq.mpr (congrArg (fun after => PublicationReleaseStep updated.current.source.custody.catalogue tick
        prior.custody.current.source.custody.caps.family after) exactFamily)
      rw [catalogue]
      exact publication_release_commit root action moving
    let next := prior.advance updated (by rw [catalogue]; exact fun _ member => member)
      (by intro record member; exact .inl (by rwa [catalogue] at member)) release
    exact ⟨⟨authority, root, next, catalogue, .inr committed⟩⟩

end LeanCage.Host.Kernel
