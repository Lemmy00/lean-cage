import FilesystemCommittedKeyIdentity
import FilesystemCommitExposure

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.publication: A physically committed stage exposes a query
-- under this release's actual secret, or supplies a concrete key-hash collision.
-- A failed or lost acknowledgement does not remove its real committed exposure.
theorem actual_installed_commit_source_exposure_attributes {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray}
    (crypto : CryptographicContract kernel sha256 hmac)
    (namespaces : TrackedAttributeContract kernel) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (objects : ObjectLifetimeContract runtime)
    (attributes : ExistingAttributeContract runtime child) (foreign : ForeignContract runtime)
    (nativeAttributes : NativeExistingAttributeContract native)
    {initial : World} {final : Population} {all : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {firstProcesses lastProcesses : Processes} {firstNative lastNative : NativeProcesses}
    {recording : NativeExternalJournal process child native hostUid firstProcesses firstNative all lastProcesses lastNative}
    (execution : RegisteredCustodyExecution runtime initial all hostUid dataObjects directories semantics recording
      [] (Population.empty initial) final)
    {backend : NativeAuthorityJournal recording}
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : all[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    {resources : PrimitiveCommitResources runtime initial all tick actor engine request observed}
    {family : Family} {catalogue : Catalogue runtime all} (root : CommitRootAt runtime resources family catalogue)
    {bootstrap : BootstrapCatalogue initial}
    (selection : BootstrapSelection bootstrap resources.source.invocation.effective)
    (installed : InstalledPublicationKey bootstrap sha256 selection.root
      resources.source.invocation.authenticated.bundle.manifest)
    (moving : request.op = .renameNew) (delta : CommitDelta resources root.root.object)
    {limit : Nat} (earlier : position < limit) :
    ∃ marker : CommitMarkerAt (position := position) runtime root hmac,
      KeyDigestCollision sha256 marker.receipt.key installed.secret ∨
        (marker.receipt.key = installed.secret ∧
          Nonempty (ExposedSourceQuery runtime initial all hmac installed.secret marker.receipt.message limit)) := by
  obtain ⟨marker, ⟨digest⟩⟩ := primitive_commit_marker_with_key_digest_attributes crypto namespaces descriptors execution.actual
    selected present root moving
  have identity := Lowered.selected_key_identity selection
    resources.source.invocation.authenticated.identified.checked.selected installed digest.digest
  refine ⟨marker, ?_⟩
  rcases identity.2 with same | collision
  · have current := marker.current_marker (backend := backend) lifetimes objects attributes foreign nativeAttributes execution
      selected action present
    have exposure := root.exposure_attributes namespaces descriptors (selected_filesystem_step tick action present) moving delta current
    have query := marker.receipt.exposed selected action present moving exposure earlier
    exact .inr ⟨same, ⟨same ▸ query⟩⟩
  · exact .inl collision

-- §AR-host-boundary.interfaces: Preserve the original logical-frame input type;
-- the raw consumer needs only the attribute-specific sibling above.
theorem actual_installed_commit_source_exposure {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray}
    (crypto : CryptographicContract kernel sha256 hmac)
    (namespaces : NamespaceContract kernel) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (objects : ObjectLifetimeContract runtime)
    (attributes : ExistingAttributeContract runtime child) (foreign : ForeignContract runtime)
    (nativeAttributes : NativeExistingAttributeContract native)
    {initial : World} {final : Population} {all : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {firstProcesses lastProcesses : Processes} {firstNative lastNative : NativeProcesses}
    {recording : NativeExternalJournal process child native hostUid firstProcesses firstNative all lastProcesses lastNative}
    (execution : RegisteredCustodyExecution runtime initial all hostUid dataObjects directories semantics recording
      [] (Population.empty initial) final)
    {backend : NativeAuthorityJournal recording}
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : all[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    {resources : PrimitiveCommitResources runtime initial all tick actor engine request observed}
    {family : Family} {catalogue : Catalogue runtime all} (root : CommitRootAt runtime resources family catalogue)
    {bootstrap : BootstrapCatalogue initial}
    (selection : BootstrapSelection bootstrap resources.source.invocation.effective)
    (installed : InstalledPublicationKey bootstrap sha256 selection.root
      resources.source.invocation.authenticated.bundle.manifest)
    (moving : request.op = .renameNew) (delta : CommitDelta resources root.root.object)
    {limit : Nat} (earlier : position < limit) :
    ∃ marker : CommitMarkerAt (position := position) runtime root hmac,
      KeyDigestCollision sha256 marker.receipt.key installed.secret ∨
        (marker.receipt.key = installed.secret ∧
          Nonempty (ExposedSourceQuery runtime initial all hmac installed.secret marker.receipt.message limit)) := by
  exact actual_installed_commit_source_exposure_attributes (backend := backend) crypto namespaces.attributes descriptors
    lifetimes objects attributes foreign nativeAttributes execution selected action present root selection installed moving delta earlier

end LeanCage.Host.Kernel
