import FilesystemCommitMarkerSurvival
import FilesystemCommitDelta

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.publication: Exposure follows the SAME physical move, including
-- committed error/loss. This one rename's attribute law preserves the already-derived
-- source marker; an acknowledgement alone is never used to guess whether it committed.
def CommitRootAt.exposure_attributes {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (namespaces : TrackedAttributeContract kernel) (descriptors : DescriptorContract kernel)
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {resources : PrimitiveCommitResources runtime initial all tick actor engine request observed}
    {family : Family} {catalogue : Catalogue runtime all} (root : CommitRootAt runtime resources family catalogue)
    (actual : kernel.step (tick.before.project engine) request observed tick.after.shared)
    (moving : request.op = .renameNew) (delta : CommitDelta resources root.root.object) {tag : ByteArray}
    (marked : tick.before.shared.attributes root.root.object Publication.attributeName = some (Publication.marker tag)) :
    CommitExposure (tick.before.project engine) tick.after.shared request tag := by
  have first : request.first = resources.source.source.commit.stage.container.fd :=
    congrArg Request.first resources.source.source.commit.operation
  have second : request.second = resources.source.source.commit.parent.directory.fd :=
    congrArg Request.second resources.source.source.commit.operation
  have left : request.left = resources.source.source.commit.stage.name :=
    congrArg Request.left resources.source.source.commit.operation
  have right : request.right = resources.source.source.commit.parent.name :=
    congrArg Request.right resources.source.source.commit.operation
  have allocated : (tick.before.project engine).allocated root.root.object = true := by
    simpa only [root.stage] using descriptors.reference_allocated _ _ _ _ _ _ actual resources.stage.directory.live
  have marker := namespaces.attribute_passive _ _ _ _ root.root.object Publication.attributeName actual
    (by intro setting; rw [moving] at setting; cases setting) (.inr rfl) allocated
    (.inr ⟨resources.parent.directory.handle.object, resources.source.source.commit.parent.name, delta.bound⟩)
  exact {
    source := resources.stage.container.handle
    target := resources.parent.directory.handle
    object := root.root.object
    sourceReference := by rw [first]; exact resources.stage.container.live
    targetReference := by rw [second]; exact resources.stage.parentLive
    sourceBinding := by rw [left]; exact root.bound
    absent := by rw [right]; exact delta.absent
    removed := by rw [left]; exact delta.gone
    published := by rw [right]; exact delta.bound
    marker := marker.trans marked }

-- §AR-host-boundary.interfaces: Retain the original logical attribute projection.
def CommitRootAt.exposure {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (namespaces : NamespaceContract kernel) (descriptors : DescriptorContract kernel)
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {resources : PrimitiveCommitResources runtime initial all tick actor engine request observed}
    {family : Family} {catalogue : Catalogue runtime all} (root : CommitRootAt runtime resources family catalogue)
    (actual : kernel.step (tick.before.project engine) request observed tick.after.shared)
    (moving : request.op = .renameNew) (delta : CommitDelta resources root.root.object) {tag : ByteArray}
    (marked : tick.before.shared.attributes root.root.object Publication.attributeName = some (Publication.marker tag)) :
    CommitExposure (tick.before.project engine) tick.after.shared request tag :=
  CommitRootAt.exposure_attributes namespaces.attributes descriptors root actual moving delta marked

-- §FS-host-boundary.publication: The concrete actual caller produces its MAC/tag
-- history and exact directory exposure from source, custody and committed syscall
-- effects. Private precommit tags and verifier-internal MAC calls are not exposed queries.
theorem actual_commit_source_exposure_attributes {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (moving : request.op = .renameNew) (delta : CommitDelta resources root.root.object)
    {limit : Nat} (earlier : position < limit) :
    ∃ marker : CommitMarkerAt (position := position) runtime root hmac,
      Nonempty (ExposedSourceQuery runtime initial all hmac marker.receipt.key marker.receipt.message limit) := by
  obtain ⟨marker⟩ := primitive_commit_marker_at_root_attributes crypto namespaces descriptors execution.actual selected present root moving
  have current := marker.current_marker (backend := backend) lifetimes objects attributes foreign nativeAttributes execution selected action present
  have exposure := root.exposure_attributes namespaces descriptors (selected_filesystem_step tick action present) moving delta current
  exact ⟨marker, ⟨marker.receipt.exposed selected action present moving exposure earlier⟩⟩

-- §AR-host-boundary.interfaces: Preserve the exact predecessor theorem type.
theorem actual_commit_source_exposure {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (moving : request.op = .renameNew) (delta : CommitDelta resources root.root.object)
    {limit : Nat} (earlier : position < limit) :
    ∃ marker : CommitMarkerAt (position := position) runtime root hmac,
      Nonempty (ExposedSourceQuery runtime initial all hmac marker.receipt.key marker.receipt.message limit) := by
  exact actual_commit_source_exposure_attributes (backend := backend) crypto namespaces.attributes descriptors lifetimes
    objects attributes foreign nativeAttributes execution selected action present root moving delta earlier

end LeanCage.Host.Kernel
