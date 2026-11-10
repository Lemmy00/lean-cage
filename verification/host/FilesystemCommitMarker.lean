import FilesystemCommitRoot
import FilesystemCommittedAuthentication
import FilesystemAttributes

namespace LeanCage.Host.Kernel
open Filesystem

structure CommitMarkerAt {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    {initial : World} {all : List (ActorTick runtime)} {position : Nat} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {family : Family} {catalogue : Catalogue runtime all}
    {resources : PrimitiveCommitResources runtime initial all tick actor engine request observed}
    (root : CommitRootAt runtime resources family catalogue) (hmac : ByteArray → ByteArray → ByteArray) where
  receipt : PrimitiveCommitAuthentication runtime initial all position tick actor engine request observed hmac
  sameSource : HEq receipt.source resources.source
  tail : receipt.marker.rawAfter = resources.adapter.occurrence.inside.map Program.filesystemPrefixEvent
  beforeReference : receipt.marker.before.handles receipt.source.source.commit.stage.directory.fd =
    some resources.stage.directory.handle
  installed : receipt.marker.after.attributes root.root.object Publication.attributeName =
    some (Publication.marker receipt.tag)
  actualMarker : receipt.markerTick.after.shared.attributes root.root.object Publication.attributeName =
    some (Publication.marker receipt.tag)
  beforeAllocated : receipt.markerTick.before.shared.allocated root.root.object = true
  afterAllocated : receipt.markerTick.after.shared.allocated root.root.object = true

-- §FS-host-boundary.publication: The acknowledged create-only marker names the SAME
-- source-created directory lifetime selected by this actual rename. The source tail
-- contains only its current raw lookup probes; no later successful rename is assumed.
theorem primitive_commit_marker_with_key_digest_attributes {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray}
    (crypto : CryptographicContract kernel sha256 hmac)
    (namespaces : TrackedAttributeContract kernel) (descriptors : DescriptorContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : all[position]? = some tick)
    (present : tick.before.actors actor = some engine)
    {resources : PrimitiveCommitResources runtime initial all tick actor engine request observed}
    {family : Family} {catalogue : Catalogue runtime all}
    (root : CommitRootAt runtime resources family catalogue) (moving : request.op = .renameNew) :
    ∃ marker : CommitMarkerAt (position := position) runtime root hmac,
      Nonempty (PrimitiveKeyDigestAt runtime initial all tick actor engine
        resources.source.invocation.authenticated.bundle marker.receipt.key sha256) := by
  obtain ⟨receipt, digest, sameSource, stage, tail, markerSample⟩ := primitive_commit_authentication_with_key_digest crypto journal selected present
    resources.adapter resources.source
  have guarded : ∀ event ∈ receipt.marker.rawAfter, RetainingEvent event := by
    rw [tail]
    exact adapter_namespace_prefix_retaining resources.adapter (.inr (.inr (.inr (.inl moving))))
  have current : (tick.before.project engine).handles receipt.source.source.commit.stage.directory.fd =
      some resources.stage.directory.handle := by
    rw [stage]
    exact resources.stage.directory.live
  have afterLive : receipt.marker.after.handles receipt.source.source.commit.stage.directory.fd =
      some resources.stage.directory.handle := by
    rw [← actor_retaining_event_handles descriptors receipt.marker.tail guarded]
    exact current
  have beforeLive : receipt.marker.before.handles receipt.source.source.commit.stage.directory.fd =
      some resources.stage.directory.handle := by
    rw [← descriptors.retained _ _ _ _ receipt.marker.actual (by simp [RetainsDescriptors])]
    exact afterLive
  have installed := namespaces.set_attribute _ _ _ _ _ receipt.marker.actual rfl (.inr rfl)
    beforeLive receipt.markerAccepted.1 receipt.markerAccepted.2
  have actualTag : receipt.marker.after.attributes root.root.object Publication.attributeName =
      some (Publication.marker receipt.tag) := by
    simpa only [root.stage] using installed
  obtain ⟨markerInput, markerOutput, markerPresent, markerAfterPresent, markerBefore, markerAfter⟩ := markerSample
  have old : receipt.marker.before.allocated root.root.object = true := by
    simpa only [root.stage] using descriptors.reference_allocated _ _ _ _ _ _ receipt.marker.actual beforeLive
  have allocated := kernel.allocation_monotone _ _ _ _ root.root.object receipt.marker.actual old
  exact ⟨{
    receipt
    sameSource
    tail
    beforeReference := beforeLive
    installed := actualTag
    actualMarker := by simpa only [markerAfter, Population.project] using actualTag
    beforeAllocated := by simpa only [markerBefore, Population.project] using old
    afterAllocated := by simpa only [markerAfter, Population.project] using allocated }, digest⟩

-- §AR-host-boundary.interfaces: Preserve the logical predecessor's full type.
theorem primitive_commit_marker_with_key_digest {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray}
    (crypto : CryptographicContract kernel sha256 hmac)
    (namespaces : NamespaceContract kernel) (descriptors : DescriptorContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : all[position]? = some tick)
    (present : tick.before.actors actor = some engine)
    {resources : PrimitiveCommitResources runtime initial all tick actor engine request observed}
    {family : Family} {catalogue : Catalogue runtime all}
    (root : CommitRootAt runtime resources family catalogue) (moving : request.op = .renameNew) :
    ∃ marker : CommitMarkerAt (position := position) runtime root hmac,
      Nonempty (PrimitiveKeyDigestAt runtime initial all tick actor engine
        resources.source.invocation.authenticated.bundle marker.receipt.key sha256) := by
  exact primitive_commit_marker_with_key_digest_attributes crypto namespaces.attributes descriptors journal selected present root moving

-- §AR-host-boundary.interfaces: Keep the original marker consumer's exact type.
theorem primitive_commit_marker_at_root_attributes {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray}
    (crypto : CryptographicContract kernel sha256 hmac)
    (namespaces : TrackedAttributeContract kernel) (descriptors : DescriptorContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : all[position]? = some tick)
    (present : tick.before.actors actor = some engine)
    {resources : PrimitiveCommitResources runtime initial all tick actor engine request observed}
    {family : Family} {catalogue : Catalogue runtime all}
    (root : CommitRootAt runtime resources family catalogue) (moving : request.op = .renameNew) :
    Nonempty (CommitMarkerAt (position := position) runtime root hmac) := by
  obtain ⟨marker, _⟩ := primitive_commit_marker_with_key_digest_attributes crypto namespaces descriptors journal selected present root moving
  exact ⟨marker⟩

-- §AR-host-boundary.interfaces: Keep the original marker projection unchanged.
theorem primitive_commit_marker_at_root {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray}
    (crypto : CryptographicContract kernel sha256 hmac)
    (namespaces : NamespaceContract kernel) (descriptors : DescriptorContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : all[position]? = some tick)
    (present : tick.before.actors actor = some engine)
    {resources : PrimitiveCommitResources runtime initial all tick actor engine request observed}
    {family : Family} {catalogue : Catalogue runtime all}
    (root : CommitRootAt runtime resources family catalogue) (moving : request.op = .renameNew) :
    Nonempty (CommitMarkerAt (position := position) runtime root hmac) := by
  exact primitive_commit_marker_at_root_attributes crypto namespaces.attributes descriptors journal selected present root moving

end LeanCage.Host.Kernel
