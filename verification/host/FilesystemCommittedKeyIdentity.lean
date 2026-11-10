import FilesystemInstalledAuthentication

namespace LeanCage.Host.Kernel
open Filesystem

structure InstalledCommitAuthentication {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    {initial : World} {all : List (ActorTick runtime)} {position : Nat} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {catalogue : BootstrapCatalogue initial} {sha256 : ByteArray → ByteArray}
    (hmac : ByteArray → ByteArray → ByteArray)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (source : HostCommitCall adapter.occurrence.logicalBefore request none)
    (selection : BootstrapSelection catalogue source.invocation.effective)
    (installed : InstalledPublicationKey catalogue sha256 selection.root
      source.invocation.authenticated.bundle.manifest) where
  receipt : PrimitiveCommitAuthentication runtime initial all position tick actor engine request observed hmac
  sameSource : HEq receipt.source source
  digest : PrimitiveKeyDigestAt runtime initial all tick actor engine
    source.invocation.authenticated.bundle receipt.key sha256
  root : source.invocation.authenticated.bundle.root = selection.root
  identity : (receipt.key = installed.secret ∧ receipt.tag = hmac installed.secret receipt.message) ∨
    KeyDigestCollision sha256 receipt.key installed.secret

-- §FS-host-boundary.publication: The publisher's selected manifest, actual copied
-- key SHA, MAC and marker stay on its SAME source/kernel prefix. No private tag is
-- counted as public until the separate real-commit exposure receipt is available.
theorem primitive_installed_commit_authentication {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray}
    (crypto : CryptographicContract kernel sha256 hmac)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : all[position]? = some tick)
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (source : HostCommitCall adapter.occurrence.logicalBefore request none)
    {catalogue : BootstrapCatalogue initial} (selection : BootstrapSelection catalogue source.invocation.effective)
    (installed : InstalledPublicationKey catalogue sha256 selection.root
      source.invocation.authenticated.bundle.manifest) :
    Nonempty (InstalledCommitAuthentication (position := position) runtime hmac adapter source selection installed) := by
  obtain ⟨receipt, ⟨digest⟩, sameSource, sameStage, markerTail, markerSample⟩ :=
    primitive_commit_authentication_with_key_digest crypto journal selected present adapter source
  have identity := Lowered.selected_key_identity selection
    source.invocation.authenticated.identified.checked.selected installed digest.digest
  refine ⟨⟨receipt, sameSource, digest, identity.1, ?_⟩⟩
  rcases identity.2 with same | collision
  · exact .inl ⟨same, by simpa only [same] using receipt.interpreted⟩
  · exact .inr collision

end LeanCage.Host.Kernel
