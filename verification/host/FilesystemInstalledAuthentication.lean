import FilesystemKeyDigest
import FilesystemBootstrapSource
import FilesystemRetrievalAuthentication

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: Release installation identifies the actual
-- protected root, key lifetime and this manifest's inventory digest. It asserts
-- no successful loader, copied-key observation or current-request private state.
structure InstalledPublicationKey {initial : World} (catalogue : BootstrapCatalogue initial)
    (sha256 : ByteArray → ByteArray) (root : String) (manifest : Json.Value) where
  secret : ByteArray
  size : secret.size = 32
  object : ObjectId
  identified : catalogue.files root Publication.keyName object
  contents : initial.contents object = secret
  inventory : ∀ files name expected,
    Validation.bundleFiles manifest = some files →
    files.find? (fun field => field.1 == Publication.keyName) = some (name, .string expected) →
    expected = Snapshot.hex (sha256 secret)

def KeyDigestCollision (sha256 : ByteArray → ByteArray) (observed installed : ByteArray) : Prop :=
  observed.size = 32 ∧ installed.size = 32 ∧ observed ≠ installed ∧ sha256 observed = sha256 installed

theorem installed_key_allocated {initial : World} {catalogue : BootstrapCatalogue initial}
    {sha256 : ByteArray → ByteArray} {root : String} {manifest : Json.Value}
    (installed : InstalledPublicationKey catalogue sha256 root manifest) :
    initial.allocated installed.object = true :=
  catalogue.initialized root Publication.keyName installed.object installed.identified

namespace Lowered

theorem authentication_key_digest {kernel : Contract} {sha256 : ByteArray → ByteArray}
    {hmac : ByteArray → ByteArray → ByteArray} (crypto : CryptographicContract kernel sha256 hmac)
    {origin : FilesystemOrigin} {ordinal : Nat} {bundle : Validation.Bundle} {wire tag : ByteArray}
    {before after : World} {events : List (Request × Reply)}
    (use : AuthenticationUse kernel origin ordinal bundle wire tag hmac before events after) :
    Nonempty (KeyDigestUse kernel origin ordinal bundle use.key sha256 before use.keyRaw use.actualBefore) :=
  key_digest_observation crypto use.loaded use.chunks use.leading

-- §FS-host-boundary.publication: Root identity comes from this actual successful
-- load of the SAME selected manifest. The real SHA result leaves an explicit
-- collision alternative instead of assuming finite hashes globally injective.
theorem selected_key_identity {kernel : Contract} {sha256 : ByteArray → ByteArray}
    {origin : FilesystemOrigin} {ordinal : Nat} {initial : World} {catalogue : BootstrapCatalogue initial}
    {request : GatewayWire.Request} (selection : BootstrapSelection catalogue request)
    (selected : CallerPrefixCuts.Selected request)
    (installed : InstalledPublicationKey catalogue sha256 selection.root selected.bundle.manifest)
    {key : ByteArray} {before after : World} {events : List (Request × Reply)}
    (digest : KeyDigestUse kernel origin ordinal selected.bundle key sha256 before events after) :
    selected.bundle.root = selection.root ∧
      (key = installed.secret ∨ KeyDigestCollision sha256 key installed.secret) := by
  have root := Except.ok.inj ((selected_bundle_loaded selected).root.symm.trans selection.selected)
  have inventory := installed.inventory digest.files digest.name digest.expected digest.inventory digest.identified
  have encoded : Snapshot.hex (sha256 key) = Snapshot.hex (sha256 installed.secret) := by
    rw [← digest.interpreted]
    exact digest.inventoryDigest.trans inventory
  have collision := Snapshot.hex_injective encoded
  refine ⟨root, ?_⟩
  by_cases same : key = installed.secret
  · exact .inl same
  · exact .inr ⟨digest.keySize, installed.size, same, collision⟩

theorem authentication_installed_key {kernel : Contract} {sha256 : ByteArray → ByteArray}
    {hmac : ByteArray → ByteArray → ByteArray} (crypto : CryptographicContract kernel sha256 hmac)
    {origin : FilesystemOrigin} {ordinal : Nat} {initial : World} {catalogue : BootstrapCatalogue initial}
    {request : GatewayWire.Request} (selection : BootstrapSelection catalogue request)
    (selected : CallerPrefixCuts.Selected request)
    (installed : InstalledPublicationKey catalogue sha256 selection.root selected.bundle.manifest)
    {wire tag : ByteArray} {before after : World} {events : List (Request × Reply)}
    (use : AuthenticationUse kernel origin ordinal selected.bundle wire tag hmac before events after) :
    selected.bundle.root = selection.root ∧
      (use.key = installed.secret ∨ KeyDigestCollision sha256 use.key installed.secret) := by
  obtain ⟨digest⟩ := authentication_key_digest crypto use
  exact selected_key_identity selection selected installed digest

-- §FS-host-boundary.publication: The forgery candidate uses the release's fixed
-- secret and the exact committed-query history, with a separate SHA bad event.
theorem verification_installed_exposure_or_collision_or_forgery {kernel : Contract}
    {runtime : PrimitiveActorRuntime kernel} {sha256 : ByteArray → ByteArray}
    {hmac : ByteArray → ByteArray → ByteArray} (crypto : CryptographicContract kernel sha256 hmac)
    (actor : ActorId) (initial : World) (all : List (ActorTick runtime))
    {catalogue : BootstrapCatalogue initial} {request : GatewayWire.Request}
    (selection : BootstrapSelection catalogue request) (selected : CallerPrefixCuts.Selected request)
    (installed : InstalledPublicationKey catalogue sha256 selection.root selected.bundle.manifest)
    {ordinal : Nat} {wire supplied : ByteArray} {before after : World} {events : List (Request × Reply)}
    (use : VerificationUse kernel (fun index request reply =>
      SourceReturnAt runtime all actor index Reply (.filesystem request) reply) ordinal
      selected.bundle wire supplied hmac before events after) :
    KeyDigestCollision sha256 use.use.key installed.secret ∨
      ∃ position tick reply,
        all[position]? = some tick ∧ tick.action = .returned actor (.filesystem {
          op := .equalSecret, left := Publication.marker (hmac installed.secret wire), right := supplied }) reply ∧
        (SourceExposed runtime initial all hmac installed.secret position wire ∨
          MacForgery hmac installed.secret (SourceExposed runtime initial all hmac installed.secret position)
            wire (observedTag supplied)) := by
  classical
  rcases (authentication_installed_key crypto selection selected installed use.use).2 with same | collision
  · obtain ⟨position, tick, input, output, sampled, action, present, afterPresent,
      count, beforeShape, afterShape⟩ := use.sampled
    refine .inr ⟨position, tick, use.reply, sampled, ?_, ?_⟩
    · simpa only [use.use.interpreted, same] using action
    · by_cases exposed : SourceExposed runtime initial all hmac installed.secret position wire
      · exact .inl exposed
      · refine .inr ⟨?_, exposed⟩
        exact (congrArg observedTag (by simpa only [same] using use.matching)).trans (observed_marker_tag _)
  · exact .inl collision

theorem report_installed_exposure_or_collision_or_forgery {kernel : Contract}
    {runtime : PrimitiveActorRuntime kernel} {sha256 : ByteArray → ByteArray}
    {hmac : ByteArray → ByteArray → ByteArray} (crypto : CryptographicContract kernel sha256 hmac)
    (actor : ActorId) (initial : World) (all : List (ActorTick runtime))
    {catalogue : BootstrapCatalogue initial} {request : GatewayWire.Request}
    (selection : BootstrapSelection catalogue request) (selected : CallerPrefixCuts.Selected request)
    (installed : InstalledPublicationKey catalogue sha256 selection.root selected.bundle.manifest)
    (ordinal : Nat) {answer : GatewayWire.Value} {before after : World} {events : List (Request × Reply)}
    (actual : RecordedRun kernel (fun index request reply =>
      SourceReturnAt runtime all actor index Reply (.filesystem request) reply) ordinal
      (Retrieval.report request selected.bundle).lower before events after (.ok answer)) :
    ∃ receipt : ReportAuthentication kernel (fun index request reply =>
        SourceReturnAt runtime all actor index Reply (.filesystem request) reply) ordinal
        request selected.bundle answer hmac events,
      KeyDigestCollision sha256 receipt.actual.use.key installed.secret ∨
        ∃ position tick reply,
          all[position]? = some tick ∧ tick.action = .returned actor (.filesystem {
            op := .equalSecret, left := Publication.marker (hmac installed.secret receipt.wire),
            right := receipt.supplied }) reply ∧
          (SourceExposed runtime initial all hmac installed.secret position receipt.wire ∨
            MacForgery hmac installed.secret (SourceExposed runtime initial all hmac installed.secret position)
              receipt.wire (observedTag receipt.supplied)) := by
  obtain ⟨receipt⟩ := recorded_report_authentication crypto actual
  exact ⟨receipt, verification_installed_exposure_or_collision_or_forgery crypto actor initial all
    selection selected installed receipt.actual⟩

end Lowered
end LeanCage.Host.Kernel
