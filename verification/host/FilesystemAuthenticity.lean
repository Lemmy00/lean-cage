import FilesystemCryptography

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.publication: Extract the candidate tag from observed bytes, not the verifier.
def observedTag (supplied : ByteArray) : ByteArray :=
  supplied.extract Publication.markerMagic.size supplied.size

theorem observed_marker_tag (tag : ByteArray) : observedTag (Publication.marker tag) = tag := by
  unfold observedTag Publication.marker
  exact ByteArray.extract_append_eq_right rfl (by rw [ByteArray.size_append])

def RecordedMarkerAuthentication.wire {kernel : Contract} {runtime : ActorRuntime kernel}
    {ticks : List (ActorTick runtime)} {actor : ActorId} {position : Nat} {engine : EngineState}
    {request : Request} {observed : Option Reply} {hmac : ByteArray → ByteArray → ByteArray}
    (receipt : RecordedMarkerAuthentication runtime ticks actor position engine request observed hmac) : ByteArray :=
  Publication.markerWire receipt.source.source.effective receipt.source.source.source.display
    receipt.source.source.stdoutHash receipt.source.source.stderrHash receipt.source.source.source.marker.policyDigest
    receipt.source.source.source.parent receipt.source.source.source.stage

-- §FS-host-boundary.publication: Only a genuine publisher's actual MAC is a signing query.
structure SourceSigningQuery {kernel : Contract} (runtime : ActorRuntime kernel)
    (ticks : List (ActorTick runtime)) (hmac : ByteArray → ByteArray → ByteArray)
    (secret message : ByteArray) (before : Nat) where
  markerPosition : Nat
  markerTick : ActorTick runtime
  actor : ActorId
  engine : EngineState
  request : Request
  observed : Option Reply
  selected : ticks[markerPosition]? = some markerTick
  action : markerTick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed))
  present : markerTick.before.actors actor = some engine
  setting : request.op = .setAttribute
  named : request.left = Publication.attributeName
  receipt : RecordedMarkerAuthentication runtime ticks actor markerPosition engine request observed hmac
  sameKey : receipt.use.key = secret
  sameMessage : receipt.wire = message
  earlier : receipt.macPosition < before

-- §AR-host-boundary.primitives: A computational game must cover the key's entire query history.
-- Current-request history alone cannot justify a bound for old persisted reports.
def SourceSigned {kernel : Contract} (runtime : ActorRuntime kernel) (ticks : List (ActorTick runtime))
    (hmac : ByteArray → ByteArray → ByteArray) (secret : ByteArray) (before : Nat) (message : ByteArray) : Prop :=
  Nonempty (SourceSigningQuery runtime ticks hmac secret message before)

-- §FS-host-boundary.acceptance: Publisher markers receive a prior genuine signing query.
theorem actual_marker_source_query {kernel : Contract} {runtime : ActorRuntime kernel}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray}
    (laws : CryptographicContract kernel sha256 hmac) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (setting : request.op = .setAttribute) (named : request.left = Publication.attributeName) :
    ∃ secret message, SourceSigned runtime ticks hmac secret position message ∧
      request.right = Publication.marker (hmac secret message) := by
  obtain ⟨receipt⟩ := actual_recorded_marker_authentication laws descriptors lifetimes references environment
    journal selected action present setting named
  refine ⟨receipt.use.key, receipt.wire,
    ⟨⟨position, tick, actor, engine, request, observed, selected, action, present, setting, named,
      receipt, rfl, rfl, receipt.earlier⟩⟩, ?_⟩
  have source := congrArg Request.right receipt.source.source.source.marker.operation
  exact source.trans (congrArg Publication.marker receipt.use.interpreted)

-- §AR-host-boundary.primitives: This is the ordinary MAC forgery event, without a no-forgery axiom.
def MacForgery (hmac : ByteArray → ByteArray → ByteArray) (secret : ByteArray)
    (queried : ByteArray → Prop) (message candidate : ByteArray) : Prop :=
  candidate = hmac secret message ∧ ¬queried message

-- §FS-host-boundary.publication: A verified nonquery marker gives the observed candidate forgery.
theorem accepted_nonquery_is_forgery {kernel : Contract} {hmac : ByteArray → ByteArray → ByteArray}
    {origin : FilesystemOrigin} {ordinal : Nat} {bundle : Validation.Bundle} {wire supplied : ByteArray}
    {before after : World} {events : List (Request × Reply)}
    (use : VerificationUse kernel origin ordinal bundle wire supplied hmac before events after)
    (queried : ByteArray → Prop) (newMessage : ¬queried wire) :
    MacForgery hmac use.authentication.key queried wire (observedTag supplied) := by
  constructor
  · exact (congrArg observedTag use.matching).trans (observed_marker_tag _)
  · exact newMessage

-- §FS-host-boundary.acceptance: The same actual verification gives source origin or a forgery.
theorem actual_verification_origin_or_forgery {kernel : Contract} {runtime : ActorRuntime kernel}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray}
    (laws : CryptographicContract kernel sha256 hmac) (actor : ActorId)
    (ticks : List (ActorTick runtime)) (ordinal : Nat) (bundle : Validation.Bundle)
    (wire supplied : ByteArray) {before after : World} {events : List (Request × Reply)}
    (actual : RecordedRun kernel (fun index request reply =>
      SourceReturnAt runtime ticks actor index Reply (.filesystem request) reply) ordinal
      (Publication.verify bundle wire supplied) before events after (.ok ())) :
    ∃ secret position tick reply,
      ticks[position]? = some tick ∧ tick.action = .returned actor (.filesystem {
        op := .equalSecret
        left := Publication.marker (hmac secret wire)
        right := supplied }) reply ∧
      (SourceSigned runtime ticks hmac secret position wire ∨
        MacForgery hmac secret (SourceSigned runtime ticks hmac secret position) wire (observedTag supplied)) := by
  classical
  obtain ⟨use⟩ := recorded_verification laws actual
  obtain ⟨position, tick, initial, final, selected, action, present, afterPresent,
    count, beforeShape, afterShape⟩ := use.sampled
  refine ⟨use.authentication.key, position, tick, use.reply, selected, ?_, ?_⟩
  · simpa only [use.authentication.interpreted] using action
  · by_cases signed : SourceSigned runtime ticks hmac use.authentication.key position wire
    · exact .inl signed
    · exact .inr (accepted_nonquery_is_forgery use _ signed)

-- §FS-host-boundary.publication: Reduce the application bad event to the cryptographic event.
def acceptedBad (hmac : ByteArray → ByteArray → ByteArray) (secret : ByteArray)
    (queried : ByteArray → Prop) (wire supplied : ByteArray) : Prop :=
  supplied = Publication.marker (hmac secret wire) ∧ ¬queried wire

theorem accepted_bad_reduces {hmac : ByteArray → ByteArray → ByteArray} {secret wire supplied : ByteArray}
    {queried : ByteArray → Prop} (bad : acceptedBad hmac secret queried wire supplied) :
    MacForgery hmac secret queried wire (observedTag supplied) := by
  refine ⟨?_, bad.2⟩
  rw [bad.1]
  exact observed_marker_tag _

-- §AR-host-boundary.primitives: Pointwise reduction transfers any finite sampled game bound.
theorem bad_sample_count_le {Seed : Type} (seeds : List Seed)
    (bad forged : Seed → Prop) [DecidablePred bad] [DecidablePred forged]
    (reduces : ∀ seed, bad seed → forged seed) :
    (seeds.filter bad).length ≤ (seeds.filter forged).length := by
  induction seeds with
  | nil => exact Nat.le_refl 0
  | cons seed rest ih =>
    by_cases badSeed : bad seed
    · have forgedSeed := reduces seed badSeed
      simpa [badSeed, forgedSeed] using Nat.succ_le_succ ih
    · by_cases forgedSeed : forged seed
      · simpa [badSeed, forgedSeed] using Nat.le_trans ih (Nat.le_succ _)
      · simpa [badSeed, forgedSeed] using ih

end LeanCage.Host.Kernel
