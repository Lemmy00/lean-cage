import RetrievalProofs.Authentication
import RetrievalProofs.Envelope
import RetrievalProofs.Policy

namespace LeanCage.Host.Retrieval

open Filesystem

def MetadataObservation (uid : Nat) (target : UInt64) (bundle : Validation.Bundle)
    (envelope : Envelope) (policy : Policy.Accepted) (raw : Option ByteArray)
    (events : List (Request × Reply)) (answer : GatewayWire.Value) : Prop :=
  if envelope.outcome.status == "complete" then
    Returns (completeMetadata uid target bundle envelope policy raw).run events (.ok answer)
  else events = [] ∧ incompleteMetadata envelope raw = .ok answer

def StoredObservation (bundle : Validation.Bundle) (parent : Directories.Parent)
    (target : Directories.Opened) (identity : Option String)
    (events : List (Request × Reply)) (answer : GatewayWire.Value) : Prop :=
  ∃ wire marker envelope policy raw wireEvents markerEvents verification policyEvents jsonEvents rawEvents last,
    events = wireEvents ++ markerEvents ++ verification ++ policyEvents ++ jsonEvents ++ rawEvents ++ last ∧
    Returns (readFile target.fd "publication.wire".toUTF8 Publication.metadataMax) wireEvents (.ok wire) ∧
    Returns (readMarker target.fd) markerEvents (.ok marker) ∧
    VerificationObservation bundle wire marker verification ∧
    EnvelopeBinding wire bundle parent target envelope ∧
    identity.any (fun identity => identity != envelope.outcome.requestId) = false ∧
    PolicyObservation bundle target.fd envelope policyEvents policy ∧
    Returns (resultJson target.fd envelope.metadata) jsonEvents (.ok ()) ∧
    OptionalCopy target.fd "vm-report.json".toUTF8 reportMax envelope.reportPresent rawEvents raw ∧
    MetadataObservation parent.uid target.fd bundle envelope policy raw last answer

-- §FS-host-boundary.publication: Authentication, policy and copied artifacts share one invocation.
theorem readStored_source (bundle : Validation.Bundle) (parent : Directories.Parent)
    (target : Directories.Opened) (identity : Option String)
    {events : List (Request × Reply)} {answer : GatewayWire.Value}
    (run : Returns (readStored bundle parent target identity).run events (.ok answer)) :
    StoredObservation bundle parent target identity events answer := by
  unfold readStored at run
  obtain ⟨wireEvents, wire, afterWireEvents, wireRun, afterWire, shape⟩ := checked_bind_split run
  obtain ⟨markerEvents, marker, afterMarkerEvents, markerRun, afterMarker, markerShape⟩ :=
    checked_bind_split afterWire
  obtain ⟨verification, verified, afterVerifyEvents, verifyRun, afterVerify, verifyShape⟩ :=
    checked_bind_split afterMarker
  cases verified
  obtain ⟨decodeEvents, envelope, afterDecodeEvents, decoded, afterDecode, decodeShape⟩ :=
    checked_bind_split afterVerify
  obtain ⟨rfl, decodedValue⟩ := checked_result _ decoded
  split at afterDecode
  · cases afterDecode
  · rename_i identityCorrect
    obtain ⟨policyEvents, policy, afterPolicyEvents, policyRun, afterPolicy, policyShape⟩ :=
      checked_bind_split afterDecode
    obtain ⟨jsonEvents, json, afterJsonEvents, jsonRun, afterJson, jsonShape⟩ := checked_bind_split afterPolicy
    cases json
    obtain ⟨rawEvents, raw, last, rawRun, final, rawShape⟩ := checked_bind_split afterJson
    refine ⟨wire, marker, envelope, policy, raw, wireEvents, markerEvents, verification,
      policyEvents, jsonEvents, rawEvents, last, ?_, wireRun, markerRun,
      verify_source _ _ _ verifyRun, decodeEnvelope_binding _ _ _ _ _ decodedValue,
      Bool.eq_false_iff.mpr identityCorrect, storedPolicy_source _ _ _ policyRun, jsonRun,
      optionalFile_source _ _ _ _ rawRun, ?_⟩
    · simp only [markerShape, verifyShape, decodeShape, policyShape, jsonShape, rawShape,
        List.nil_append] at shape
      simpa only [List.append_assoc] using shape
    · split at final
      · rename_i complete
        simpa only [MetadataObservation, complete, ↓reduceIte] using final
      · rename_i incomplete
        obtain ⟨empty, value⟩ := checked_result _ final
        simpa [MetadataObservation, incomplete] using
          (show last = [] ∧ incompleteMetadata envelope raw = .ok answer from ⟨empty, value⟩)

end LeanCage.Host.Retrieval
