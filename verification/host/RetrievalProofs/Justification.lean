import RetrievalProofs.Source
import RetrievalProofs.Validation

namespace LeanCage.Host.Retrieval

open Filesystem

def recognizedOutcome (envelope : Envelope) (raw : Option ByteArray) : Outcome :=
  { envelope.outcome with report := raw.bind (Artifacts.knownReport (envelope.outcome.command == "check")) }

theorem incompleteMetadata_source (envelope : Envelope) (raw : Option ByteArray) (answer : GatewayWire.Value)
    (accepted : incompleteMetadata envelope raw = .ok answer) :
    envelope.outcome.exitCode = 126 ∧ answer = (recognizedOutcome envelope raw).metadata .empty .empty ∧
      GatewayWire.encodeValue answer = GatewayWire.encodeValue envelope.metadata := by
  unfold incompleteMetadata at accepted
  obtain ⟨exit, accepted⟩ := except_guard_next accepted
  obtain ⟨same, accepted⟩ := except_guard_next accepted
  cases accepted
  refine ⟨by simpa using exit, rfl, ?_⟩
  have matched : sameValue ((recognizedOutcome envelope raw).metadata .empty .empty)
      envelope.metadata = true := by simpa [recognizedOutcome] using same
  simpa only [sameValue, beq_iff_eq, recognizedOutcome] using matched

inductive ContentEvidence (uid : Nat) (target : UInt64) (bundle : Validation.Bundle)
    (envelope : Envelope) (policy : Policy.Accepted) (raw : Option ByteArray) :
    List (Request × Reply) → GatewayWire.Value → Prop where
  | complete (events : List (Request × Reply)) (answer : GatewayWire.Value)
      (kind : envelope.outcome.status = "complete")
      (observed : CompleteObservation uid target bundle envelope policy raw events answer) :
      ContentEvidence uid target bundle envelope policy raw events answer
  | incomplete (answer : GatewayWire.Value) (kind : envelope.outcome.status ≠ "complete")
      (exit : envelope.outcome.exitCode = 126)
      (report : answer = (recognizedOutcome envelope raw).metadata .empty .empty)
      (matched : GatewayWire.encodeValue answer = GatewayWire.encodeValue envelope.metadata) :
      ContentEvidence uid target bundle envelope policy raw [] answer

theorem content_justified (uid : Nat) (target : UInt64) (bundle : Validation.Bundle)
    (envelope : Envelope) (policy : Policy.Accepted) (raw : Option ByteArray)
    (events : List (Request × Reply)) (answer : GatewayWire.Value)
    (observed : MetadataObservation uid target bundle envelope policy raw events answer) :
    ContentEvidence uid target bundle envelope policy raw events answer := by
  unfold MetadataObservation at observed
  split at observed
  · rename_i complete
    exact .complete events answer (by simpa using complete) (completeMetadata_source _ _ _ _ _ _ observed)
  · rename_i incomplete
    obtain ⟨rfl, accepted⟩ := observed
    obtain ⟨exit, report, matched⟩ := incompleteMetadata_source _ _ _ accepted
    exact .incomplete answer (by simpa using incomplete) exit report matched

def StoredEvidence (bundle : Validation.Bundle) (parent : Directories.Parent)
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
    ContentEvidence parent.uid target.fd bundle envelope policy raw last answer

theorem stored_justified (bundle : Validation.Bundle) (parent : Directories.Parent)
    (target : Directories.Opened) (identity : Option String) (events : List (Request × Reply))
    (answer : GatewayWire.Value) (observed : StoredObservation bundle parent target identity events answer) :
    StoredEvidence bundle parent target identity events answer := by
  obtain ⟨wire, marker, envelope, policy, raw, wireEvents, markerEvents, verification, policyEvents,
    jsonEvents, rawEvents, last, shape, wireRun, markerRun, verified, binding, caller, policyRead,
    jsonRun, rawRead, content⟩ := observed
  exact ⟨wire, marker, envelope, policy, raw, wireEvents, markerEvents, verification, policyEvents,
    jsonEvents, rawEvents, last, shape, wireRun, markerRun, verified, binding, caller, policyRead,
    jsonRun, rawRead, content_justified _ _ _ _ _ _ _ _ content⟩

def DestinationEvidence (bundle : Validation.Bundle) (path : ByteArray) (identity : Option String)
    (events : List (Request × Reply)) (answer : GatewayWire.Value) : Prop :=
  ∃ parent target ancestors opening content targetClose parentClose,
    events = ancestors ++ opening ++ content ++ targetClose ++ parentClose ∧
    Returns (Directories.parent path false) ancestors (.ok parent) ∧
    Returns (Directories.publicAt parent.uid parent.directory.fd parent.name false) opening (.ok target) ∧
    StoredEvidence bundle parent target identity content answer ∧
    Returns (closeResult target.fd (.ok answer)) targetClose (.ok answer) ∧
    Returns (closeResult parent.directory.fd (.ok answer)) parentClose (.ok answer)

def ReportEvidence (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (events : List (Request × Reply)) (answer : GatewayWire.Value) : Prop :=
  request.valid = true ∧ request.command = GatewayWire.reportCommand ∧
    ∃ path identity selection selected,
      events = selection ++ selected ∧
      Returns (destination request bundle) selection (.ok (path, identity)) ∧
      DestinationEvidence bundle path identity selected answer

-- §FS-host-boundary.publication: Actual callers get authenticated, copied and revalidated metadata.
theorem report_justified (request : GatewayWire.Request) (bundle : Validation.Bundle)
    {events : List (Request × Reply)} {answer : GatewayWire.Value}
    (run : Returns (report request bundle) events (.ok answer)) :
    ReportEvidence request bundle events answer := by
  obtain ⟨valid, command, path, identity, selection, selected, shape, selectedRun,
    parent, target, ancestors, opening, content, targetClose, parentClose, sourceShape,
    parentRun, targetRun, stored, targetClosed, parentClosed⟩ := report_source _ _ run
  exact ⟨valid, command, path, identity, selection, selected, shape, selectedRun,
    parent, target, ancestors, opening, content, targetClose, parentClose, sourceShape,
    parentRun, targetRun, stored_justified _ _ _ _ _ _ stored, targetClosed, parentClosed⟩

end LeanCage.Host.Retrieval
