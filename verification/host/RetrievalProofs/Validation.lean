import RetrievalProofs.Stored
import ArtifactsProofs.Composition
import RetrievalProofs.Collection

namespace LeanCage.Host.Retrieval

open Filesystem

def validatedOutcome (envelope : Envelope) (validated : Artifacts.Validated) : Outcome :=
  { envelope.outcome with
    report := some validated.report
    stdout := validated.stdout
    stderr := validated.stderr
    files := validated.files }

def ValidationObservation (bundle : Validation.Bundle) (envelope : Envelope)
    (policy : Policy.Accepted) (received : Transport.Result)
    (events : List (Request × Reply)) (answer : GatewayWire.Value) : Prop :=
  ∃ expected validated hashes validation identification,
    events = validation ++ identification ∧
    Retrieval.expected bundle (envelope.outcome.command == "check") policy.transport = .ok expected ∧
    Returns (Artifacts.validate expected received) validation (.ok validated) ∧
    Artifacts.ArtifactsValid expected received validation validated ∧
    envelope.outcome.exitCode = received.terminal.controller ∧
    Returns (validatedOutcome envelope validated).identify identification (.ok hashes) ∧
    answer = (validatedOutcome envelope validated).metadata hashes.1 hashes.2 ∧
    GatewayWire.encodeValue answer = GatewayWire.encodeValue envelope.metadata

-- §FS-host-boundary.publication: Complete public metadata consumes actual artifact validation.
theorem validateMetadata_source (bundle : Validation.Bundle) (envelope : Envelope)
    (policy : Policy.Accepted) (received : Transport.Result)
    {events : List (Request × Reply)} {answer : GatewayWire.Value}
    (run : Returns (validateMetadata bundle envelope policy received).run events (.ok answer)) :
    ValidationObservation bundle envelope policy received events answer := by
  unfold validateMetadata at run
  obtain ⟨expectedEvents, expected, last, expectedRun, afterExpected, shape⟩ := checked_bind_split run
  obtain ⟨rfl, expectedValue⟩ := checked_result _ expectedRun
  obtain ⟨validation, validated, identificationEvents, validatedRun, afterValidated, validationShape⟩ :=
    checked_bind_split afterExpected
  split at afterValidated
  · cases afterValidated
  · rename_i controller
    obtain ⟨identification, hashes, finalEvents, identified, final, identificationShape⟩ :=
      checked_bind_split afterValidated
    dsimp only at final
    split at final
    · cases final
    · rename_i sameValueBytes
      obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
      cases same
      refine ⟨expected, validated, hashes, validation, identification, ?_, expectedValue,
        validatedRun, Artifacts.validate_sound _ _ _ _ validatedRun, ?_, identified, rfl, ?_⟩
      · simpa only [List.nil_append, validationShape, identificationShape, List.append_nil] using shape
      · simpa using controller
      · have checked : sameValue ((validatedOutcome envelope validated).metadata hashes.1 hashes.2)
            envelope.metadata = true := by simpa [validatedOutcome] using sameValueBytes
        simpa only [sameValue, beq_iff_eq, validatedOutcome] using checked

def reconstructed (envelope : Envelope) (report : ByteArray) (terminal : Transport.Terminal)
    (stored : Option ByteArray) (stdout stderr : ByteArray) (manifest : Option ByteArray)
    (blobs : List Transport.Blob) : Transport.Result := {
  report
  stored
  stdout := if envelope.stdoutPresent then some stdout else none
  stderr := if envelope.stderrPresent then some stderr else none
  manifest
  blobs
  terminal
  frames := [] }

def CompleteObservation (uid : Nat) (target : UInt64) (bundle : Validation.Bundle)
    (envelope : Envelope) (policy : Policy.Accepted) (raw : Option ByteArray)
    (events : List (Request × Reply)) (answer : GatewayWire.Value) : Prop :=
  ∃ report terminal stored stdout stderr manifest blobs storedEvents stdoutEvents stderrEvents
      manifestEvents blobEvents last,
    raw = some report ∧ envelope.terminal = some terminal ∧
    events = storedEvents ++ stdoutEvents ++ stderrEvents ++ manifestEvents ++ blobEvents ++ last ∧
    OptionalCopy target "stored-report.json".toUTF8 reportMax envelope.storedPresent storedEvents stored ∧
    Returns (readFile target "stdout".toUTF8 policy.transport.stdoutMax) stdoutEvents (.ok stdout) ∧
    Returns (readFile target "stderr".toUTF8 policy.transport.stderrMax) stderrEvents (.ok stderr) ∧
    (envelope.stdoutPresent = false → stdout.isEmpty = true) ∧
    (envelope.stderrPresent = false → stderr.isEmpty = true) ∧
    OptionalCopy target "export.manifest".toUTF8 manifestMax envelope.manifestPresent manifestEvents manifest ∧
    ManifestObservation uid target policy.transport manifest blobEvents blobs ∧
    ValidationObservation bundle envelope policy
      (reconstructed envelope report terminal stored stdout stderr manifest blobs) last answer

-- §FS-host-boundary.publication: Reconstructed records use only this invocation's actual copies.
theorem completeMetadata_source (uid : Nat) (target : UInt64) (bundle : Validation.Bundle)
    (envelope : Envelope) (policy : Policy.Accepted) (raw : Option ByteArray)
    {events : List (Request × Reply)} {answer : GatewayWire.Value}
    (run : Returns (completeMetadata uid target bundle envelope policy raw).run events (.ok answer)) :
    CompleteObservation uid target bundle envelope policy raw events answer := by
  cases raw with
  | none => cases run
  | some report =>
    cases terminated : envelope.terminal with
    | none => simp only [completeMetadata, terminated] at run; cases run
    | some terminal =>
      simp only [completeMetadata, terminated] at run
      obtain ⟨storedEvents, stored, afterStoredEvents, storedRun, afterStored, shape⟩ := checked_bind_split run
      obtain ⟨stdoutEvents, stdout, afterStdoutEvents, stdoutRun, afterStdout, stdoutShape⟩ :=
        checked_bind_split afterStored
      obtain ⟨stderrEvents, stderr, afterStderrEvents, stderrRun, afterStderr, stderrShape⟩ :=
        checked_bind_split afterStdout
      split at afterStderr
      · cases afterStderr
      · rename_i absentEmpty
        obtain ⟨manifestEvents, manifest, afterManifestEvents, manifestRun, afterManifest, manifestShape⟩ :=
          checked_bind_split afterStderr
        obtain ⟨blobEvents, blobs, last, blobsRun, final, blobShape⟩ := checked_bind_split afterManifest
        have absent : (envelope.stdoutPresent = false → stdout.isEmpty = true) ∧
            (envelope.stderrPresent = false → stderr.isEmpty = true) := by
          simpa [Bool.or_eq_true] using absentEmpty
        refine ⟨report, terminal, stored, stdout, stderr, manifest, blobs, storedEvents,
          stdoutEvents, stderrEvents, manifestEvents, blobEvents, last, rfl, terminated, ?_,
          optionalFile_source _ _ _ _ storedRun, stdoutRun, stderrRun, absent.1, absent.2,
          optionalFile_source _ _ _ _ manifestRun, manifestBlobs_source _ _ _ _ blobsRun,
          validateMetadata_source _ _ _ _ final⟩
        simpa only [stdoutShape, stderrShape, manifestShape, blobShape, List.append_assoc] using shape


end LeanCage.Host.Retrieval
