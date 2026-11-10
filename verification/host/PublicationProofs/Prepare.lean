import PublicationProofs.Effects

namespace LeanCage.Host.Publication

open Filesystem

def candidate (input : Input) (target : ByteArray) : Outcome :=
  { input.outcome with output := some target, publication := "stored", publicationError := none }

def stagedInput (input : Input) (target : ByteArray) : Input :=
  { input with outcome := candidate input target }

def PreparedObservation (bundle : Validation.Bundle) (input : Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) (parent : Directories.Parent) (stage : Directories.Fresh)
    (events : List (Request × Reply)) (outcome : Outcome) : Prop :=
  outcome = candidate input target ∧ ∃ policyDigest json tag hashing authenticating filling marked,
    let metadata := (candidate input target).metadata stdoutHash stderrHash
    let wire := GatewayWire.encodeResponse 0 (envelope (stagedInput input target) metadata policyDigest parent stage)
    events = hashing ++ authenticating ++ filling ++ [({
      op := .setAttribute
      first := stage.directory.fd
      left := attributeName
      right := marker tag }, marked)] ∧
    Returns (Filesystem.hash input.policy.raw) hashing (.ok policyDigest) ∧
    WireJson.render GatewayWire.valueDepthMax metadata = .ok json ∧
    json.size ≤ metadataMax ∧ wire.size ≤ metadataMax ∧
    Retrieval.AuthenticationObservation bundle wire tag authenticating ∧
    Returns (fill parent.uid stage.directory.fd (stagedInput input target)
      (json ++ "\n".toUTF8) wire) filling (.ok ()) ∧ marked.1 = 0 ∧ marked.2 = .empty

-- §FS-host-boundary.publication: Actual bytes and authentication precede the stage's marker.
theorem prepare_source (bundle : Validation.Bundle) (input : Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) (parent : Directories.Parent) (stage : Directories.Fresh)
    {events : List (Request × Reply)} {outcome : Outcome}
    (run : Returns (prepare bundle input target stdoutHash stderrHash parent stage) events (.ok outcome)) :
    PreparedObservation bundle input target stdoutHash stderrHash parent stage events outcome := by
  unfold prepare at run
  obtain ⟨hashing, result, last, hashed, afterHash, shape⟩ := Snapshot.returns_bind_split _ _ run
  cases result with
  | error => cases afterHash
  | ok policyDigest =>
    dsimp only at afterHash
    split at afterHash
    · rename_i json rendered
      split at afterHash
      · cases afterHash
      · rename_i bounded
        obtain ⟨authenticating, result, afterAuthEvents, authenticated, afterAuth, authShape⟩ :=
          Snapshot.returns_bind_split _ _ afterHash
        cases result with
        | error => cases afterAuth
        | ok tag =>
          dsimp only at afterAuth
          obtain ⟨filling, result, afterFillEvents, filled, afterFill, fillShape⟩ :=
            Snapshot.returns_bind_split _ _ afterAuth
          cases result with
          | error => cases afterFill
          | ok complete =>
            cases complete
            obtain ⟨marked, finalEvents, markedShape, final⟩ := Snapshot.returns_call_split afterFill
            dsimp only [Filesystem.Program.bind] at final
            split at final
            · cases final
            · rename_i valid
              obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
              cases same
              have markerValid : marked.1 = 0 ∧ marked.2 = .empty := by
                have flags : marked.1 = 0 ∧ marked.2.isEmpty = true := by
                  simpa [Bool.or_eq_true] using valid
                exact ⟨flags.1, ByteArray.size_eq_zero_iff.mp
                  (by simpa only [ByteArray.isEmpty, beq_iff_eq] using flags.2)⟩
              have bounds : json.size ≤ metadataMax ∧
                  (GatewayWire.encodeResponse 0 (envelope (stagedInput input target)
                    ((candidate input target).metadata stdoutHash stderrHash) policyDigest parent stage)).size ≤
                      metadataMax := by
                simpa only [stagedInput, candidate, Bool.or_eq_true, decide_eq_true_eq,
                  not_or, Nat.not_lt] using bounded
              refine ⟨rfl, policyDigest, json, tag, hashing, authenticating, filling, marked, ?_,
                hashed, rendered, bounds.1, bounds.2, Retrieval.authenticate_source _ _ authenticated,
                filled, markerValid.1, markerValid.2⟩
              simpa only [authShape, fillShape, markedShape, List.append_assoc] using shape
    · cases afterHash

theorem prepare_report (bundle : Validation.Bundle) (input : Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) (parent : Directories.Parent) (stage : Directories.Fresh)
    {events : List (Request × Reply)} {outcome : Outcome}
    (run : Returns (prepare bundle input target stdoutHash stderrHash parent stage) events (.ok outcome)) :
    outcome.report = input.outcome.report := by
  have same := (prepare_source _ _ _ _ _ _ _ run).1
  rw [same]
  rfl

end LeanCage.Host.Publication
