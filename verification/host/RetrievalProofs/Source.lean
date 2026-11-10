import RetrievalProofs.Stored

namespace LeanCage.Host.Retrieval

open Filesystem

def DestinationObservation (bundle : Validation.Bundle) (path : ByteArray) (identity : Option String)
    (events : List (Request × Reply)) (answer : GatewayWire.Value) : Prop :=
  ∃ parent target ancestors opening content targetClose parentClose,
    events = ancestors ++ opening ++ content ++ targetClose ++ parentClose ∧
    Returns (Directories.parent path false) ancestors (.ok parent) ∧
    Returns (Directories.publicAt parent.uid parent.directory.fd parent.name false) opening (.ok target) ∧
    StoredObservation bundle parent target identity content answer ∧
    Returns (closeResult target.fd (.ok answer)) targetClose (.ok answer) ∧
    Returns (closeResult parent.directory.fd (.ok answer)) parentClose (.ok answer)

-- §FS-host-boundary.publication: Same retained ancestry, target and content precede both closes.
theorem atDestination_source (bundle : Validation.Bundle) (path : ByteArray) (identity : Option String)
    {events : List (Request × Reply)} {answer : GatewayWire.Value}
    (run : Returns (atDestination bundle path identity) events (.ok answer)) :
    DestinationObservation bundle path identity events answer := by
  unfold atDestination at run
  obtain ⟨ancestors, parentResult, last, parentRun, afterParent, shape⟩ := Snapshot.returns_bind_split _ _ run
  cases parentResult with
  | error => cases afterParent
  | ok parent =>
    obtain ⟨opening, targetResult, rest, targetRun, afterTarget, targetShape⟩ :=
      Snapshot.returns_bind_split _ _ afterParent
    cases targetResult with
    | error =>
      have impossible := (Snapshot.closeResult_provenance _ _ afterTarget).1
      cases impossible
    | ok target =>
      obtain ⟨content, observed, finalEvents, storedRun, afterStored, storedShape⟩ :=
        Snapshot.returns_bind_split _ _ afterTarget
      obtain ⟨targetClose, closed, parentClose, targetCloseRun, parentCloseRun, closeShape⟩ :=
        Snapshot.returns_bind_split _ _ afterStored
      have closedValue := (Snapshot.closeResult_provenance _ _ parentCloseRun).1
      cases closedValue
      have observedValue := (Snapshot.closeResult_provenance _ _ targetCloseRun).1
      cases observedValue
      exact ⟨parent, target, ancestors, opening, content, targetClose, parentClose,
        by simpa only [targetShape, storedShape, closeShape, List.append_assoc] using shape,
        parentRun, targetRun, readStored_source _ _ _ _ storedRun, targetCloseRun, parentCloseRun⟩

def ReportObservation (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (events : List (Request × Reply)) (answer : GatewayWire.Value) : Prop :=
  request.valid = true ∧ request.command = GatewayWire.reportCommand ∧
    ∃ path identity selection selected,
      events = selection ++ selected ∧
      Returns (destination request bundle) selection (.ok (path, identity)) ∧
      DestinationObservation bundle path identity selected answer

-- §FS-host-boundary.publication: The real public request selects every subsequent read and check.
theorem report_source (request : GatewayWire.Request) (bundle : Validation.Bundle)
    {events : List (Request × Reply)} {answer : GatewayWire.Value}
    (run : Returns (report request bundle) events (.ok answer)) :
    ReportObservation request bundle events answer := by
  unfold report at run
  split at run
  · cases run
  · rename_i caller
    have requestValid : request.valid = true ∧ request.command = GatewayWire.reportCommand := by
      simpa [Bool.or_eq_true] using caller
    obtain ⟨selection, result, selected, destinationRun, final, shape⟩ := Snapshot.returns_bind_split _ _ run
    cases result with
    | error => cases final
    | ok choice =>
      exact ⟨requestValid.1, requestValid.2, choice.1, choice.2, selection, selected, shape,
        destinationRun, atDestination_source _ _ _ final⟩

end LeanCage.Host.Retrieval
