import PublicationProofs.Prefix

namespace LeanCage.Host.Publication

open Filesystem

-- §FS-host-boundary.publication: Every storage or hash error retains the recognized input report.
set_option maxHeartbeats 1000000 in
theorem publish_report (request : GatewayWire.Request) (bundle : Validation.Bundle) (input : Input)
    {events : List (Request × Reply)} {output : Output}
    (run : Returns (publish request bundle input) events output) :
    output.outcome.report = input.outcome.report := by
  unfold publish at run
  obtain ⟨_, identified, _, _, afterIdentify, _⟩ := Snapshot.returns_bind_split _ _ run
  cases identified with
  | error hashingError =>
    obtain ⟨_, target, _, _, afterTarget, _⟩ := Snapshot.returns_bind_split _ _ afterIdentify
    cases target with
    | error =>
      obtain ⟨_, same⟩ := Snapshot.returns_pure_eq afterTarget
      cases same
      rfl
    | ok target =>
      obtain ⟨_, published, _, attempted, final, _⟩ := Snapshot.returns_bind_split _ _ afterTarget
      obtain ⟨_, same⟩ := Snapshot.returns_pure_eq final
      cases same
      cases published with
      | error => rfl
      | ok outcome =>
        exact attempt_report bundle (invalidate input hashingError.message) target .empty .empty attempted
  | ok hashes =>
    rcases hashes with ⟨stdoutHash, stderrHash⟩
    obtain ⟨_, target, _, _, afterTarget, _⟩ := Snapshot.returns_bind_split _ _ afterIdentify
    cases target with
    | error =>
      obtain ⟨_, same⟩ := Snapshot.returns_pure_eq afterTarget
      cases same
      rfl
    | ok target =>
      obtain ⟨_, published, _, attempted, final, _⟩ := Snapshot.returns_bind_split _ _ afterTarget
      obtain ⟨_, same⟩ := Snapshot.returns_pure_eq final
      cases same
      cases published with
      | error => rfl
      | ok outcome => exact attempt_report bundle input target stdoutHash stderrHash attempted

-- §FS-host-boundary.publication: Failed publication changes outer storage status, not inner report.
theorem storageFailure_fields (outcome : Outcome) (error : String) :
    (outcome.storageFailure error).report = outcome.report ∧
    (outcome.storageFailure error).publication = "failed" ∧
    (outcome.storageFailure error).output = none ∧
    (outcome.storageFailure error).exitCode = 126 := ⟨rfl, rfl, rfl, rfl⟩

end LeanCage.Host.Publication
