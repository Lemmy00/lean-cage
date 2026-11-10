import PublicationProofs

namespace LeanCage.Host.Publication
open Filesystem

def CompletePreserved (input output : Outcome) : Prop :=
  output.status = "complete" → input.status = "complete" ∧
    output.stdout = input.stdout ∧ output.stderr = input.stderr ∧ output.files = input.files

theorem attempt_complete_preserved (bundle : Validation.Bundle) (input : Input)
    (target stdoutHash stderrHash : ByteArray) {events : List (Request × Reply)} {outcome : Outcome}
    (run : Returns (attempt bundle input target stdoutHash stderrHash) events (.ok outcome)) :
    CompletePreserved input.outcome outcome := by
  obtain ⟨display, _, _, _, _, _, _, _, _, _, _, _, _, prepared, _⟩ := attempt_source _ _ _ _ _ run
  rw [prepared.1]
  exact fun complete => ⟨complete, rfl, rfl, rfl⟩

-- §FS-host-boundary.artifacts: Publication cannot manufacture complete captures or exports.
theorem publish_complete_preserved (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (input : Input) {events : List (Request × Reply)} {output : Output}
    (run : Returns (publish request bundle input) events output) :
    CompletePreserved input.outcome output.outcome := by
  unfold publish at run
  obtain ⟨_, identified, _, _, afterIdentify, _⟩ := Snapshot.returns_bind_split _ _ run
  cases identified with
  | error hashingError =>
    obtain ⟨_, target, _, _, afterTarget, _⟩ := Snapshot.returns_bind_split _ _ afterIdentify
    cases target with
    | error =>
      obtain ⟨_, same⟩ := Snapshot.returns_pure_eq afterTarget
      cases same
      intro complete
      simp [invalidate, Outcome.storageFailure] at complete
    | ok target =>
      obtain ⟨_, published, _, attempted, final, _⟩ := Snapshot.returns_bind_split _ _ afterTarget
      obtain ⟨_, same⟩ := Snapshot.returns_pure_eq final
      cases same
      cases published with
      | error =>
        intro complete
        simp [invalidate, Outcome.storageFailure] at complete
      | ok outcome =>
        intro complete
        have earlier := attempt_complete_preserved bundle (invalidate input hashingError.message)
          target .empty .empty attempted complete
        simp [invalidate] at earlier
  | ok hashes =>
    rcases hashes with ⟨stdoutHash, stderrHash⟩
    obtain ⟨_, target, _, _, afterTarget, _⟩ := Snapshot.returns_bind_split _ _ afterIdentify
    cases target with
    | error =>
      obtain ⟨_, same⟩ := Snapshot.returns_pure_eq afterTarget
      cases same
      exact fun complete => ⟨complete, rfl, rfl, rfl⟩
    | ok target =>
      obtain ⟨_, published, _, attempted, final, _⟩ := Snapshot.returns_bind_split _ _ afterTarget
      obtain ⟨_, same⟩ := Snapshot.returns_pure_eq final
      cases same
      cases published with
      | error => exact fun complete => ⟨complete, rfl, rfl, rfl⟩
      | ok outcome => exact attempt_complete_preserved bundle input target stdoutHash stderrHash attempted

end LeanCage.Host.Publication
