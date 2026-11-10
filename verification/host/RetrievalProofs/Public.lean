import RetrievalProofs.Effects
import ArtifactsProofs.Report

namespace LeanCage.Host.Retrieval

open Filesystem

theorem naturalField_bound (value : GatewayWire.Value) (key : String) (maximum number : Nat)
    (accepted : naturalField value key maximum = .ok number) : number ≤ maximum := by
  unfold naturalField at accepted
  split at accepted
  · split at accepted
    · rename_i bounded
      cases accepted
      exact bounded
    · cases accepted
  · cases accepted

private theorem two_choices (value first second : String) (blocked : ¬(value ≠ first ∧ value ≠ second)) :
    value = first ∨ value = second := by
  by_cases same : value = first
  · exact .inl same
  · exact .inr (Classical.byContradiction (fun different => blocked ⟨same, different⟩))

structure PublicBinding (bundle : Validation.Bundle) (metadata : GatewayWire.Value) (outcome : Outcome) : Prop where
  schema : stringField metadata "schema" = .ok "leancage-workspace-v1"
  request : requestId outcome.requestId = true
  bundle : outcome.bundleId = bundle.identity
  command : outcome.command = "run" ∨ outcome.command = "check"
  status : outcome.status = "complete" ∨ outcome.status = "incomplete"
  exit : outcome.exitCode ≤ 255
  cleanup : outcome.vmCleanup = "complete" ∨ outcome.vmCleanup = "unknown" ∨ outcome.vmCleanup = "not_started"
  publication : outcome.publication = "stored" ∧ outcome.publicationError = none
  output : ∃ path, outcome.output = some path ∧ path.isEmpty = false ∧ rawPathValid path = true ∧ path[0]! = 47
  empty : outcome.report = none ∧ outcome.stdout = .empty ∧ outcome.stderr = .empty ∧ outcome.files = []

-- §FS-host-boundary.publication: Stored outer fields have checked schema, identity and bounds.
theorem publicOutcome_binding (bundle : Validation.Bundle) (metadata : GatewayWire.Value) (outcome : Outcome)
    (accepted : publicOutcome bundle metadata = .ok outcome) : PublicBinding bundle metadata outcome := by
  unfold publicOutcome at accepted
  obtain ⟨schema, schemaRead, accepted⟩ := Artifacts.except_bind_ok accepted
  obtain ⟨schemaCorrect, accepted⟩ := except_guard_next accepted
  obtain ⟨identity, identityRead, accepted⟩ := Artifacts.except_bind_ok accepted
  obtain ⟨bundleId, bundleRead, accepted⟩ := Artifacts.except_bind_ok accepted
  obtain ⟨command, commandRead, accepted⟩ := Artifacts.except_bind_ok accepted
  obtain ⟨status, statusRead, accepted⟩ := Artifacts.except_bind_ok accepted
  obtain ⟨identityCorrect, accepted⟩ := except_guard_next accepted
  obtain ⟨exitCode, exitRead, accepted⟩ := Artifacts.except_bind_ok accepted
  obtain ⟨cleanup, cleanupRead, accepted⟩ := Artifacts.except_bind_ok accepted
  obtain ⟨cleanupCorrect, accepted⟩ := except_guard_next accepted
  obtain ⟨error, errorRead, accepted⟩ := Artifacts.except_bind_ok accepted
  obtain ⟨publication, publicationRead, accepted⟩ := Artifacts.except_bind_ok accepted
  obtain ⟨publicationError, publicationErrorRead, accepted⟩ := Artifacts.except_bind_ok accepted
  obtain ⟨publicationCorrect, accepted⟩ := except_guard_next accepted
  split at accepted
  · rename_i path pathRead
    obtain ⟨pathCorrect, accepted⟩ := except_guard_next accepted
    cases accepted
    have exactSchema : schema = "leancage-workspace-v1" := by simpa using schemaCorrect
    have identityFields : requestId identity = true ∧ bundleId = bundle.identity ∧
        ¬(command ≠ "run" ∧ command ≠ "check") ∧
        ¬(status ≠ "complete" ∧ status ≠ "incomplete") := by
      simpa [Bool.or_eq_true, Bool.and_eq_true, and_assoc] using Bool.eq_false_iff.mp identityCorrect
    have cleanupBlocked : ¬(cleanup ≠ "complete" ∧ cleanup ≠ "unknown" ∧ cleanup ≠ "not_started") := by
      simpa [Bool.and_eq_true, and_assoc] using Bool.eq_false_iff.mp cleanupCorrect
    have cleanupFields : cleanup = "complete" ∨ cleanup = "unknown" ∨ cleanup = "not_started" := by
      by_cases first : cleanup = "complete"
      · exact .inl first
      · by_cases second : cleanup = "unknown"
        · exact .inr (.inl second)
        · exact .inr (.inr (Classical.byContradiction
            (fun last => cleanupBlocked ⟨first, second, last⟩)))
    have pathFields : path.isEmpty = false ∧ rawPathValid path = true ∧ path[0]! = 47 := by
      simpa [Bool.or_eq_true, and_assoc] using Bool.eq_false_iff.mp pathCorrect
    exact ⟨exactSchema ▸ schemaRead, identityFields.1, identityFields.2.1,
      two_choices _ _ _ identityFields.2.2.1, two_choices _ _ _ identityFields.2.2.2,
      naturalField_bound _ _ _ _ exitRead, cleanupFields, ⟨rfl, rfl⟩,
      ⟨path, rfl, pathFields⟩, ⟨rfl, rfl, rfl, rfl⟩⟩
  · cases accepted

end LeanCage.Host.Retrieval
