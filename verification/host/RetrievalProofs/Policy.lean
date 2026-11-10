import RetrievalProofs.Files
import ArtifactsProofs.Report

namespace LeanCage.Host.Retrieval

open Filesystem

theorem mapError_ok {ε δ α : Type} (source : Except ε α) (map : ε → δ) {value : α}
    (accepted : source.mapError map = .ok value) : source = .ok value := by
  cases source with
  | error => cases accepted
  | ok actual => cases accepted; rfl

theorem boundedNatural_bound (value : Json.Value) (key : String) (maximum count : Nat)
    (accepted : Policy.boundedNatural value key maximum = some count) : count ≤ maximum := by
  obtain ⟨field, _, parsed⟩ := Option.bind_eq_some_iff.mp accepted
  exact (Json.naturalBelow_exact field maximum count).mp parsed |>.2

structure PolicySupported (value : Json.Value) (raw : ByteArray) (policy : Policy.Accepted) : Prop where
  valueExact : policy.value = value
  rawExact : policy.raw = raw
  transport : policy.transport.Valid
  snapshot : policy.snapshot.supported = true
  wallPositive : 0 < policy.wallMilliseconds
  wallBound : policy.wallMilliseconds ≤ 3600000
  bytesBound : raw.size ≤ reportMax

-- §FS-host-boundary.publication: Retrieval derives supported budgets from these exact policy bytes.
theorem budgets_supported (value : Json.Value) (raw : ByteArray) (policy : Policy.Accepted)
    (accepted : Policy.budgets value raw = .ok policy) : PolicySupported value raw policy := by
  unfold Policy.budgets at accepted
  split at accepted
  · rename_i limits limitsRead
    split at accepted
    · rename_i stdout stdoutRead
      split at accepted
      · rename_i stderr stderrRead
        split at accepted
        · rename_i workspace workspaceRead
          split at accepted
          · rename_i inodes inodeRead
            split at accepted
            · rename_i stdin stdinRead
              split at accepted
              · rename_i wall wallRead
                dsimp only at accepted
                split at accepted
                · cases accepted
                · rename_i supported
                  cases accepted
                  have bounds : (Transport.Limits.mk stdout stderr workspace inodes).valid = true ∧
                      (Snapshot.Limits.mk workspace inodes stdin).supported = true ∧ wall ≠ 0 ∧ raw.size ≤ reportMax := by
                    simpa [Bool.or_eq_true, and_assoc] using supported
                  exact ⟨rfl, rfl, of_decide_eq_true bounds.1, bounds.2.1,
                    Nat.pos_of_ne_zero bounds.2.2.1, boundedNatural_bound _ _ _ _ wallRead, bounds.2.2.2⟩
              · cases accepted
            · cases accepted
          · cases accepted
        · cases accepted
      · cases accepted
    · cases accepted
  · cases accepted

def PolicyObservation (bundle : Validation.Bundle) (target : UInt64) (envelope : Envelope)
    (events : List (Request × Reply)) (policy : Policy.Accepted) : Prop :=
  ∃ raw digest value copied copies hashes,
    events = copies ++ hashes ∧
    Snapshot.OpenedCopy target "policy.json".toUTF8 copies copied ∧ copied.bytes = raw ∧
    raw.size ≤ reportMax ∧ Returns (Filesystem.hash raw) hashes (.ok digest) ∧
    Snapshot.hex digest = envelope.policyDigest ∧
    Json.parse raw reportMax = .ok value ∧ Policy.budgets value raw = .ok policy ∧
    Validation.stringField policy.value "profile" = Validation.stringField bundle.manifest "profile" ∧
    Validation.stringField policy.value "runtime_manifest_digest" =
      Validation.stringField bundle.manifest "runtime_manifest_digest"

-- §FS-host-boundary.publication: The copied policy hash, parsed bytes and actual budgets agree.
theorem storedPolicy_source (bundle : Validation.Bundle) (target : UInt64) (envelope : Envelope)
    {events : List (Request × Reply)} {policy : Policy.Accepted}
    (run : Returns (storedPolicy bundle target envelope).run events (.ok policy)) :
    PolicyObservation bundle target envelope events policy := by
  unfold storedPolicy at run
  obtain ⟨copies, raw, last, read, afterRead, shape⟩ := checked_bind_split run
  obtain ⟨hashes, digest, tailEvents, hashRun, afterHash, hashShape⟩ := checked_bind_split afterRead
  split at afterHash
  · cases afterHash
  · rename_i digestCorrect
    obtain ⟨parseEvents, value, budgetEvents, parsed, afterParse, parseShape⟩ := checked_bind_split afterHash
    obtain ⟨rfl, parseValue⟩ := checked_result _ parsed
    obtain ⟨budgetEvents, actual, finalEvents, budgeted, final, budgetShape⟩ := checked_bind_split afterParse
    obtain ⟨rfl, budgetValue⟩ := checked_result _ budgeted
    split at final
    · cases final
    · rename_i profile
      obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
      cases same
      obtain ⟨bounded, copied, source, bytes⟩ := readFile_source _ _ _ read
      have digested : Snapshot.hex digest = envelope.policyDigest := by simpa using digestCorrect
      have identity :
          Validation.stringField policy.value "profile" = Validation.stringField bundle.manifest "profile" ∧
          Validation.stringField policy.value "runtime_manifest_digest" =
            Validation.stringField bundle.manifest "runtime_manifest_digest" := by
        simpa [Bool.or_eq_true] using profile
      exact ⟨raw, digest, value, copied, copies, hashes,
        by simpa only [hashShape, parseShape, budgetShape, List.nil_append, List.append_nil] using shape,
        source, bytes, bounded, hashRun, digested,
        mapError_ok _ _ parseValue, mapError_ok _ _ budgetValue, identity.1, identity.2⟩

end LeanCage.Host.Retrieval
