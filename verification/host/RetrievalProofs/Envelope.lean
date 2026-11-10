import RetrievalProofs.Effects
import ArtifactsProofs.Report
import RetrievalProofs.Public

namespace LeanCage.Host.Retrieval

open Filesystem

structure EnvelopeBinding (bytes : ByteArray) (bundle : Validation.Bundle)
    (parent : Directories.Parent) (target : Directories.Opened) (value : Envelope) : Prop where
  decoded : ∃ fields, GatewayWire.decodeResponse bytes = .ok (0, .object fields) ∧
    stringField (.object fields) "schema" = .ok "leancage-publication-v1" ∧
    naturalField (.object fields) "device" (2^64 - 1) = .ok target.information.device ∧
    naturalField (.object fields) "inode" (2^64 - 1) = .ok target.information.inode ∧
    naturalField (.object fields) "parent_device" (2^64 - 1) = .ok parent.directory.information.device ∧
    naturalField (.object fields) "parent_inode" (2^64 - 1) = .ok parent.directory.information.inode ∧
    field (.object fields) "name" = some (.path parent.name) ∧
    stringField (.object fields) "policy_sha256" = .ok value.policyDigest ∧
    field (.object fields) "public" = some value.metadata ∧
    boolField (.object fields) "report_present" = .ok value.reportPresent ∧
    boolField (.object fields) "stored_present" = .ok value.storedPresent ∧
    boolField (.object fields) "manifest_present" = .ok value.manifestPresent ∧
    boolField (.object fields) "stdout_present" = .ok value.stdoutPresent ∧
    boolField (.object fields) "stderr_present" = .ok value.stderrPresent ∧
    readTerminal (.object fields) = .ok value.terminal
  outcome : publicOutcome bundle value.metadata = .ok value.outcome
  publicFields : PublicBinding bundle value.metadata value.outcome
  policy : Artifacts.digestText value.policyDigest = true
  complete : value.outcome.status = "complete" → value.reportPresent = true ∧ value.terminal.isSome = true
  incomplete : value.outcome.status ≠ "complete" →
    value.storedPresent = false ∧ value.manifestPresent = false ∧ value.stdoutPresent = false ∧
      value.stderrPresent = false ∧ value.terminal = none

-- §FS-host-boundary.publication: Decoding establishes the actual object and name binding.
theorem decodeEnvelope_binding (bytes : ByteArray) (bundle : Validation.Bundle)
    (parent : Directories.Parent) (target : Directories.Opened) (value : Envelope)
    (accepted : decodeEnvelope bytes bundle parent target = .ok value) :
    EnvelopeBinding bytes bundle parent target value := by
  unfold decodeEnvelope at accepted
  split at accepted
  · rename_i fields parsed
    obtain ⟨schema, schemaRead, accepted⟩ := Artifacts.except_bind_ok accepted
    obtain ⟨schemaCorrect, accepted⟩ := except_guard_next accepted
    obtain ⟨device, deviceRead, accepted⟩ := Artifacts.except_bind_ok accepted
    obtain ⟨inode, inodeRead, accepted⟩ := Artifacts.except_bind_ok accepted
    obtain ⟨parentDevice, parentDeviceRead, accepted⟩ := Artifacts.except_bind_ok accepted
    obtain ⟨parentInode, parentInodeRead, accepted⟩ := Artifacts.except_bind_ok accepted
    obtain ⟨objects, accepted⟩ := except_guard_next accepted
    split at accepted
    · rename_i name nameRead
      obtain ⟨nameCorrect, accepted⟩ := except_guard_next accepted
      obtain ⟨digest, digestRead, accepted⟩ := Artifacts.except_bind_ok accepted
      obtain ⟨digestCorrect, accepted⟩ := except_guard_next accepted
      split at accepted
      · rename_i publicFields publicRead
        obtain ⟨outcome, outcomeRead, accepted⟩ := Artifacts.except_bind_ok accepted
        obtain ⟨reportPresent, reportRead, accepted⟩ := Artifacts.except_bind_ok accepted
        obtain ⟨storedPresent, storedRead, accepted⟩ := Artifacts.except_bind_ok accepted
        obtain ⟨manifestPresent, manifestRead, accepted⟩ := Artifacts.except_bind_ok accepted
        obtain ⟨stdoutPresent, stdoutRead, accepted⟩ := Artifacts.except_bind_ok accepted
        obtain ⟨stderrPresent, stderrRead, accepted⟩ := Artifacts.except_bind_ok accepted
        obtain ⟨terminal, terminalRead, accepted⟩ := Artifacts.except_bind_ok accepted
        dsimp only at accepted
        have exactSchema : schema = "leancage-publication-v1" := by simpa using schemaCorrect
        have exactObjects : device = target.information.device ∧ inode = target.information.inode ∧
            parentDevice = parent.directory.information.device ∧
            parentInode = parent.directory.information.inode := by
          simpa [Bool.or_eq_true, and_assoc] using (Bool.eq_false_iff.mp objects)
        have exactName : name = parent.name := by simpa using nameCorrect
        have exactDigest : Artifacts.digestText digest = true := by simpa using digestCorrect
        have source : ∃ envelopeFields,
            GatewayWire.decodeResponse bytes = .ok (0, .object envelopeFields) ∧
            stringField (.object envelopeFields) "schema" = .ok "leancage-publication-v1" ∧
            naturalField (.object envelopeFields) "device" (2^64 - 1) = .ok target.information.device ∧
            naturalField (.object envelopeFields) "inode" (2^64 - 1) = .ok target.information.inode ∧
            naturalField (.object envelopeFields) "parent_device" (2^64 - 1) = .ok parent.directory.information.device ∧
            naturalField (.object envelopeFields) "parent_inode" (2^64 - 1) = .ok parent.directory.information.inode ∧
            field (.object envelopeFields) "name" = some (.path parent.name) ∧
            stringField (.object envelopeFields) "policy_sha256" = .ok digest ∧
            field (.object envelopeFields) "public" = some (.object publicFields) ∧
            boolField (.object envelopeFields) "report_present" = .ok reportPresent ∧
            boolField (.object envelopeFields) "stored_present" = .ok storedPresent ∧
            boolField (.object envelopeFields) "manifest_present" = .ok manifestPresent ∧
            boolField (.object envelopeFields) "stdout_present" = .ok stdoutPresent ∧
            boolField (.object envelopeFields) "stderr_present" = .ok stderrPresent ∧
            readTerminal (.object envelopeFields) = .ok terminal := by
          exact ⟨fields, parsed, exactSchema ▸ schemaRead,
            exactObjects.1 ▸ deviceRead, exactObjects.2.1 ▸ inodeRead,
            exactObjects.2.2.1 ▸ parentDeviceRead, exactObjects.2.2.2 ▸ parentInodeRead,
            exactName ▸ nameRead, digestRead, publicRead, reportRead, storedRead,
            manifestRead, stdoutRead, stderrRead, terminalRead⟩
        split at accepted
        · rename_i complete
          split at accepted
          · cases accepted
          · rename_i valid
            cases accepted
            exact ⟨source, outcomeRead, publicOutcome_binding _ _ _ outcomeRead, exactDigest,
              by intro _; simpa [Option.isSome_iff_ne_none] using valid,
              by intro different; exact False.elim (different (by simpa using complete))⟩
        · rename_i incomplete
          split at accepted
          · cases accepted
          · rename_i valid
            cases accepted
            exact ⟨source, outcomeRead, publicOutcome_binding _ _ _ outcomeRead, exactDigest,
              by intro same; exact False.elim (incomplete (by simpa using same)),
              by intro _; simpa [Bool.or_eq_true, and_assoc] using valid⟩
      · cases accepted
    · cases accepted
  · cases accepted

end LeanCage.Host.Retrieval
