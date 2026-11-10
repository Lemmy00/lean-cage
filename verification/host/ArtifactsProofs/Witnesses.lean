import ArtifactsProofs.Fixtures

namespace LeanCage.Host.Artifacts.Witness

open Filesystem

set_option cbv.maxSteps 2000000
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

-- §FS-host-boundary.acceptance: A useful export, including root .tmp, runs the real validator.
theorem useful_program_completes :
    success (replay hashReplies (validateExport limits manifest manifestKey 1 received.blobs)) = true := by decide +kernel

theorem useful_actual_export :
    ∃ events output, Returns (validateExport limits manifest manifestKey 1 received.blobs) events (.ok output) ∧
      ExportValid limits manifest manifestKey received.blobs events output := by
  have computed := useful_program_completes
  cases result : replay hashReplies (validateExport limits manifest manifestKey 1 received.blobs) with
  | none => simp [result, success] at computed
  | some value =>
    cases value with
    | error error => simp [result, success] at computed
    | ok output =>
      obtain ⟨events, run⟩ := replay_returns hashReplies
        (validateExport limits manifest manifestKey 1 received.blobs) (.ok output) result
      exact ⟨events, output, run, validateExport_sound limits manifest manifestKey 1 received.blobs events output run⟩

-- §FS-host-boundary.acceptance: One actual full report and export inhabit the complete validator.
theorem useful_full_completes : success (replay hashReplies (validate expected received)) = true := by decide +kernel

theorem useful_actual_validation :
    ∃ events output, Returns (validate expected received) events (.ok output) ∧
      ArtifactsValid expected received events output := by
  have computed := useful_full_completes
  cases result : replay hashReplies (validate expected received) with
  | none => simp [result, success] at computed
  | some value =>
    cases value with
    | error error => simp [result, success] at computed
    | ok output =>
      obtain ⟨events, run⟩ := replay_returns hashReplies (validate expected received) (.ok output) result
      exact ⟨events, output, run, validate_sound expected received events output run⟩

theorem invalid_hash_rejected :
    failure (replay [(0, .empty)] (validateExport limits manifest manifestKey 1 received.blobs)) = true := by decide +kernel

theorem omitted_count_rejected :
    failure (replay [(0, rawDigest manifestKey)] (validateExport limits manifest manifestKey 0 received.blobs)) = true := by decide +kernel

theorem missing_blob_rejected :
    failure (replay [(0, rawDigest manifestKey)] (validateExport limits manifest manifestKey 1 [])) = true := by decide +kernel

def rejected {α : Type} : Filesystem.Result α → Bool
  | .error _ => true
  | .ok _ => false

theorem duplicate_path_rejected :
    rejected (parseManifest limits "LCEXPORT1\nD 61\nO 61\n".toUTF8) = true := by decide +kernel

theorem missing_parent_rejected :
    rejected (parseManifest limits "LCEXPORT1\nO 612f62\n".toUTF8) = true := by decide +kernel

theorem conflicting_parent_rejected :
    rejected (parseManifest limits "LCEXPORT1\nO 61\nD 612f62\n".toUTF8) = true := by decide +kernel

theorem leading_zero_rejected :
    rejected (parseManifest limits ("LCEXPORT1\nF 0 61 03 " ++ contentKey ++ "\n").toUTF8) = true := by decide +kernel

theorem invalid_utf8_rejected : rejected (decodePath "ff".toUTF8) = true := by decide +kernel
theorem traversal_rejected : rejected (decodePath "2e2e2f61".toUTF8) = true := by decide +kernel
theorem uppercase_hex_rejected : rejected (decodePath "2E746d70".toUTF8) = true := by decide +kernel

end LeanCage.Host.Artifacts.Witness
