import ArtifactsProofs.Composition

namespace LeanCage.Host.Artifacts

open Filesystem

def pathBytes (paths : List ExportPath) : Nat := (paths.map (fun path => path.text.toUTF8.size)).sum

theorem pathBytes_bound (paths : List ExportPath) : pathBytes paths ≤ 4095 * paths.length := by
  induction paths with
  | nil => simp [pathBytes]
  | cons path rest ih =>
    have bounded := path.valid.1
    simp only [pathBytes, List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one] at *
    omega

theorem export_path_bytes_bound (limits : Transport.Limits) (raw : ByteArray) (digest : String)
    (sources : List Transport.Blob) (events : List (Request × Reply)) (output : Export)
    (accepted : ExportValid limits raw digest sources events output) :
    pathBytes (output.files.map (·.path) ++ output.dirs ++ output.omitted) ≤ 4095 * limits.inodesMax := by
  have bound := pathBytes_bound (output.files.map (·.path) ++ output.dirs ++ output.omitted)
  have count : (output.files.map (·.path) ++ output.dirs ++ output.omitted).length ≤ limits.inodesMax := by
    simpa only [List.length_append, List.length_map] using accepted.inodeCount
  exact Nat.le_trans bound (Nat.mul_le_mul_left 4095 count)

theorem capture_getD_bound (entry : String) (count : Option Nat) (content : Option ByteArray) (limit : Nat)
    (accepted : captureConsistent entry count content limit = true) : (content.getD .empty).size ≤ limit := by
  cases content with
  | none => exact Nat.zero_le _
  | some bytes => exact capture_present_bound entry count bytes limit accepted

-- §FS-host-boundary.artifacts: Retained outputs have bounds derived from actual validation.
theorem validated_retained_bounds (expected : Expected) (received : Transport.Result)
    (events : List (Request × Reply)) (output : Validated)
    (run : Returns (validate expected received) events (.ok output)) :
    output.rawReport.size ≤ reportMax ∧ output.stdout.size ≤ expected.limits.stdoutMax ∧
      output.stderr.size ≤ expected.limits.stderrMax ∧ fileBytes output.files ≤ expected.limits.workspaceMax ∧
      output.files.length + output.dirs.length + output.omitted.length ≤ expected.limits.inodesMax ∧
      pathBytes (output.files.map (·.path) ++ output.dirs ++ output.omitted) ≤ 4095 * expected.limits.inodesMax := by
  have valid := validate_sound expected received events output run
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [valid.rawReport]
    exact (Json.parse_success valid.report.parsed).1
  · rw [valid.stdout]
    exact capture_getD_bound _ _ _ _ valid.report.control.stdout
  · rw [valid.stderr]
    exact capture_getD_bound _ _ _ _ valid.report.control.stderr
  · rcases valid.exported with absent | present
    · rcases absent with ⟨files, dirs, omitted, _⟩
      rw [files, dirs, omitted]
      simp only [fileBytes, pathBytes, List.map_nil, List.sum_nil, List.length_nil, List.nil_append, Nat.add_zero]
      exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
    · rcases present with ⟨exported, files, dirs, omitted, _, _, _, _, _, verified⟩
      rw [files, dirs, omitted]
      exact ⟨verified.bytes, verified.inodeCount, export_path_bytes_bound _ _ _ _ _ _ verified⟩

end LeanCage.Host.Artifacts
