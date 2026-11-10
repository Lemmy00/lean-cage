import ArtifactsProofs.Effects
import JsonProofs

namespace LeanCage.Host.Artifacts

open Filesystem

theorem except_bind_ok {ε α β : Type} {first : Except ε α} {next : α → Except ε β} {answer : β}
    (accepted : (first.bind next) = .ok answer) :
    ∃ value, first = .ok value ∧ next value = .ok answer := by
  cases first with
  | error error => contradiction
  | ok value => exact ⟨value, rfl, accepted⟩

structure ReportDecoded (expected : Expected) (value : Json.Value) (report : Report) : Prop where
  runId : readNatural value "run_id" 1 = .ok report.runId
  stage : readNatural value "stage" 9 = .ok report.stage
  detail : readNatural value "detail" 4095 = .ok report.detail
  uid : readNatural value "uid" 100999 = .ok report.uid
  cancellationBits : readNatural value "cancellation_bits" 63 = .ok report.cancellationBits
  exportErrno : readNatural value "export_errno" 4095 = .ok report.exportErrno
  exportOmitted : readNatural value "export_omitted" expected.limits.inodesMax = .ok report.exportOmitted
  entry : readString value "entry" = .ok report.entry
  cleanup : readString value "cleanup" = .ok report.cleanup
  termination : readString value "termination" = .ok report.termination
  storage : readString value "report_storage" = .ok report.storage
  storageError : readOptionalString value "report_storage_error" = .ok report.storageError
  exportState : readString value "export" = .ok report.exportState
  exportDigest : readOptionalString value "export_digest" = .ok report.exportDigest
  stdoutCaptured : readOptionalNatural value "stdout_captured_bytes" expected.limits.stdoutMax = .ok report.stdoutCaptured
  stderrCaptured : readOptionalNatural value "stderr_captured_bytes" expected.limits.stderrMax = .ok report.stderrCaptured
  stdoutObserved : readOptionalNatural value "stdout_bytes" (2^64 - 1) = .ok report.stdoutObserved
  stderrObserved : readOptionalNatural value "stderr_bytes" (2^64 - 1) = .ok report.stderrObserved
  stdoutTruncated : readOptionalBool value "stdout_truncated" = .ok report.stdoutTruncated
  stderrTruncated : readOptionalBool value "stderr_truncated" = .ok report.stderrTruncated

-- §FS-host-boundary.artifacts: Typed fields come from the same actual parsed object.
theorem reportFields_decoded (expected : Expected) (value : Json.Value) (report : Report)
    (accepted : reportFields expected value = .ok report) : ReportDecoded expected value report := by
  unfold reportFields at accepted
  obtain ⟨runId, runIdRead, accepted⟩ := except_bind_ok accepted
  obtain ⟨stage, stageRead, accepted⟩ := except_bind_ok accepted
  obtain ⟨detail, detailRead, accepted⟩ := except_bind_ok accepted
  obtain ⟨uid, uidRead, accepted⟩ := except_bind_ok accepted
  obtain ⟨cancellationBits, cancellationRead, accepted⟩ := except_bind_ok accepted
  obtain ⟨exportErrno, errnoRead, accepted⟩ := except_bind_ok accepted
  obtain ⟨exportOmitted, omittedRead, accepted⟩ := except_bind_ok accepted
  obtain ⟨entry, entryRead, accepted⟩ := except_bind_ok accepted
  obtain ⟨cleanup, cleanupRead, accepted⟩ := except_bind_ok accepted
  obtain ⟨termination, terminationRead, accepted⟩ := except_bind_ok accepted
  obtain ⟨storage, storageRead, accepted⟩ := except_bind_ok accepted
  obtain ⟨storageError, storageErrorRead, accepted⟩ := except_bind_ok accepted
  obtain ⟨exportState, exportRead, accepted⟩ := except_bind_ok accepted
  obtain ⟨exportDigest, exportDigestRead, accepted⟩ := except_bind_ok accepted
  obtain ⟨stdoutCaptured, stdoutRead, accepted⟩ := except_bind_ok accepted
  obtain ⟨stderrCaptured, stderrRead, accepted⟩ := except_bind_ok accepted
  obtain ⟨stdoutObserved, stdoutObservedRead, accepted⟩ := except_bind_ok accepted
  obtain ⟨stderrObserved, stderrObservedRead, accepted⟩ := except_bind_ok accepted
  obtain ⟨stdoutTruncated, stdoutTruncatedRead, accepted⟩ := except_bind_ok accepted
  obtain ⟨stderrTruncated, stderrTruncatedRead, accepted⟩ := except_bind_ok accepted
  cases accepted
  exact ⟨runIdRead, stageRead, detailRead, uidRead, cancellationRead, errnoRead, omittedRead, entryRead,
    cleanupRead, terminationRead, storageRead, storageErrorRead, exportRead, exportDigestRead,
    stdoutRead, stderrRead, stdoutObservedRead, stderrObservedRead, stdoutTruncatedRead, stderrTruncatedRead⟩

theorem readNatural_bounded (value : Json.Value) (key : String) (maximum number : Nat)
    (accepted : readNatural value key maximum = .ok number) :
    (Json.get? value key).bind (fun field => Json.naturalBelow? field maximum) = some number ∧ number ≤ maximum := by
  unfold readNatural at accepted
  cases selected : (Json.get? value key).bind (fun field => Json.naturalBelow? field maximum) with
  | none => simp [selected] at accepted
  | some actual =>
    simp only [selected, Except.ok.injEq] at accepted
    subst actual
    rcases Option.bind_eq_some_iff.mp selected with ⟨field, _, parsed⟩
    exact ⟨rfl, (Json.naturalBelow_exact field maximum number).mp parsed |>.2⟩

theorem readOptionalNatural_bounded (value : Json.Value) (key : String) (maximum : Nat) (number : Option Nat)
    (accepted : readOptionalNatural value key maximum = .ok number) : ∀ count ∈ number, count ≤ maximum := by
  unfold readOptionalNatural at accepted
  cases selected : Json.get? value key with
  | none => simp [selected] at accepted
  | some field =>
    cases field with
    | null => simp only [selected, Except.ok.injEq] at accepted; cases accepted; simp
    | bool boolean => simp [selected, Json.naturalBelow?] at accepted
    | string text => simp [selected, Json.naturalBelow?] at accepted
    | array values => simp [selected, Json.naturalBelow?] at accepted
    | object fields => simp [selected, Json.naturalBelow?] at accepted
    | number bytes =>
      simp only [selected] at accepted
      cases parsed : Json.naturalBelow? (.number bytes) maximum with
      | none => simp [parsed] at accepted
      | some count =>
        simp only [parsed, Except.ok.injEq] at accepted
        cases accepted
        intro actual member
        have equal : actual = count := by simpa [eq_comm] using member
        subst actual
        exact (Json.naturalBelow_exact _ maximum count).mp parsed |>.2

structure ControlValid (expected : Expected) (received : Transport.Result) (report : Report) : Prop where
  kind : report.kindValid expected = true
  exportState : report.exportValid = true
  storage : report.storageValid expected = true
  transportError : received.terminal.error = 0
  controller : received.terminal.controller ≤ 255
  retrieved : received.terminal.retrieved ≤ 255
  extinct : received.terminal.extinct ≤ 1
  cleanup : report.cleanup = "complete" → received.terminal.extinct = 1
  stdout : captureConsistent report.entry report.stdoutCaptured received.stdout expected.limits.stdoutMax = true
  stderr : captureConsistent report.entry report.stderrCaptured received.stderr expected.limits.stderrMax = true
  stdoutObserved : observedConsistent report.stdoutObserved report.stdoutCaptured report.stdoutTruncated
    expected.limits.stdoutMax = true
  stderrObserved : observedConsistent report.stderrObserved report.stderrCaptured report.stderrTruncated
    expected.limits.stderrMax = true
  unallocated : expected.preflight = true ∨ report.runId = 0 →
    noArtifacts received = true ∧ received.terminal.retrieved = 126 ∧ report.exportState ≠ "complete"
  stored : expected.preflight = false → report.runId ≠ 0 → report.storage = "stored" →
    received.terminal.retrieved = 0 ∧ received.stored = some received.report
  failedStorage : expected.preflight = false → report.runId ≠ 0 → report.storage ≠ "stored" →
    received.terminal.retrieved ≠ 0 ∧ received.stored = none
  committed : expected.preflight = false → report.runId ≠ 0 → report.exportState = "complete" →
    received.manifest.isSome = true
  uncommitted : expected.preflight = false → report.runId ≠ 0 → report.exportState ≠ "complete" →
    received.manifest = none ∧ received.blobs = []

set_option maxHeartbeats 3000000 in
theorem checkControl_sound (expected : Expected) (received : Transport.Result) (report : Report)
    (accepted : checkControl expected received report = .ok ()) : ControlValid expected received report := by
  unfold checkControl at accepted
  simp only [bind, Except.bind] at accepted
  repeat' (split at accepted <;> (try simp only [bind, Except.bind] at accepted) <;> try contradiction)
  all_goals
    constructor <;> grind [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none, List.isEmpty_iff]

structure ReportValid (expected : Expected) (received : Transport.Result) (value : Json.Value) (report : Report) : Prop where
  limits : expected.limits.Valid
  parsed : Json.parse received.report reportMax = .ok value
  recognized : Artifacts.recognized expected.preflight value = true
  profile : stringField value "profile" = some expected.profile
  runtime : stringField value "runtime_manifest_digest" = some expected.runtimeDigest
  decoded : ReportDecoded expected value report
  control : ControlValid expected received report

-- §FS-host-boundary.artifacts: Schema, profile and typed fields belong to these same raw bytes.
theorem checkReport_sound (expected : Expected) (received : Transport.Result) (value : Json.Value) (report : Report)
    (accepted : checkReport expected received = .ok (value, report)) : ReportValid expected received value report := by
  unfold checkReport at accepted
  simp only [bind, Except.bind] at accepted
  split at accepted
  · contradiction
  · rename_i limits
    cases parsed : Json.parse received.report reportMax with
    | error error => simp [parsed, Except.mapError] at accepted
    | ok actual =>
      simp only [parsed, Except.mapError] at accepted
      split at accepted
      · contradiction
      · rename_i identity
        obtain ⟨fields, read, accepted⟩ := except_bind_ok accepted
        obtain ⟨token, control, accepted⟩ := except_bind_ok accepted
        cases token
        cases accepted
        refine ⟨?_, parsed, ?_, ?_, ?_, reportFields_decoded expected value report read,
          checkControl_sound expected received report control⟩
        · have trueLimits : expected.limits.valid = true := by simpa using limits
          exact of_decide_eq_true trueLimits
        all_goals grind

theorem report_run0_entry (expected : Expected) (report : Report) (valid : report.kindValid expected = true)
    (unallocated : report.runId = 0) : report.entry = "no" := by
  apply Classical.byContradiction
  intro different
  have absent : (report.entry == "no") = false := by simp [different]
  simp only [Report.kindValid, unallocated, beq_self_eq_true, ite_true, absent,
    Bool.and_false, Bool.false_and] at valid
  contradiction

theorem report_preflight_entry (expected : Expected) (report : Report) (valid : report.kindValid expected = true)
    (preflight : expected.preflight = true) : report.entry = "no" := by
  apply Classical.byContradiction
  intro different
  have absent : (report.entry == "no") = false := by simp [different]
  simp only [Report.kindValid, preflight, ite_true, absent, Bool.false_and, Bool.and_false] at valid
  contradiction

theorem noArtifacts_fields (received : Transport.Result) (absent : noArtifacts received = true) :
    received.stored = none ∧ received.stdout = none ∧ received.stderr = none ∧
      received.manifest = none ∧ received.blobs = [] := by
  simpa only [noArtifacts, Bool.and_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff, and_assoc] using absent

theorem capture_present_bound (entry : String) (count : Option Nat) (bytes : ByteArray) (limit : Nat)
    (valid : captureConsistent entry count (some bytes) limit = true) : bytes.size ≤ limit := by
  simp only [captureConsistent, Option.all_some, Bool.and_eq_true, decide_eq_true_eq] at valid
  exact valid.1

theorem capture_known_present (entry : String) (count : Nat) (bytes : ByteArray) (limit : Nat)
    (valid : captureConsistent entry (some count) (some bytes) limit = true) : bytes.size = count := by
  simp only [captureConsistent, Option.all_some, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at valid
  exact valid.2

theorem capture_known_absent (entry : String) (count limit : Nat)
    (valid : captureConsistent entry (some count) none limit = true) : count = 0 ∧ entry ≠ "yes" := by
  simpa [captureConsistent] using valid

theorem knownReport_preserved (preflight : Bool) (raw : ByteArray) (value : Json.Value)
    (known : knownReport preflight raw = some value) :
    Json.parse raw reportMax = .ok value ∧ recognized preflight value = true := by
  unfold knownReport at known
  cases parsed : Json.parse raw reportMax with
  | error error => simp [parsed] at known
  | ok actual =>
    simp only [parsed] at known
    split at known
    · rename_i recognized
      cases known
      exact ⟨rfl, recognized⟩
    · contradiction

end LeanCage.Host.Artifacts
