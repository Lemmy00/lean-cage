import ApplicationProofs
import ArtifactsProofs

namespace LeanCage.Host.ReceiveProofs
open Filesystem

theorem expected_source (bundle : Validation.Bundle) (preflight : Bool)
    (limits : Transport.Limits) (value : Artifacts.Expected)
    (accepted : expected bundle preflight limits = .ok value) :
    value.preflight = preflight ∧ value.limits = limits ∧
      Validation.stringField bundle.manifest "profile" = some value.profile ∧
      Validation.stringField bundle.manifest "runtime_manifest_digest" = some value.runtimeDigest := by
  unfold expected at accepted
  repeat' first | split at accepted | cases accepted
  all_goals exact ⟨rfl, rfl, by assumption, by assumption⟩

-- §FS-host-boundary.artifacts: Completion names the same decoder and actual validation calls.
structure Complete (request : String) (bundle : Validation.Bundle) (preflight : Bool)
    (policy : Policy.Accepted) (vm : VirtualMachine.Result)
    (events : List (Request × Reply)) (input : Publication.Input) where
  transport : Transport.Result
  expectation : Artifacts.Expected
  validated : Artifacts.Validated
  vmError : vm.error = none
  finish : vm.transport.finish = .ok transport
  expected : expected bundle preflight policy.transport = .ok expectation
  validation : Returns (Artifacts.validate expectation transport) events (.ok validated)
  valid : Artifacts.ArtifactsValid expectation transport events validated
  policySame : input.policy = policy
  received : input.received = some transport
  checked : input.validated = some validated
  boot : input.boot = vm.boot
  raw : input.rawReport = vm.transport.report?
  requestId : input.outcome.requestId = request
  bundleId : input.outcome.bundleId = bundle.identity
  report : input.outcome.report = some validated.report
  stdout : input.outcome.stdout = validated.stdout
  stderr : input.outcome.stderr = validated.stderr
  files : input.outcome.files = validated.files
  exitCode : input.outcome.exitCode = transport.terminal.controller

-- §FS-host-boundary.acceptance: A complete public candidate is produced by actual checking.
theorem receive_complete (request : String) (bundle : Validation.Bundle) (preflight : Bool)
    (policy : Policy.Accepted) (vm : VirtualMachine.Result)
    {events : List (Request × Reply)} {input : Publication.Input}
    (run : Returns (receive request bundle preflight policy vm) events input)
    (complete : input.outcome.status = "complete") :
    Nonempty (Complete request bundle preflight policy vm events input) := by
  unfold receive at run
  dsimp only at run
  split at run
  · obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq run
    cases same
    simp [incomplete] at complete
  · rename_i noError
    cases finished : vm.transport.finish with
    | error error =>
      simp only [finished] at run
      obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq run
      cases same
      simp [incomplete] at complete
    | ok transport =>
      simp only [finished] at run
      cases expectation : expected bundle preflight policy.transport with
      | error error =>
        simp only [expectation] at run
        obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq run
        cases same
        simp [incomplete] at complete
      | ok expectationValue =>
        simp only [expectation] at run
        obtain ⟨checking, result, last, validation, final, shape⟩ :=
          Snapshot.returns_bind_split _ _ run
        cases result with
        | error error =>
          obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
          cases same
          simp [incomplete] at complete
        | ok validated =>
          obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
          cases same
          simp only [List.append_nil] at shape
          subst events
          have noError : vm.error = none := by simpa using noError
          exact ⟨⟨transport, expectationValue, validated, noError, finished, expectation,
            validation, Artifacts.validate_sound _ _ _ _ validation,
            rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

-- §FS-host-boundary.artifacts: The caller's bounds govern the actual complete returned bytes.
theorem receive_bounds (request : String) (bundle : Validation.Bundle) (preflight : Bool)
    (policy : Policy.Accepted) (vm : VirtualMachine.Result)
    {events : List (Request × Reply)} {input : Publication.Input}
    (run : Returns (receive request bundle preflight policy vm) events input)
    (complete : input.outcome.status = "complete") :
    input.outcome.stdout.size ≤ policy.transport.stdoutMax ∧
      input.outcome.stderr.size ≤ policy.transport.stderrMax ∧
      Artifacts.fileBytes input.outcome.files ≤ policy.transport.workspaceMax ∧
      input.outcome.files.length ≤ policy.transport.inodesMax := by
  obtain ⟨source⟩ := receive_complete request bundle preflight policy vm run complete
  have limits := (expected_source bundle preflight policy.transport _ source.expected).2.1
  have bounds := Artifacts.validated_retained_bounds _ _ _ _ source.validation
  rw [source.stdout, source.stderr, source.files]
  rw [limits] at bounds
  exact ⟨bounds.2.1, bounds.2.2.1, bounds.2.2.2.1, by
    have count := bounds.2.2.2.2.1
    omega⟩

-- §FS-host-boundary.publication: Later validation failure never erases a recognized report.
theorem receive_report (request : String) (bundle : Validation.Bundle) (preflight : Bool)
    (policy : Policy.Accepted) (vm : VirtualMachine.Result)
    {events : List (Request × Reply)} {input : Publication.Input}
    (run : Returns (receive request bundle preflight policy vm) events input) :
    input.outcome.report = vm.transport.report?.bind (Artifacts.knownReport preflight) := by
  unfold receive at run
  dsimp only at run
  split at run
  · obtain ⟨_, same⟩ := Snapshot.returns_pure_eq run
    cases same
    rfl
  · cases finished : vm.transport.finish with
    | error error =>
      simp only [finished] at run
      obtain ⟨_, same⟩ := Snapshot.returns_pure_eq run
      cases same
      rfl
    | ok transport =>
      simp only [finished] at run
      cases expectation : expected bundle preflight policy.transport with
      | error error =>
        simp only [expectation] at run
        obtain ⟨_, same⟩ := Snapshot.returns_pure_eq run
        cases same
        rfl
      | ok expectationValue =>
        simp only [expectation] at run
        obtain ⟨checking, result, last, validation, final, _⟩ := Snapshot.returns_bind_split _ _ run
        cases result with
        | error error =>
          obtain ⟨_, same⟩ := Snapshot.returns_pure_eq final
          cases same
          rfl
        | ok validated =>
          obtain ⟨_, same⟩ := Snapshot.returns_pure_eq final
          cases same
          have valid := Artifacts.validate_sound _ _ _ _ validation
          have kind := (expected_source bundle preflight policy.transport _ expectation).1
          have raw := (Transport.finish_shape _ _ finished).2.2.1
          simp only [raw, Option.bind_some]
          unfold Artifacts.knownReport
          rw [valid.report.parsed, ← kind]
          dsimp only
          rw [valid.report.recognized]
          rfl

-- §FS-host-boundary.artifacts: Arbitrary and lost validation calls can only request hashes.
theorem receive_hashOnly (request : String) (bundle : Validation.Bundle) (preflight : Bool)
    (policy : Policy.Accepted) (vm : VirtualMachine.Result) :
    Artifacts.HashOnly (receive request bundle preflight policy vm) := by
  unfold receive
  split
  · exact .pure _
  · split
    · exact .pure _
    · split
      · exact .pure _
      · apply Artifacts.hashOnly_bind (Artifacts.validate_hashOnly _ _)
        intro result
        cases result <;> exact .pure _

theorem receive_no_write_prefix (request : String) (bundle : Validation.Bundle) (preflight : Bool)
    (policy : Policy.Accepted) (vm : VirtualMachine.Result)
    {events : List (Request × Option Reply)}
    (run : Prefix (receive request bundle preflight policy vm) events) :
    ∀ event ∈ events, event.1.op = .sha256 :=
  Artifacts.hashOnly_prefix (receive_hashOnly request bundle preflight policy vm) run

end LeanCage.Host.ReceiveProofs
