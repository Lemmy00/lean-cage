import ProgramProofs
import LeanCageHost.Application
import SnapshotProofs
import PolicyProofs

namespace LeanCage.Host.ApplicationProofs
open Filesystem

abbrev Run {α : Type} (program : Checked α) (events : List Program.Event) (value : α) : Prop :=
  Program.Returns program.run events (.ok value)

theorem bind_source {α β : Type} (first : Checked α) (next : α → Checked β)
    {events : List Program.Event} {value : β} (run : Run (first >>= next) events value) :
    ∃ before middle after, Run first before middle ∧ Run (next middle) after value ∧
      events = before ++ after := by
  change Program.Returns (Program.bind first.run (ExceptT.bindCont next)) events (.ok value) at run
  obtain ⟨before, middle, after, initial, final, shape⟩ := Program.returns_bind_split _ _ run
  cases middle with
  | error error => cases final
  | ok middle => exact ⟨before, middle, after, initial, final, shape⟩

theorem filesystem_source {α : Type} (program : Filesystem.Program (Filesystem.Result α))
    {events : List Program.Event} {value : α} (run : Run (filesystem program) events value) :
    ∃ source, Filesystem.Returns program source (.ok value) ∧
      events = source.map Program.filesystemEvent :=
  Program.lift_filesystem_source program run

theorem checked_source {α : Type} (input : Except String α)
    {events : List Program.Event} {value : α} (run : Run (checked input) events value) :
    input = .ok value ∧ events = [] := by
  cases input with
  | error error => cases run
  | ok original =>
    obtain ⟨rfl, equal⟩ := Program.returns_pure _ run
    cases equal
    exact ⟨rfl, rfl⟩

theorem check_request_source (request : GatewayWire.Request) {events : List Program.Event}
    (run : Run (checkRequest request) events ()) :
    request.valid = true ∧ request.command ≠ GatewayWire.cliCommand ∧ events = [] := by
  unfold checkRequest at run
  split at run
  · cases run
  · rename_i allowed
    obtain ⟨empty, _⟩ := Program.returns_pure _ run
    have allowed : request.valid = true ∧ request.command ≠ GatewayWire.cliCommand := by
      simpa [Bool.or_eq_true] using allowed
    exact ⟨allowed.1, allowed.2, empty⟩

-- §FS-host-boundary.snapshot: This receipt names the actual subcalls of the maintained producer.
structure Preparation (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (value : Policy.Accepted × Snapshot.Frozen) (events : List Program.Event) where
  raw : ByteArray
  originalValue : Json.Value
  original : Policy.Accepted
  bound : Policy.Accepted
  finalValue : Json.Value
  loadEvents : List (Request × Reply)
  validateEvents : List Program.Event
  snapshotEvents : List (Request × Reply)
  revalidateEvents : List Program.Event
  load : Filesystem.Returns (Validation.loadPolicy request) loadEvents (.ok raw)
  validate : Program.Returns (Validation.validateCopied bundle raw) validateEvents (.ok originalValue)
  budgets : Policy.budgets originalValue raw = .ok original
  snapshot : Filesystem.Returns
    (Snapshot.freeze (inputWorkspace request) (inputStdin request) original.snapshot)
    snapshotEvents (.ok value.2)
  binding : Policy.bind original value.2 = .ok bound
  revalidate : Program.Returns (Validation.validateCopied bundle bound.raw)
    revalidateEvents (.ok finalValue)
  profile : Validation.stringField finalValue "profile" =
    Validation.stringField bundle.manifest "profile"
  runtime : Validation.stringField finalValue "runtime_manifest_digest" =
    Validation.stringField bundle.manifest "runtime_manifest_digest"
  finalBudgets : Policy.budgets finalValue bound.raw = .ok value.1
  unchanged : value.1.sameBudgets original = true
  trace : events = loadEvents.map Program.filesystemEvent ++ validateEvents ++
    snapshotEvents.map Program.filesystemEvent ++ revalidateEvents

-- §FS-host-boundary.snapshot: Snapshot bounds and identities have the same real caller producer.
theorem prepare_policy_source (request : GatewayWire.Request) (bundle : Validation.Bundle)
    {events : List Program.Event} {value : Policy.Accepted × Snapshot.Frozen}
    (run : Run (preparePolicy request bundle) events value) :
    Nonempty (Preparation request bundle value events) := by
  unfold preparePolicy at run
  obtain ⟨loadEvents, raw, afterLoad, loaded, rest, loadShape⟩ := bind_source _ _ run
  obtain ⟨validateEvents, originalValue, afterValidate, validated, rest, validateShape⟩ :=
    bind_source _ _ rest
  obtain ⟨budgetEvents, original, afterBudgets, budgeted, rest, budgetShape⟩ := bind_source _ _ rest
  obtain ⟨budgets, rfl⟩ := checked_source _ budgeted
  obtain ⟨snapshotEvents, frozen, afterSnapshot, copied, rest, snapshotShape⟩ := bind_source _ _ rest
  obtain ⟨bindEvents, bound, afterBind, boundRun, rest, bindShape⟩ := bind_source _ _ rest
  obtain ⟨binding, rfl⟩ := checked_source _ boundRun
  obtain ⟨revalidateEvents, finalValue, last, revalidated, rest, revalidateShape⟩ := bind_source _ _ rest
  dsimp only at rest
  split at rest
  · cases rest
  · rename_i matched
    obtain ⟨finalBudgetEvents, final, ending, finalBudgeted, rest, finalBudgetShape⟩ := bind_source _ _ rest
    obtain ⟨finalBudgets, rfl⟩ := checked_source _ finalBudgeted
    split at rest
    · cases rest
    · rename_i unchanged
      change Program.Returns (.pure (Except.ok (final, frozen) : Except Failure _))
        ending (Except.ok value : Except Failure _) at rest
      obtain ⟨rfl, equal⟩ := Program.returns_pure _ rest
      have equal := Except.ok.inj equal
      cases equal
      obtain ⟨sourceLoad, load, loadTrace⟩ := filesystem_source _ loaded
      obtain ⟨sourceSnapshot, snapshot, snapshotTrace⟩ := filesystem_source _ copied
      have matched : Validation.stringField finalValue "profile" =
          Validation.stringField bundle.manifest "profile" ∧
          Validation.stringField finalValue "runtime_manifest_digest" =
          Validation.stringField bundle.manifest "runtime_manifest_digest" := by
        simpa using matched
      have unchanged : final.sameBudgets original = true := by simpa using unchanged
      refine ⟨⟨raw, originalValue, original, bound, finalValue,
        sourceLoad, validateEvents, sourceSnapshot, revalidateEvents,
        load, validated, budgets, snapshot, binding, revalidated,
        matched.1, matched.2, finalBudgets, unchanged, ?_⟩⟩
      simp only [loadShape, validateShape, budgetShape, snapshotShape, bindShape,
        revalidateShape, finalBudgetShape, loadTrace, snapshotTrace, List.nil_append,
        List.append_nil, List.append_assoc]

-- §FS-host-boundary.snapshot: The actual caller's returned snapshot satisfies its final budgets.
theorem prepared_snapshot_bounds (request : GatewayWire.Request) (bundle : Validation.Bundle)
    {events : List Program.Event} {value : Policy.Accepted × Snapshot.Frozen}
    (run : Run (preparePolicy request bundle) events value) :
    value.2.workspaceBytes ≤ value.1.transport.workspaceMax ∧
    value.2.count ≤ value.1.transport.inodesMax ∧
    (∀ input, value.2.stdin = some input → input.size ≤ value.1.snapshot.stdinBytes) ∧
    value.1.transport.valid = true := by
  obtain ⟨witness⟩ := prepare_policy_source request bundle run
  have bounds := Snapshot.freeze_bounds _ _ _ witness.snapshot
  obtain ⟨_, _, bytes, inodes, _, _, _⟩ := Policy.budgets_source _ _ _ witness.budgets
  have same := Policy.same_budgets _ _ witness.unchanged
  have final := Policy.budgets_source _ _ _ witness.finalBudgets
  refine ⟨?_, ?_, ?_, final.2.2.2.2.1⟩
  · simpa only [same.1, bytes] using bounds.2.2.2.1
  · simpa only [same.1, inodes] using bounds.2.2.1
  · intro input present
    simpa only [same.2.2.2.1] using bounds.2.2.2.2.2.2.1 input present

end LeanCage.Host.ApplicationProofs
