import LeanCage.Launch.Model
import Std.Tactic

namespace LeanCage.Launch

-- §FS-filter-loading.installation.failure: Every possible event is blocked after failure.
theorem failed_terminal (validated : Bool) (reason : Failure) (event : Event) :
    step validated (.failed reason) event = none := by
  cases event <;> try rfl
  next reason' => cases reason' <;> cases validated <;> rfl

-- §FS-filter-loading.installation.failure: External termination cannot reopen setup.
theorem terminated_terminal (validated : Bool) (event : Event) :
    step validated .terminated event = none := by
  cases event <;> try rfl
  next reason => cases reason <;> cases validated <;> rfl

-- §FS-filter-loading.installation.model: Each concrete transition preserves earlier receipts.
theorem step_receipts {validated : Bool} {before after : Stage} {trace : Trace} {event : Event}
    (hreceipts : Receipts before trace) (hstep : step validated before event = some after) :
    Receipts after (trace ++ [event]) := by
  cases before <;> cases event <;> cases after <;> simp_all [step, Receipts]

-- §FS-filter-loading.installation.model: Transitions cannot fabricate a positive verdict.
theorem step_validation_guard {validated : Bool} {before after : Stage} {event : Event}
    (hguard : ValidationGuard validated before) (hstep : step validated before event = some after) :
    ValidationGuard validated after := by
  cases before <;> cases event <;> cases after <;> simp_all [step, ValidationGuard]

-- §FS-filter-loading.installation.model: All reachable states retain their required receipts.
theorem reaches_receipts {validated : Bool} {trace : Trace} {state : Stage}
    (h : Reaches validated trace state) : Receipts state trace := by
  induction h with
  | start => trivial
  | next _ hstep ih => exact step_receipts ih hstep

-- §FS-filter-loading.installation.model: Setup reachability depends on successful validation.
theorem reaches_validation_guard {validated : Bool} {trace : Trace} {state : Stage}
    (h : Reaches validated trace state) : ValidationGuard validated state := by
  induction h with
  | start => trivial
  | next _ hstep ih => exact step_validation_guard ih hstep

-- §FS-filter-loading.installation.model: Privilege restriction requires earlier validation.
theorem validation_before_no_new_privileges {validated : Bool} {trace : Trace}
    {before after : Stage} (h : Reaches validated trace before)
    (hs : step validated before .noNewPrivilegesSet = some after) :
    .validationAccepted ∈ trace := by
  cases before <;> simp [step] at hs
  exact reaches_receipts h

-- §FS-filter-loading.installation.model: Receipts precede installation, not merely guest entry.
theorem no_new_privileges_before_install {validated : Bool} {trace : Trace} {before after : Stage}
    (h : Reaches validated trace before) (hs : step validated before .filterInstalled = some after) :
    .validationAccepted ∈ trace ∧ .noNewPrivilegesSet ∈ trace := by
  cases before <;> simp [step] at hs
  exact reaches_receipts h

-- §FS-filter-loading.installation.model: Every reachable exec attempt follows installation.
theorem install_before_exec {validated : Bool} {trace : Trace} {before after : Stage}
    (h : Reaches validated trace before) (hs : step validated before .execAttempted = some after) :
    .validationAccepted ∈ trace ∧ .noNewPrivilegesSet ∈ trace ∧ .filterInstalled ∈ trace := by
  cases before <;> simp [step] at hs
  exact reaches_receipts h

-- §FS-filter-loading.installation.model: Image replacement also requires an earlier exec attempt.
theorem install_before_guest {validated : Bool} {trace : Trace} {before after : Stage}
    (h : Reaches validated trace before) (hs : step validated before .execSucceeded = some after) :
    .validationAccepted ∈ trace ∧ .noNewPrivilegesSet ∈ trace ∧
      .filterInstalled ∈ trace ∧ .execAttempted ∈ trace := by
  cases before <;> simp [step] at hs
  exact reaches_receipts h

-- §FS-filter-loading.installation.model: Exact histories also establish the order of receipts.
theorem step_successful_history {validated : Bool} {before after : Stage}
    {trace : Trace} {event : Event} (hh : SuccessfulHistory before trace)
    (hs : step validated before event = some after) :
    SuccessfulHistory after (trace ++ [event]) := by
  cases before <;> cases event <;> cases after <;>
    simp_all [step, SuccessfulHistory, successTrace]

-- §FS-filter-loading.installation.model: All successful reachability preserves the exact order.
theorem reaches_successful_history {validated : Bool} {trace : Trace} {state : Stage}
    (h : Reaches validated trace state) : SuccessfulHistory state trace := by
  induction h with
  | start => rfl
  | next _ hs ih => exact step_successful_history ih hs

-- §FS-filter-loading.installation.model: Guest entry has the full ordered successful trace.
theorem executed_trace_exact {validated : Bool} {trace : Trace}
    (h : Reaches validated trace .executed) : trace = successTrace :=
  reaches_successful_history h

-- §FS-filter-loading.installation.model: Replay composes at a real intermediate state.
theorem replay_append (validated : Bool) (state : Stage) (left right : Trace) :
    replay validated state (left ++ right) =
      (replay validated state left).bind fun middle => replay validated middle right := by
  induction left generalizing state with
  | nil => rfl
  | cons event rest ih =>
    cases hs : step validated state event <;> simp [replay, hs, ih]

-- §FS-filter-loading.installation.model: Inductive executions are executable by replay.
theorem reaches_replay {validated : Bool} {trace : Trace} {state : Stage}
    (h : Reaches validated trace state) : replay validated .unvalidated trace = some state := by
  induction h with
  | start => rfl
  | next _ hstep ih => simp [replay_append, ih, replay, hstep]

-- §FS-filter-loading.installation.model: Replay cannot introduce an unmodeled transition.
theorem replay_extends_reaches {validated : Bool} {history trace : Trace} {before after : Stage}
    (hp : Reaches validated history before) (hr : replay validated before trace = some after) :
    Reaches validated (history ++ trace) after := by
  induction trace generalizing history before with
  | nil =>
    simp only [replay, Option.some.injEq] at hr
    subst after
    simpa using hp
  | cons event rest ih =>
    cases hs : step validated before event with
    | none => simp [replay, hs] at hr
    | some middle =>
      have hr' : replay validated middle rest = some after := by simpa [replay, hs] using hr
      simpa [List.append_assoc] using ih (Reaches.next hp hs) hr'

-- §FS-filter-loading.installation.model: The executable and relational execution boundaries agree.
theorem replay_iff_reaches (validated : Bool) (trace : Trace) (state : Stage) :
    replay validated .unvalidated trace = some state ↔ Reaches validated trace state := by
  constructor
  · intro h
    simpa using replay_extends_reaches Reaches.start h
  · exact reaches_replay

-- §FS-filter-loading.installation.model: Rejected input excludes image replacement on any trace.
theorem rejected_never_executes (trace : Trace) :
    replay false .unvalidated trace ≠ some .executed := by
  intro h
  have hg := reaches_validation_guard ((replay_iff_reaches false trace .executed).mp h)
  simp [ValidationGuard] at hg

-- §FS-filter-loading.installation.model: All success assumptions are jointly inhabited.
theorem success_witness : replay true .unvalidated successTrace = some .executed := by
  rfl

-- §FS-filter-loading.installation.model: Failed installation is a real, inhabited model outcome.
theorem failed_install_witness :
    replay true .unvalidated [.validationAccepted, .noNewPrivilegesSet,
      .failed (.osError .installFilter ⟨22, by decide⟩)] =
      some (.failed (.osError .installFilter ⟨22, by decide⟩)) := by
  rfl

-- §FS-filter-loading.installation.model: Interrupted installation is terminal and inhabited.
theorem interrupted_install_witness :
    replay true .unvalidated [.validationAccepted, .noNewPrivilegesSet,
      .failed (.interrupted .installFilter)] = some (.failed (.interrupted .installFilter)) := by
  rfl

end LeanCage.Launch
