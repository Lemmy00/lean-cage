import LeanCage.Launch.Contract

namespace LeanCage.Launch

-- §FS-filter-loading.installation.failure: Failed, terminated and executed states are terminal.
def active : Stage → Bool
  | .failed _ | .terminated | .executed => false
  | _ => true

-- §FS-filter-loading.installation.states: Failures belong to the operation actually pending.
def pendingCall : Stage → Option OsCall
  | .ready => some .setNoNewPrivileges
  | .privilegesRestricted => some .installFilter
  | .executing => some .exec
  | _ => none

-- §FS-filter-loading.installation.failure: Interruption is distinct from an ordinary errno.
def allowedFailure (validated : Bool) (state : Stage) : Failure → Bool
  | .validationRejected => !validated && decide (state = .unvalidated)
  | .cancelled => active state
  | .osError operation errno =>
    decide (pendingCall state = some operation) && decide (errno.val.toNat ≠ 4)
  | .interrupted operation | .contractViolation operation =>
    decide (pendingCall state = some operation)

-- §FS-filter-loading.installation.model: Include every documented outcome; block bad ordering.
def step (validated : Bool) (state : Stage) (event : Event) : Option Stage :=
  match event with
  | .failed reason => if allowedFailure validated state reason then some (.failed reason) else none
  | .terminated => if active state then some .terminated else none
  | .validationAccepted =>
    match state with
    | .unvalidated => if validated then some .ready else none
    | _ => none
  | .noNewPrivilegesSet =>
    match state with
    | .ready => some .privilegesRestricted
    | _ => none
  | .filterInstalled =>
    match state with
    | .privilegesRestricted => some .filterInstalled
    | _ => none
  | .execAttempted =>
    match state with
    | .filterInstalled => some .executing
    | _ => none
  | .execSucceeded =>
    match state with
    | .executing => some .executed
    | _ => none

-- §FS-filter-loading.installation.model: Total executable replay of a finite event sequence.
def replay (validated : Bool) : Stage → Trace → Option Stage
  | state, [] => some state
  | state, event :: rest => (step validated state event).bind fun next => replay validated next rest

-- §FS-filter-loading.installation.model: Reachability starts before validation, not after setup.
inductive Reaches (validated : Bool) : Trace → Stage → Prop where
  | start : Reaches validated [] .unvalidated
  | next {trace : Trace} {before after : Stage} {event : Event} :
    Reaches validated trace before → step validated before event = some after →
    Reaches validated (trace ++ [event]) after

-- §FS-filter-loading.installation.model: Historical receipts do not claim rollback on failure.
def Receipts (state : Stage) (trace : Trace) : Prop :=
  match state with
  | .ready => .validationAccepted ∈ trace
  | .privilegesRestricted => .validationAccepted ∈ trace ∧ .noNewPrivilegesSet ∈ trace
  | .filterInstalled =>
    .validationAccepted ∈ trace ∧ .noNewPrivilegesSet ∈ trace ∧ .filterInstalled ∈ trace
  | .executing | .executed =>
    .validationAccepted ∈ trace ∧ .noNewPrivilegesSet ∈ trace ∧
      .filterInstalled ∈ trace ∧ .execAttempted ∈ trace
  | _ => True

-- §FS-filter-loading.installation.model: Successful setup requires a real validation verdict.
def ValidationGuard (validated : Bool) : Stage → Prop
  | .unvalidated | .failed _ | .terminated => True
  | _ => validated = true

-- §FS-filter-loading.installation.model: Inhabited success without a universal-success premise.
def successTrace : Trace :=
  [.validationAccepted, .noNewPrivilegesSet, .filterInstalled, .execAttempted, .execSucceeded]

-- §FS-filter-loading.installation.model: Successful states have these exact ordered histories.
def SuccessfulHistory (state : Stage) (trace : Trace) : Prop :=
  match state with
  | .unvalidated => trace = []
  | .ready => trace = [.validationAccepted]
  | .privilegesRestricted => trace = [.validationAccepted, .noNewPrivilegesSet]
  | .filterInstalled => trace = [.validationAccepted, .noNewPrivilegesSet, .filterInstalled]
  | .executing =>
    trace = [.validationAccepted, .noNewPrivilegesSet, .filterInstalled, .execAttempted]
  | .executed => trace = successTrace
  | .failed _ | .terminated => True

end LeanCage.Launch
