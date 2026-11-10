import LeanCageHost.Policy

namespace LeanCage.Host.Policy

theorem same_budgets (first second : Policy.Accepted) (same : first.sameBudgets second = true) :
    first.transport = second.transport ∧
    first.snapshot.workspaceBytes = second.snapshot.workspaceBytes ∧
    first.snapshot.workspaceInodes = second.snapshot.workspaceInodes ∧
    first.snapshot.stdinBytes = second.snapshot.stdinBytes ∧
    first.wallMilliseconds = second.wallMilliseconds := by
  simpa [Policy.Accepted.sameBudgets, and_assoc] using same

theorem budgets_source (value : Json.Value) (raw : ByteArray) (policy : Policy.Accepted)
    (accepted : Policy.budgets value raw = .ok policy) :
    policy.value = value ∧ policy.raw = raw ∧
    policy.snapshot.workspaceBytes = policy.transport.workspaceMax ∧
    policy.snapshot.workspaceInodes = policy.transport.inodesMax ∧
    policy.transport.valid = true ∧ policy.snapshot.supported = true ∧ raw.size ≤ reportMax := by
  unfold Policy.budgets at accepted
  repeat' first
    | split at accepted
    | cases accepted
  all_goals simp_all
  split at accepted
  · change Except.error _ = Except.ok policy at accepted
    cases accepted
  · change Except.ok _ = Except.ok policy at accepted
    cases accepted
    simp_all

end LeanCage.Host.Policy
