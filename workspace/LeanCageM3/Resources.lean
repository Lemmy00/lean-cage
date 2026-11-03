import LeanCageM3.Lifecycle

namespace LeanCageM3

-- §FS-workspace.resources: Named counters and supervisor knowledge, not an instantaneous RSS model.
structure Accounting where
  lastCPU : UInt64 := 0
  lastTime : UInt64 := 0
  lastOOM : UInt64 := 0
  cpuCancel : Bool := false
  wallCancel : Bool := false
  accountingLost : Bool := false
  oomObserved : Bool := false
  deriving DecidableEq, Repr

def sample (s : Accounting) (cpu time oom budget deadline : UInt64) : Accounting :=
  if cpu < s.lastCPU ∨ time < s.lastTime ∨ oom < s.lastOOM then
    { s with accountingLost := true }
  else
    { s with
      lastCPU := cpu
      lastTime := time
      lastOOM := oom
      cpuCancel := s.cpuCancel || decide (budget ≤ cpu)
      wallCancel := s.wallCancel || decide (deadline ≤ time)
      oomObserved := s.oomObserved || decide (s.lastOOM < oom) }

-- §AR-workspace.proofs: A delivered monotone sample triggers cancellation, without assuming timely
-- delivery.
theorem sampled_cpu_cancels (s : Accounting) (cpu time oom budget deadline : UInt64)
    (cpuMono : s.lastCPU ≤ cpu) (timeMono : s.lastTime ≤ time) (oomMono : s.lastOOM ≤ oom)
    (reached : budget ≤ cpu) :
    (sample s cpu time oom budget deadline).cpuCancel = true := by
  have h : ¬(cpu < s.lastCPU ∨ time < s.lastTime ∨ oom < s.lastOOM) := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at *
    omega
  simp [sample, h, reached]

theorem sampled_deadline_cancels (s : Accounting) (cpu time oom budget deadline : UInt64)
    (cpuMono : s.lastCPU ≤ cpu) (timeMono : s.lastTime ≤ time) (oomMono : s.lastOOM ≤ oom)
    (reached : deadline ≤ time) :
    (sample s cpu time oom budget deadline).wallCancel = true := by
  have h : ¬(cpu < s.lastCPU ∨ time < s.lastTime ∨ oom < s.lastOOM) := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at *
    omega
  simp [sample, h, reached]

theorem decreasing_counter_unknown (s : Accounting) (cpu time oom budget deadline : UInt64)
    (decreased : cpu < s.lastCPU ∨ time < s.lastTime ∨ oom < s.lastOOM) :
    (sample s cpu time oom budget deadline).accountingLost = true := by simp [sample, decreased]

theorem oom_requires_increase (s : Accounting) (cpu time oom budget deadline : UInt64)
    (before : s.oomObserved = false)
    (after : (sample s cpu time oom budget deadline).oomObserved = true) : s.lastOOM < oom := by
  unfold sample at after
  split at after
  · simp [before] at after
  · simpa [before] using after

-- §FS-workspace.resources: Creation is bounded; arbitrary inward migration is not an allowed
-- operation.
def admitTask (current limit : Nat) : Nat := if current < limit then current + 1 else current

theorem task_bound_preserved (current limit : Nat) (bound : current ≤ limit) :
    admitTask current limit ≤ limit := by unfold admitTask; split <;> omega

def capturePrefix (cap : Nat) (before incoming : List UInt8) : List UInt8 :=
  (before ++ incoming).take cap

theorem capture_bounded (cap : Nat) (before incoming : List UInt8) :
    (capturePrefix cap before incoming).length ≤ cap := by simp only [capturePrefix, List.length_take]; omega

-- §FS-workspace.authority: Unknown cleanup retains the lease; exhausted machine identities do not
-- wrap.
structure Lease where
  id : UInt64
  active : Bool
  extinct : Bool
  released : Bool
  deriving DecidableEq, Repr

def reusable (lease : Lease) : Bool := !lease.active && lease.extinct && lease.released

def nextRun (last : UInt64) : Option UInt64 := if last = (18446744073709551615 : UInt64) then none else some (last + 1)

theorem reuse_requires_extinction (lease : Lease) (h : reusable lease = true) :
    lease.extinct = true ∧ lease.released = true := by
  simp only [reusable, Bool.and_eq_true] at h
  exact ⟨h.1.2, h.2⟩

theorem exhaustion_rejected : nextRun (18446744073709551615 : UInt64) = none := by simp [nextRun]

end LeanCageM3

namespace LeanCageM3
-- §FS-workspace.resources: Serial admission reservations have a separate, explicit capacity
-- contract.
def reserve (current requested capacity : Nat) : Option Nat :=
  if current ≤ capacity ∧ requested ≤ capacity - current then some (current + requested) else none

theorem reservation_bounded (current requested capacity total : Nat)
    (accepted : reserve current requested capacity = some total) :
    total = current + requested ∧ total ≤ capacity := by
  unfold reserve at accepted
  split at accepted
  · cases accepted; constructor
    · rfl
    · omega
  · contradiction

theorem reservation_exhaustion (current requested capacity : Nat)
    (exhausted : capacity < current + requested) : reserve current requested capacity = none := by
  unfold reserve; split
  · omega
  · rfl
end LeanCageM3
