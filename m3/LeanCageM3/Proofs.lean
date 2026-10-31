import LeanCageM3.AuthorityProofs
import LeanCageM3.Filter
import LeanCageM3.ProcessProofs
import LeanCageM3.Resources

namespace LeanCageM3

-- §AR-workspace.proofs: Component results compose over model traces, not unproved Linux
-- transitions.
structure SafetySummary (s : Authority) (requests : List Request) (events : List LaunchEvent) : Prop where
  runtime : ∀ id object, s.objects id = some object → object.area = .runtime →
    (executeRequests s requests).objects id = some object
  entry : entryReady (launchTrace {} events)
  reads : ∀ fd bytes, readHandle (executeRequests s requests) fd = some bytes →
    ∃ (h : Handle) (obj : Object), (executeRequests s requests).handles fd = some h ∧
      deref (executeRequests s requests) h.ref = some obj ∧
      readable (executeRequests s requests).run obj.area = true ∧ obj.bytes = bytes

-- Arbitrary aliases, host interference, failures, guest output and report loss occur in these traces.
theorem model_safety (s : Authority) (requests : List Request) (events : List LaunchEvent) :
    SafetySummary s requests events := by
  exact ⟨runtime_trace_preserved s requests, reachable_entry_ready events,
    read_requires_authority (executeRequests s requests)⟩

-- §FS-assurance.evidence: Useful read/write and entry witnesses accompany universal safety claims.
theorem useful_execution :
    readHandle (writeHandle (openName usefulAuthority [97] 3 true) 3 [66]) 3 = some [66] ∧
      (launchStep { receipts := required } .attemptExec).entered = true :=
  ⟨useful_read_write, useful_entry⟩

-- §FS-workspace.execution: Every actually accepted request retains bounds and the complete filter
-- theorem.
theorem accepted_policy_filter_action (bytes : ByteArray) (policy : Policy)
    (accepted : decodePolicy bytes = .ok policy) (arch nr low high : UInt32) :
    limitsValid policy.limits = true ∧ argvValid policy.argv = true ∧
    Filter.run arch nr low high (Filter.allowed.length + 20) Filter.instructions 0 =
      some (Filter.action arch nr low high) := by
  have bounds := decodePolicy_bounds bytes policy accepted
  exact ⟨bounds.1, bounds.2, Filter.policy_filter_action arch nr low high⟩

-- §FS-workspace.resources: All actual members, including threads, inherit the owned cgroup
-- identity.
theorem resource_scope (s : Processes) (safe : processesSafe s) (pid : UInt32) (task : Task)
    (present : s.tasks pid = some task) : task.scope = s.run := (safe pid task present).2.1

-- §AR-workspace.proofs: Composition starts with empty authority/process handles, not an invariant
-- premise.
theorem reachable_model_safety (run : RunId) (objects : ObjectId → Option Object)
    (names : Name → Option Node) (requests : List Request) (events : List LaunchEvent)
    (uid : UInt32) (root : Ref) (namespaceId : UInt64) (filter : List UInt8)
    (grants : List Handle) (processEvents : List ProcessEvent) :
    SafetySummary (cleanAuthority run objects names) requests events ∧
    IssuedHandles (executeRequests (cleanAuthority run objects names) requests) ∧
    processesSafe (processTrace (emptyProcesses run uid root namespaceId filter grants) processEvents) :=
  ⟨model_safety _ requests events, reachable_issued_handles run objects names requests,
    reachable_processes_safe run uid root namespaceId filter grants processEvents⟩

end LeanCageM3
