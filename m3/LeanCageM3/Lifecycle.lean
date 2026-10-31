import LeanCageM3.Authority
import LeanCageM3.Results

namespace LeanCageM3

-- §AR-workspace.proofs: Receipts record mechanisms; no receipt states the safety conclusion.
inductive Receipt where
  | runtimeFrozen | workspacePrivate | handlesClosed | credentials | scopePlaced
  | privateMounts | namespaces | filterValidated | noNewPrivileges | filterInstalled | parentArmed
  deriving DecidableEq, Repr

def required : List Receipt := [.parentArmed, .runtimeFrozen, .workspacePrivate,
  .namespaces, .privateMounts, .scopePlaced, .handlesClosed, .credentials,
  .filterValidated, .noNewPrivileges, .filterInstalled]

structure Lifecycle where
  receipts : List Receipt := []
  failed : Bool := false
  entered : Bool := false
  knowledge : Knowledge := {}

inductive LaunchEvent where
  | success (mechanism : Receipt)
  | failure | attemptExec
  | guest (bytes : ByteArray)
  | cancel | loseReport | extinct | release

-- §FS-workspace.results: Setup failure, hostile bytes, lost reports and cancellation remain steps.
def launchStep (s : Lifecycle) : LaunchEvent → Lifecycle
  | .success mechanism => if s.failed || s.entered || required[s.receipts.length]? != some mechanism then s else
      { s with receipts := s.receipts ++ [mechanism] }
  | .failure => { s with failed := true }
  | .attemptExec => if !s.failed && s.receipts == required then
      { s with entered := true, knowledge := observe s.knowledge .execObserved } else s
  | .guest bytes => { s with knowledge := observe s.knowledge (.guestBytes bytes) }
  | .cancel => { s with knowledge := observe s.knowledge .cancel }
  | .loseReport => { s with knowledge := observe s.knowledge .reportLost }
  | .extinct => { s with knowledge := observe s.knowledge .scopeExtinct }
  | .release => { s with knowledge := observe s.knowledge .releaseObserved }

-- §AR-workspace.proofs: The first entry requires every specific receipt and no earlier failure.
theorem entry_requires_receipts (s : Lifecycle) (before : s.entered = false)
    (after : (launchStep s .attemptExec).entered = true) :
    s.failed = false ∧ ∀ r ∈ required, r ∈ s.receipts := by
  simp only [launchStep] at after
  split at after
  · rename_i h
    have both : s.failed = false ∧ s.receipts = required := by simpa using h
    exact ⟨both.1, by simp [both.2]⟩
  · simp [before] at after

-- §FS-workspace.authority: Task identities include allocation generation, scope and credentials.
def workspaceCredentials (uid : UInt32) : LeanCageM2.Credentials :=
  { realUid := uid, effectiveUid := uid, savedUid := uid, fsUid := uid,
    realGid := uid, effectiveGid := uid, savedGid := uid, fsGid := uid }

structure Task where
  generation : UInt64
  owner : RunId
  credentials : LeanCageM2.Credentials
  scope : RunId
  root : Ref
  namespaceId : UInt64
  handles : List Handle
  nnp : Bool
  filter : List UInt8
  deriving DecidableEq, Repr

structure Processes where
  run : RunId
  uid : UInt32
  root : Ref
  namespaceId : UInt64
  filter : List UInt8
  grants : List Handle
  tasks : UInt32 → Option Task

def taskSafe (s : Processes) (task : Task) : Prop :=
  task.owner = s.run ∧ task.scope = s.run ∧ task.credentials = workspaceCredentials s.uid ∧
  task.root = s.root ∧ task.namespaceId = s.namespaceId ∧ task.nnp = true ∧ task.filter = s.filter ∧
  ∀ handle ∈ task.handles, handle ∈ s.grants

def processesSafe (s : Processes) : Prop := ∀ pid task, s.tasks pid = some task → taskSafe s task

-- §FS-workspace.execution: A fresh child copies restrictions; a requested owner is not an argument.
def forkTask (s : Processes) (parent child : UInt32) (generation : UInt64) : Processes :=
  match s.tasks parent with
  | none => s
  | some task => if s.tasks child = none then
      { s with tasks := fun pid => if pid = child then some { task with generation } else s.tasks pid }
    else s

def exitTask (s : Processes) (pid : UInt32) : Processes :=
  { s with tasks := fun n => if n = pid then none else s.tasks n }

-- §AR-workspace.proofs: Arbitrary child PID and generation inherit the existing parent's scope.
theorem descendant_inherits (s : Processes) (safe : processesSafe s)
    (parent child : UInt32) (generation : UInt64) :
    processesSafe (forkTask s parent child generation) := by
  unfold forkTask
  split
  · exact safe
  · rename_i task found
    split
    · intro pid result h
      dsimp at h ⊢
      split at h
      · cases h
        exact safe parent task found
      · exact safe pid result h
    · exact safe

theorem exit_preserves_scope (s : Processes) (safe : processesSafe s) (pid : UInt32) :
    processesSafe (exitTask s pid) := by
  intro n task h
  simp only [exitTask] at h ⊢
  split at h
  · contradiction
  · exact safe n task h

-- §FS-workspace.execution: An exec changes code, preserving the actual owner, scope and
-- restrictions.
def execTask (s : Processes) (_pid : UInt32) (_program : List UInt8) : Processes := s

theorem exec_preserves_scope (s : Processes) (safe : processesSafe s)
    (pid : UInt32) (program : List UInt8) : processesSafe (execTask s pid program) := safe

-- §AR-workspace.proofs: Reachability retains failures and cancellation, including after entry.
def entryReady (s : Lifecycle) : Prop := s.entered = true → ∀ r ∈ required, r ∈ s.receipts

theorem entry_ready_step (s : Lifecycle) (ready : entryReady s) (event : LaunchEvent) :
    entryReady (launchStep s event) := by
  cases event <;> simp only [launchStep]
  · split
    · exact ready
    · intro entered r hr
      exact List.mem_append_left _ (ready entered r hr)
  · exact ready
  · split
    · rename_i h
      intro _
      have ready : s.failed = false ∧ s.receipts = required := by simpa using h
      simp [ready.2]
    · exact ready
  · exact ready
  · exact ready
  · exact ready
  · exact ready
  · exact ready

def launchTrace (s : Lifecycle) : List LaunchEvent → Lifecycle
  | [] => s
  | event :: rest => launchTrace (launchStep s event) rest

theorem reachable_entry_ready (events : List LaunchEvent) :
    entryReady (launchTrace {} events) := by
  have preserve : ∀ (s : Lifecycle), entryReady s → entryReady (launchTrace s events) := by
    induction events with
    | nil => intro s ready; exact ready
    | cons event rest ih => intro s ready; exact ih _ (entry_ready_step s ready event)
  exact preserve {} (by simp [entryReady])

theorem useful_entry : (launchStep { receipts := required } .attemptExec).entered = true := by decide

-- §AR-workspace.proofs: This erases extra M3 preparation without borrowing M2's fixed-UID
-- invariant.
def projectReceipt : Receipt → List LeanCageM2.Operation
  | .workspacePrivate => [.bootstrap]
  | .privateMounts => [.namespaces]
  | .handlesClosed => [.handles]
  | .credentials => [.credentials]
  | .filterValidated => [.validate]
  | .noNewPrivileges => [.nnp]
  | .filterInstalled => [.filter]
  | _ => []

def entryOrdered (s : Lifecycle) : Prop := s.entered = true → s.receipts = required

theorem entry_ordered_step (s : Lifecycle) (ordered : entryOrdered s) (event : LaunchEvent) :
    entryOrdered (launchStep s event) := by
  cases event <;> simp only [launchStep]
  · split
    · exact ordered
    · rename_i h
      intro entered
      change s.entered = true at entered
      simp [entered] at h
  · exact ordered
  · split
    · rename_i h
      have both : s.failed = false ∧ s.receipts = required := by simpa using h
      intro _; exact both.2
    · exact ordered
  · exact ordered
  · exact ordered
  · exact ordered
  · exact ordered
  · exact ordered

theorem reachable_entry_ordered (events : List LaunchEvent) :
    entryOrdered (launchTrace {} events) := by
  have preserve : ∀ (s : Lifecycle), entryOrdered s → entryOrdered (launchTrace s events) := by
    induction events with
    | nil => intro s h; exact h
    | cons e es ih => intro s h; exact ih _ (entry_ordered_step s h e)
  exact preserve {} (by simp [entryOrdered])

theorem lifecycle_projection (events : List LaunchEvent)
    (entered : (launchTrace {} events).entered = true) :
    (launchTrace {} events).receipts.flatMap projectReceipt ++ [.exec] = LeanCageM2.plan := by
  rw [reachable_entry_ordered events entered]
  decide

theorem useful_launch_trace :
    (launchTrace {} (required.map LaunchEvent.success ++ [.attemptExec])).entered = true := by decide

end LeanCageM3
