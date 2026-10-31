import LeanCageM3.Lifecycle

namespace LeanCageM3

-- §AR-workspace.proofs: Admission constructs each restriction; it does not take a safety
-- proposition.
def admitLeader (s : Processes) (pid : UInt32) (generation : UInt64) : Processes :=
  if s.tasks pid = none then
    { s with tasks := fun n => if n = pid then some {
        generation, owner := s.run, credentials := workspaceCredentials s.uid,
        scope := s.run, root := s.root, namespaceId := s.namespaceId,
        handles := s.grants, nnp := true, filter := s.filter } else s.tasks n }
  else s

def emptyProcesses (run : RunId) (uid : UInt32) (root : Ref) (namespaceId : UInt64)
    (filter : List UInt8) (grants : List Handle) : Processes :=
  ⟨run, uid, root, namespaceId, filter, grants, fun _ => none⟩

inductive ProcessEvent where
  | admit (pid : UInt32) (generation : UInt64)
  | fork (parent child : UInt32) (generation : UInt64)
  | exec (pid : UInt32) (program : List UInt8)
  | exit (pid : UInt32)
  | deniedMigration (pid : UInt32) (target : RunId)

def processStep (s : Processes) : ProcessEvent → Processes
  | .admit pid generation => admitLeader s pid generation
  | .fork parent child generation => forkTask s parent child generation
  | .exec pid program => execTask s pid program
  | .exit pid => exitTask s pid
  | .deniedMigration _ _ => s

def processTrace (s : Processes) : List ProcessEvent → Processes
  | [] => s
  | event :: rest => processTrace (processStep s event) rest

-- §FS-workspace.execution: Establish inheritance from the empty state, then preserve arbitrary
-- traces.
theorem admission_establishes_scope (s : Processes) (safe : processesSafe s)
    (pid : UInt32) (generation : UInt64) : processesSafe (admitLeader s pid generation) := by
  unfold admitLeader
  split
  · intro n task present
    dsimp at present ⊢
    split at present
    · cases present
      simp [taskSafe]
    · exact safe n task present
  · exact safe

theorem process_step_safe (s : Processes) (safe : processesSafe s) (event : ProcessEvent) :
    processesSafe (processStep s event) := by
  cases event with
  | admit pid generation => exact admission_establishes_scope s safe pid generation
  | fork parent child generation => exact descendant_inherits s safe parent child generation
  | exec pid program => exact exec_preserves_scope s safe pid program
  | exit pid => exact exit_preserves_scope s safe pid
  | deniedMigration pid target => exact safe

theorem reachable_processes_safe (run : RunId) (uid : UInt32) (root : Ref)
    (namespaceId : UInt64) (filter : List UInt8) (grants : List Handle)
    (events : List ProcessEvent) :
    processesSafe (processTrace (emptyProcesses run uid root namespaceId filter grants) events) := by
  have preserve : ∀ s, processesSafe s → processesSafe (processTrace s events) := by
    induction events with
    | nil => intro s safe; exact safe
    | cons event rest ih => intro s safe; exact ih _ (process_step_safe s safe event)
  apply preserve
  simp [processesSafe, emptyProcesses]

-- §FS-assurance.evidence: A real parent, child and exec remain after the successful model trace.
theorem useful_descendants :
    let final := processTrace (emptyProcesses 1 100000 ⟨7, 1⟩ 1 [1, 2] [])
      [.admit 1 1, .fork 1 2 2, .exec 2 [65], .exit 1, .deniedMigration 2 99]
    (final.tasks 2).isSome = true ∧ final.tasks 1 = none := by decide

end LeanCageM3
