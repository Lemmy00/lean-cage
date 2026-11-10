import FilesystemVirtualMachineBorrowing.Loop

namespace LeanCage.Host.VirtualMachine
open Filesystem Kernel

theorem observe_exit_borrow {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : DescriptorContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (raw : handle.rawOwned = true)
    (fuel : Nat) {configuration : IO.Process.StdioConfig} (child : IO.Process.Child configuration) :
    ActorBorrowPost runtime actor held handle (fun _ => True) (observeExit fuel child) := by
  induction fuel with
  | zero => exact .pure True.intro
  | succ fuel ih =>
    unfold observeExit
    apply actor_borrow_bind (runtime_effect_borrow sdk actor held handle (.tryWait child) True.intro raw)
    intro status _
    cases status with
    | error error => exact .pure True.intro
    | ok status =>
      cases status with
      | some code => exact .pure True.intro
      | none =>
        apply actor_borrow_bind (poll_borrow laws actor held handle _ _)
        intro ignored _
        exact ih

theorem reap_borrow {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : DescriptorContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (raw : handle.rawOwned = true)
    {configuration : IO.Process.StdioConfig} (child : IO.Process.Child configuration)
    (state : State) (fresh : ConnectionFresh held state) :
    ActorBorrowPost runtime actor held handle (ConnectionFresh held) (reap child state) := by
  unfold reap
  split
  · exact .pure fresh
  · apply actor_borrow_bind (runtime_effect_borrow sdk actor held handle (.terminate child) True.intro raw)
    intro ignored _
    apply actor_borrow_bind (observe_exit_borrow laws sdk actor held handle raw _ child)
    intro observed _
    split
    · exact .pure fresh
    · apply actor_borrow_bind (perform_passive_borrow laws actor held handle _ (by simp [RetainsDescriptors]))
      intro ignored _
      apply actor_borrow_bind (observe_exit_borrow laws sdk actor held handle raw _ child)
      intro observed _
      exact .pure fresh

private theorem after_state_borrow {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : DescriptorContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (raw : handle.rawOwned = true)
    {configuration : IO.Process.StdioConfig} (child : IO.Process.Child configuration)
    (state : State) (fresh : ConnectionFresh held state) :
    ActorBorrowPost runtime actor held handle (fun _ => True) (runAfterState child state) := by
  unfold runAfterState
  apply actor_borrow_bind (reap_borrow laws sdk actor held handle raw child state fresh)
  intro state fresh
  cases connected : state.connection with
  | some fd =>
    apply actor_borrow_bind (vm_close_borrow laws actor held handle fd (fresh fd connected))
    intro ignored _
    exact .pure True.intro
  | none => exact .pure True.intro

-- §FS-host-boundary.ownership: Spawn, supervision and all failures retain borrowed raw resources.
theorem run_borrow {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : DescriptorContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (raw : handle.rawOwned = true)
    (bundle : Validation.Bundle) (directory : String) (duration : Nat) (transport : Transport.State) :
    ActorBorrowPost runtime actor held handle (fun _ => True) (run bundle directory duration transport) := by
  unfold run
  apply actor_borrow_bind (runtime_effect_borrow sdk actor held handle (.spawn (arguments bundle directory)) True.intro raw)
  intro child _
  cases child with
  | error error => exact .pure True.intro
  | ok child =>
    apply actor_borrow_bind (runtime_effect_borrow sdk actor held handle (.descriptor child.stdout) True.intro raw)
    intro boot _
    apply actor_borrow_bind (runtime_effect_borrow sdk actor held handle (.descriptor child.stderr) True.intro raw)
    intro diagnostic _
    have initialFresh : ConnectionFresh held ({transport} : State) := by
      intro fd impossible
      cases impossible
    split
    · rename_i bootFd diagnosticFd foundBoot foundDiagnostic
      apply actor_borrow_bind (clock_borrow laws actor held handle)
      intro began _
      cases began with
      | error error =>
        have failedFresh : ConnectionFresh held (({transport} : State).fail error.message) := initialFresh
        apply actor_borrow_bind (first := ConnectionFresh held) (.pure failedFresh)
        intro state fresh
        exact after_state_borrow laws sdk actor held handle raw child state fresh
      | ok began =>
        apply actor_borrow_bind (loop_borrow laws sdk actor held handle raw _ child _ _ _ _ _ _ initialFresh)
        intro state fresh
        exact after_state_borrow laws sdk actor held handle raw child state fresh
    · have failedFresh : ConnectionFresh held
          (({transport} : State).fail "VM stream ownership could not be established") := initialFresh
      apply actor_borrow_bind (first := ConnectionFresh held) (.pure failedFresh)
      intro state fresh
      exact after_state_borrow laws sdk actor held handle raw child state fresh

end LeanCage.Host.VirtualMachine
