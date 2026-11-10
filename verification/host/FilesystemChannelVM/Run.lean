import FilesystemChannelVM.Loop

namespace LeanCage.Host.VirtualMachine
open Filesystem Kernel

theorem channel_observe_exit {kernel : Contract} {sourceProgram : Program UInt32} {runtime : ActorRuntime kernel sourceProgram}
    (laws : DescriptorContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (raw : handle.rawOwned = true)
    (fuel : Nat) {configuration : IO.Process.StdioConfig} (child : IO.Process.Child configuration) :
    ChannelWritePost runtime actor held handle (fun _ => True) (observeExit fuel child) := by
  induction fuel with
  | zero => exact .pure True.intro
  | succ fuel ih =>
    unfold observeExit
    apply channel_bind (channel_runtime sdk actor held handle (.tryWait child) True.intro raw)
    intro status _
    cases status with
    | error error => exact .pure True.intro
    | ok status =>
      cases status with
      | some code => exact .pure True.intro
      | none =>
        apply channel_bind (channel_poll laws actor held handle _ _)
        intro ignored _
        exact ih

theorem channel_reap {kernel : Contract} {sourceProgram : Program UInt32} {runtime : ActorRuntime kernel sourceProgram}
    (laws : DescriptorContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (raw : handle.rawOwned = true)
    {configuration : IO.Process.StdioConfig} (child : IO.Process.Child configuration)
    (state : State) (fresh : ConnectionFresh held state) :
    ChannelWritePost runtime actor held handle (ConnectionFresh held) (reap child state) := by
  unfold reap
  split
  · exact .pure fresh
  · apply channel_bind (channel_runtime sdk actor held handle (.terminate child) True.intro raw)
    intro ignored _
    apply channel_bind (channel_observe_exit laws sdk actor held handle raw _ child)
    intro observed _
    split
    · exact .pure fresh
    · apply channel_bind (channel_perform laws actor held handle _ (by simp [RetainsDescriptors]) (by intro wrong; cases wrong) rfl)
      intro ignored _
      apply channel_bind (channel_observe_exit laws sdk actor held handle raw _ child)
      intro observed _
      exact .pure fresh

private theorem channel_after_state {kernel : Contract} {sourceProgram : Program UInt32} {runtime : ActorRuntime kernel sourceProgram}
    (laws : DescriptorContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (raw : handle.rawOwned = true)
    {configuration : IO.Process.StdioConfig} (child : IO.Process.Child configuration)
    (state : State) (fresh : ConnectionFresh held state) :
    ChannelWritePost runtime actor held handle (fun _ => True) (runAfterState child state) := by
  unfold runAfterState
  apply channel_bind (channel_reap laws sdk actor held handle raw child state fresh)
  intro state fresh
  cases connected : state.connection with
  | some fd =>
    apply channel_bind (channel_close laws actor held handle fd (fresh fd connected))
    intro ignored _
    exact .pure True.intro
  | none => exact .pure True.intro

-- §FS-host-boundary.caller: Actual spawn, supervision and cancellation never write
-- the borrowed response channel.
theorem channel_run {kernel : Contract} {sourceProgram : Program UInt32} {runtime : ActorRuntime kernel sourceProgram}
    (laws : DescriptorContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (raw : handle.rawOwned = true)
    (bundle : Validation.Bundle) (directory : String) (duration : Nat) (transport : Transport.State) :
    ChannelWritePost runtime actor held handle (fun _ => True) (run bundle directory duration transport) := by
  unfold run
  apply channel_bind (channel_runtime sdk actor held handle (.spawn (arguments bundle directory)) True.intro raw)
  intro child _
  cases child with
  | error error => exact .pure True.intro
  | ok child =>
    apply channel_bind (channel_runtime sdk actor held handle (.descriptor child.stdout) True.intro raw)
    intro boot _
    apply channel_bind (channel_runtime sdk actor held handle (.descriptor child.stderr) True.intro raw)
    intro diagnostic _
    have initialFresh : ConnectionFresh held ({transport} : State) := by
      intro fd impossible
      cases impossible
    split
    · rename_i bootFd diagnosticFd foundBoot foundDiagnostic
      apply channel_bind (channel_clock laws actor held handle)
      intro began _
      cases began with
      | error error =>
        have failedFresh : ConnectionFresh held (({transport} : State).fail error.message) := initialFresh
        apply channel_bind (first := ConnectionFresh held) (.pure failedFresh)
        intro state fresh
        exact channel_after_state laws sdk actor held handle raw child state fresh
      | ok began =>
        apply channel_bind (channel_loop laws sdk actor held handle raw _ child _ _ _ _ _ _ initialFresh)
        intro state fresh
        exact channel_after_state laws sdk actor held handle raw child state fresh
    · have failedFresh : ConnectionFresh held
          (({transport} : State).fail "VM stream ownership could not be established") := initialFresh
      apply channel_bind (first := ConnectionFresh held) (.pure failedFresh)
      intro state fresh
      exact channel_after_state laws sdk actor held handle raw child state fresh

end LeanCage.Host.VirtualMachine
