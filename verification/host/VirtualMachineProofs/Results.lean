import VirtualMachineProofs.Run
import VirtualMachineProofs.Arguments

namespace LeanCage.Host.VirtualMachine

theorem read_subsequence_member {connection : Option UInt64} {events : List Program.Event}
    {stream : List Transport.Event} (source : ReadSubsequence connection events stream)
    (frame : Transport.Event) (member : frame ∈ stream) :
    ∃ fd observation, connection = some fd ∧ observation ∈ events ∧ ReadOrigin fd frame observation := by
  induction source with
  | nil => simp at member
  | skip event rest ih =>
    obtain ⟨fd, observation, selected, present, origin⟩ := ih member
    exact ⟨fd, observation, selected, List.mem_cons_of_mem event present, origin⟩
  | @read fd observation first events stream selected origin rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨fd, observation, selected, by simp, origin⟩
    · obtain ⟨fd, observation, selected, present, origin⟩ := ih later
      exact ⟨fd, observation, selected, List.mem_cons_of_mem _ present, origin⟩

-- §FS-host-boundary.acceptance: Framing inputs are produced by the maintained actual VM effect
-- program.
structure FinishedOrigin (request bundle : ByteArray) (limits : Transport.Limits)
    (initial : Transport.State) (events : List Program.Event) (vm : Result)
    (received : Transport.Result) where
  connection : Option UInt64
  stream : List Transport.Event
  initialized : Transport.State.init request bundle limits = .ok initial
  observed : ReadSubsequence connection events stream
  sameState : vm.transport = initial.run stream
  framed : (initial.run stream).finish = .ok received
  eofFd : UInt64
  eofObservation : Program.Event
  eofConnection : connection = some eofFd
  eofPresent : eofObservation ∈ events
  actualEof : ReadOrigin eofFd .eof eofObservation

-- §FS-host-boundary.transport: Completion requires an actual successful zero-length connection
-- read.
theorem actual_finished_origin (request bundleIdentity : ByteArray) (limits : Transport.Limits)
    (initial : Transport.State) (bundle : Validation.Bundle) (directory : String) (duration : Nat)
    {events : List Program.Event} {vm : Result} {received : Transport.Result}
    (initialized : Transport.State.init request bundleIdentity limits = .ok initial)
    (run : Program.Returns (VirtualMachine.run bundle directory duration initial) events vm)
    (finished : vm.transport.finish = .ok received) :
    Nonempty (FinishedOrigin request bundleIdentity limits initial events vm received) := by
  obtain ⟨connection, ⟨stream, sameState, observed⟩, _⟩ := run_source bundle directory duration initial run
  have framed : (initial.run stream).finish = .ok received := by simpa only [← sameState] using finished
  have eof := Transport.accepted_has_eof request bundleIdentity limits initial initialized stream received framed
  obtain ⟨fd, observation, selected, present, origin⟩ := read_subsequence_member observed .eof eof
  exact ⟨⟨connection, stream, initialized, observed, sameState, framed,
    fd, observation, selected, present, origin⟩⟩

theorem actual_run_bounds (request bundleIdentity : ByteArray) (limits : Transport.Limits)
    (initial : Transport.State) (bundle : Validation.Bundle) (directory : String) (duration : Nat)
    {events : List Program.Event} {vm : Result}
    (initialized : Transport.State.init request bundleIdentity limits = .ok initial)
    (run : Program.Returns (VirtualMachine.run bundle directory duration initial) events vm) :
    vm.transport.Bounded ∧ vm.boot.size ≤ diagnosticMax := by
  obtain ⟨_, _, bounded⟩ := run_source bundle directory duration initial run
  exact bounded (Transport.bounded_init request bundleIdentity limits initial initialized)

end LeanCage.Host.VirtualMachine
