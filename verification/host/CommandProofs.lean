import CallerProofs
import LeanCageHost.Commands

namespace LeanCage.Host.Commands

theorem failure_code (failure : Filesystem.Failure) : (failureValue failure).1 ≠ 0 := by
  cases kind : failure.errno <;> simp [failureValue, kind]

-- §FS-host-boundary.caller: Success values come from the identical application invocation.
theorem dispatch_success_source (request : GatewayWire.Request) (duration : Option Nat)
    {events : List Program.Event} {answer : GatewayWire.Value}
    (run : Program.Returns (dispatch request duration) events (0, answer)) :
    Program.Returns (execute request duration) events (.ok answer) := by
  unfold dispatch at run
  obtain ⟨first, result, last, invoked, final, trace⟩ := Program.returns_bind_split _ _ run
  cases result with
  | error failure =>
    obtain ⟨_, same⟩ := Program.returns_pure _ final
    have code := congrArg Prod.fst same
    exact False.elim (failure_code failure code.symm)
  | ok value =>
    obtain ⟨rfl, same⟩ := Program.returns_pure _ final
    have same := congrArg Prod.snd same
    cases same
    rw [trace]
    simpa only [List.append_nil] using invoked

theorem native_run_source (request : GatewayWire.Request)
    {events : List Program.Event} {answer : GatewayWire.Value}
    (native : request.command ≠ GatewayWire.cliCommand)
    (run : Program.Returns (Commands.run request) events (0, answer)) :
    Program.Returns (execute request none) events (.ok answer) := by
  unfold Commands.run at run
  simp only [beq_iff_eq, native, ↓reduceIte] at run
  exact dispatch_success_source request none run

end LeanCage.Host.Commands
