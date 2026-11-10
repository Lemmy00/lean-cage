import VirtualMachineProofs.Loop

namespace LeanCage.Host.VirtualMachine
open Filesystem

-- §AR-application-verification.lifetime: Reaping observations cannot replace or fabricate
-- received bytes.
theorem reap_frame {configuration : IO.Process.StdioConfig} (child : IO.Process.Child configuration)
    (state : State) {events : List Program.Event} {after : State}
    (run : Program.Returns (reap child state) events after) :
    after.transport = state.transport ∧ after.connection = state.connection ∧
      after.boot = state.boot ∧ after.diagnostic = state.diagnostic := by
  unfold reap at run
  split at run
  · obtain ⟨rfl, rfl⟩ := Program.returns_pure _ run
    exact ⟨rfl, rfl, rfl, rfl⟩
  · obtain ⟨first, ignored, tail, terminated, rest, shape⟩ := Program.returns_bind_split _ _ run
    obtain ⟨observedTrace, observed, last, observedRun, ending, observationShape⟩ :=
      Program.returns_bind_split _ _ rest
    try dsimp only at ending
    split at ending
    · obtain ⟨rfl, rfl⟩ := Program.returns_pure _ ending
      exact ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨signalTrace, ignored, last, signalRun, ending, signalShape⟩ :=
        Program.returns_bind_split _ _ ending
      obtain ⟨finalTrace, observed, last, observedRun, ending, observationShape⟩ :=
        Program.returns_bind_split _ _ ending
      obtain ⟨rfl, rfl⟩ := Program.returns_pure _ ending
      exact ⟨rfl, rfl, rfl, rfl⟩

def initialProgram {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (directory : String) (duration : Nat)
    (transport : Transport.State) (boot diagnostic : Reply) : Program State := do
  let initial : State := { transport }
  match descriptor boot, descriptor diagnostic with
  | some boot, some diagnostic => do
    let began ← Runtime.clock
    match began with
    | .error error => pure (initial.fail error.message)
    | .ok began =>
      loop (duration / 1000000 + Transport.retainedBudget transport.limits + 2 * diagnosticMax + 1024)
        child (directory ++ "/control.sock").toUTF8 boot diagnostic began duration initial
  | _, _ => pure (initial.fail "VM stream ownership could not be established")

def finalProgram {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (state : State) : Program Result := do
  let state ← reap child state
  if let some fd := state.connection then close fd
  let state := if state.exitCode != some 33 then state.fail "VM ended without a complete exit" else state
  return Result.ofState state (if state.exitCode.isSome then "complete" else "unknown")

theorem initial_program_progress {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (directory : String) (duration : Nat)
    (transport : Transport.State) (boot diagnostic : Reply)
    {trace : List Program.Event} {after : State}
    (run : Program.Returns (initialProgram child directory duration transport boot diagnostic) trace after) :
    Progress { transport } after trace := by
  unfold initialProgram at run
  split at run
  · obtain ⟨clockTrace, began, tail, clockRun, rest, shape⟩ := Program.returns_bind_split _ _ run
    cases began with
    | error error =>
      obtain ⟨rfl, rfl⟩ := Program.returns_pure _ rest
      exact .fail _ _ _
    | ok began =>
      have progress := loop_progress _ child _ _ _ began duration { transport } rest
      have all := (Progress.refl { transport } clockTrace).trans progress
      simpa only [shape] using all
  · obtain ⟨rfl, rfl⟩ := Program.returns_pure _ run
    exact .fail _ _ _

theorem final_program_frame {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (state : State)
    {trace : List Program.Event} {result : Result}
    (run : Program.Returns (finalProgram child state) trace result) :
    result.transport = state.transport ∧ result.boot = state.boot := by
  unfold finalProgram at run
  obtain ⟨first, reaped, last, observed, rest, shape⟩ := Program.returns_bind_split _ _ run
  have frame := reap_frame child state observed
  have finish : ∀ {events : List Program.Event} {result : Result}, Program.Returns
      (pure (Result.ofState
        (if reaped.exitCode != some 33 then reaped.fail "VM ended without a complete exit" else reaped)
        (if (if reaped.exitCode != some 33 then reaped.fail "VM ended without a complete exit" else reaped).exitCode.isSome
          then "complete" else "unknown"))) events result →
      result.transport = state.transport ∧ result.boot = state.boot := by
    intro events result final
    obtain ⟨rfl, rfl⟩ := Program.returns_pure _ final
    split <;> exact ⟨frame.1, frame.2.2.1⟩
  cases connection : reaped.connection with
  | none =>
    simp only [connection] at rest
    exact finish rest
  | some fd =>
    simp only [connection] at rest
    obtain ⟨closed, ignored, last, closure, ending, closeShape⟩ := Program.returns_bind_split _ _ rest
    exact finish ending

theorem finish_result_source {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (transport : Transport.State) (state : State)
    (leading before after : List Program.Event) (result : Result)
    (progress : Progress { transport } state before)
    (finished : Program.Returns (finalProgram child state) after result) :
    ∃ connection, StreamSource transport result.transport connection (leading ++ before ++ after) ∧
      (transport.Bounded → result.transport.Bounded ∧ result.boot.size ≤ diagnosticMax) := by
  have frame := final_program_frame child state finished
  obtain ⟨stream, matched, observed⟩ := progress.source
  refine ⟨state.connection, ⟨stream, frame.1.trans matched, ?_⟩, ?_⟩
  · simpa only [List.nil_append, List.append_nil] using
      read_subsequence_append (read_subsequence_append (read_subsequence_empty _ leading) observed)
        (read_subsequence_empty _ after)
  · intro bound
    have initial : State.Bounded { transport } :=
      ⟨bound, by change 0 ≤ diagnosticMax; omega, by change 0 ≤ diagnosticMax; omega⟩
    have bounded := progress.bounded initial
    simpa only [frame.1, frame.2] using And.intro bounded.1 bounded.2.1

-- §FS-host-boundary.transport: The real spawned VM program supplies the exact decoder input stream.
theorem run_source (bundle : Validation.Bundle) (directory : String) (duration : Nat)
    (transport : Transport.State) {trace : List Program.Event} {result : Result}
    (run : Program.Returns (VirtualMachine.run bundle directory duration transport) trace result) :
    ∃ connection, StreamSource transport result.transport connection trace ∧
      (transport.Bounded → result.transport.Bounded ∧ result.boot.size ≤ diagnosticMax) := by
  unfold VirtualMachine.run at run
  dsimp only [Program.effect, Program.bind] at run
  cases run with
  | call _ _ created tail _ rest =>
    dsimp only [Program.bind] at rest
    cases created with
    | error error =>
      obtain ⟨rfl, rfl⟩ := Program.returns_pure _ rest
      exact ⟨none, stream_source_refl _ _ _,
        fun bound => ⟨bound, by change 0 ≤ diagnosticMax; omega⟩⟩
    | ok child =>
      dsimp only [Program.effect, Program.bind] at rest
      cases rest with
      | call _ _ boot more _ rest =>
        dsimp only [Program.effect, Program.bind] at rest
        cases rest with
        | call _ _ diagnostic ending _ rest =>
          dsimp only [Program.bind] at rest
          let leading : List Program.Event :=
            [.returned (.spawn (arguments bundle directory)) (.ok child),
              .returned (.descriptor child.stdout) boot, .returned (.descriptor child.stderr) diagnostic]
          cases firstDescriptor : descriptor boot with
          | none =>
            simp only [firstDescriptor] at rest
            have final : Program.Returns
                (finalProgram child (({ transport } : State).fail "VM stream ownership could not be established"))
                ending result := by
              set_option smartUnfolding false in with_unfolding_all exact rest
            exact finish_result_source child transport _ leading [] ending result (.fail _ _ []) final
          | some bootFd =>
            cases secondDescriptor : descriptor diagnostic with
            | none =>
              simp only [firstDescriptor, secondDescriptor] at rest
              have final : Program.Returns
                  (finalProgram child (({ transport } : State).fail "VM stream ownership could not be established"))
                  ending result := by
                set_option smartUnfolding false in with_unfolding_all exact rest
              exact finish_result_source child transport _ leading [] ending result (.fail _ _ []) final
            | some diagnosticFd =>
              simp only [firstDescriptor, secondDescriptor] at rest
              obtain ⟨clockTrace, began, last, clockRun, afterClock, clockShape⟩ :=
                Program.returns_bind_split _ _ rest
              cases began with
              | error error =>
                have final : Program.Returns
                    (finalProgram child (({ transport } : State).fail error.message)) last result := by
                  set_option smartUnfolding false in with_unfolding_all exact afterClock
                have source := finish_result_source child transport _ (leading ++ clockTrace) [] last result
                  (.fail _ _ []) final
                simpa only [clockShape, leading, List.append_assoc, List.cons_append, List.nil_append] using source
              | ok began =>
                obtain ⟨loopTrace, state, finalTrace, loopRun, finalRun, loopShape⟩ :=
                  Program.returns_bind_split _ _ afterClock
                have final : Program.Returns (finalProgram child state) finalTrace result := by
                  set_option smartUnfolding false in with_unfolding_all exact finalRun
                have progress := loop_progress _ child _ bootFd diagnosticFd began duration { transport } loopRun
                have source := finish_result_source child transport state (leading ++ clockTrace) loopTrace
                  finalTrace result progress final
                simpa only [clockShape, loopShape, leading, List.append_assoc, List.cons_append,
                  List.nil_append] using source

end LeanCage.Host.VirtualMachine
