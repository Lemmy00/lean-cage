import VirtualMachineProofs.Run

namespace LeanCage.Host.VirtualMachine
open Filesystem

-- §FS-host-boundary.ownership: A successful observation is retained as its
-- actual source event. Generic calls cannot manufacture such an observation.
inductive ReapingProgram {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) {α : Type} (post : α → Prop) : Program α → Prop where
  | pure {value : α} (valid : post value) : ReapingProgram child post (.pure value)
  | call {β : Type} {effect : Effect β} {next : β → Program α}
      (following : ∀ reply, ReapingProgram child post (next reply)) : ReapingProgram child post (.call effect next)
  | observation {next : Except String (Option UInt32) → Program α}
      (following : ∀ reply, (∀ code, reply ≠ .ok (some code)) → ReapingProgram child post (next reply)) :
      ReapingProgram child post (.call (.tryWait child) next)

theorem ReapingProgram.bind {configuration : IO.Process.StdioConfig} {child : IO.Process.Child configuration}
    {α β : Type} {program : Program α} {next : α → Program β} {first : α → Prop} {post : β → Prop}
    (source : ReapingProgram child first program)
    (tail : ∀ value, first value → ReapingProgram child post (next value)) :
    ReapingProgram child post (program.bind next) := by
  induction source with
  | pure valid => exact tail _ valid
  | call following ih => exact .call ih
  | observation following ih => exact .observation ih

theorem ReapingProgram.weaken {configuration : IO.Process.StdioConfig} {child : IO.Process.Child configuration}
    {α : Type} {program : Program α} {first post : α → Prop} (source : ReapingProgram child first program)
    (weaken : ∀ value, first value → post value) : ReapingProgram child post program := by
  induction source with
  | pure valid => exact .pure (weaken _ valid)
  | call following ih => exact .call ih
  | observation following ih => exact .observation ih

theorem ReapingProgram.any {configuration : IO.Process.StdioConfig} (child : IO.Process.Child configuration)
    {α : Type} (program : Program α) : ReapingProgram child (fun _ => True) program := by
  induction program with
  | pure => exact .pure True.intro
  | call effect next ih => exact .call ih

theorem ReapingProgram.returns {configuration : IO.Process.StdioConfig} {child : IO.Process.Child configuration}
    {α : Type} {program : Program α} {post : α → Prop} (source : ReapingProgram child post program)
    {events : List Program.Event} {value : α} (run : Program.Returns program events value) :
    post value ∨ ∃ code, Program.Event.returned (.tryWait child) (.ok (some code)) ∈ events := by
  induction source generalizing events value with
  | pure valid =>
    obtain ⟨rfl, rfl⟩ := Program.returns_pure _ run
    exact .inl valid
  | call following ih =>
    cases run with
    | call _ _ reply tail value rest =>
      rcases ih reply rest with valid | ⟨code, member⟩
      · exact .inl valid
      · exact .inr ⟨code, List.mem_cons_of_mem _ member⟩
  | observation following ih =>
    cases run with
    | call _ _ reply tail value rest =>
      by_cases reaped : ∃ code, reply = .ok (some code)
      · obtain ⟨code, rfl⟩ := reaped
        exact .inr ⟨code, by simp⟩
      · have none : ∀ code, reply ≠ .ok (some code) := by
          intro code same
          exact reaped ⟨code, same⟩
        rcases ih reply none rest with valid | ⟨code, member⟩
        · exact .inl valid
        · exact .inr ⟨code, List.mem_cons_of_mem _ member⟩

private theorem consume_exit_none {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (fd boot diagnostic : UInt64) (now : Nat)
    (state : State) (absent : state.exitCode = none) :
    ReapingProgram child (fun after => after.exitCode = none) (consume fd boot diagnostic now state) := by
  unfold consume
  apply ReapingProgram.bind (.any child (Runtime.read fd _))
  intro reply _
  cases reply with
  | error => exact .pure absent
  | ok value =>
    cases value with
    | pending => exact .pure absent
    | eof | data part =>
      repeat' first | exact .pure absent | (dsimp only; split) | split

private theorem consume_ready_exit_none {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (descriptors : List (UInt64 × Nat)) (ready : List Nat)
    (boot diagnostic : UInt64) (now : Nat) (state : State) (absent : state.exitCode = none) :
    ReapingProgram child (fun after => after.exitCode = none)
      (consumeReady descriptors ready boot diagnostic now state) := by
  induction descriptors generalizing ready state with
  | nil => cases ready <;> exact .pure absent
  | cons descriptor rest ih =>
    cases ready with
    | nil => exact .pure absent
    | cons flags more =>
      unfold consumeReady
      split
      · dsimp only [Bind.bind, Pure.pure, Program.bind]
        split
        · exact .pure absent
        · exact ih more state absent
      · apply ReapingProgram.bind (consume_exit_none child _ _ _ _ _ absent)
        intro after absentAfter
        dsimp only
        split
        · exact .pure absentAfter
        · exact ih more after absentAfter

private theorem after_send_exit_none (fuel : Nat) {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (path : ByteArray) (boot diagnostic : UInt64)
    (began duration now : Nat)
    (later : ∀ state, state.exitCode = none → ReapingProgram child (fun after => after.exitCode = none)
      (loop fuel child path boot diagnostic began duration state))
    (state : State) (absent : state.exitCode = none) :
    ReapingProgram child (fun after => after.exitCode = none)
      (afterSend fuel child path boot diagnostic began duration now state) := by
  unfold afterSend
  split
  · exact .pure absent
  · split
    · exact .pure absent
    · apply ReapingProgram.bind (.any child (Runtime.poll (events state boot diagnostic) 100))
      intro ready _
      cases ready with
      | error => exact .pure absent
      | ok ready =>
        apply ReapingProgram.bind (consume_ready_exit_none child _ _ _ _ _ _ absent)
        intro after absentAfter
        split
        · exact .pure absentAfter
        · exact later after absentAfter

private theorem connected_exit_none (fuel : Nat) {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (path : ByteArray) (boot diagnostic : UInt64)
    (began duration now : Nat)
    (later : ∀ state, state.exitCode = none → ReapingProgram child (fun after => after.exitCode = none)
      (loop fuel child path boot diagnostic began duration state))
    (state : State) (absent : state.exitCode = none) :
    ReapingProgram child (fun after => after.exitCode = none)
      (connectedProgram fuel child path boot diagnostic began duration now state) := by
  unfold connectedProgram
  split
  · exact .pure absent
  · split
    · exact .pure absent
    · dsimp only
      split
      · split
        · exact after_send_exit_none fuel child path boot diagnostic began duration now later state absent
        · rename_i fd selected
          apply ReapingProgram.bind (.any child (Runtime.perform {op := .write, first := fd, left := "C".toUTF8}))
          intro sent _
          split
          · exact after_send_exit_none fuel child path boot diagnostic began duration now later
              {state with sent := some now} absent
          · exact after_send_exit_none fuel child path boot diagnostic began duration now later
              (state.fail "VM cancellation transmission failed") absent
      · exact after_send_exit_none fuel child path boot diagnostic began duration now later state absent

-- §AR-application-verification.lifetime: Every newly known VM exit comes from
-- this actual child's successful tryWait. No deadline, signal, pipe EOF or
-- source error can manufacture a known exit code.
theorem loop_reaping_source (fuel : Nat) {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (path : ByteArray) (boot diagnostic : UInt64)
    (began duration : Nat) (state : State) (absent : state.exitCode = none) :
    ReapingProgram child (fun after => after.exitCode = none)
      (loop fuel child path boot diagnostic began duration state) := by
  induction fuel generalizing state with
  | zero => exact .pure absent
  | succ fuel ih =>
    unfold loop
    dsimp only [Program.effect, Program.bind]
    apply ReapingProgram.observation
    intro observed notReaped
    let waited : State := match (generalizing := false) observed with
      | .ok (some code) => { state with exitCode := some code }
      | .ok none => state
      | .error error => state.fail error
    have waitedAbsent : waited.exitCode = none := by
      cases observed with
      | error => exact absent
      | ok result =>
        cases result with
        | none => exact absent
        | some code => exact False.elim (notReaped code rfl)
    have normalized : ReapingProgram child (fun after => after.exitCode = none)
        (if waited.error.isSome then pure waited else do
          let clock ← Runtime.clock
          let .ok now := clock | return waited.fail "VM clock observation failed"
          if let some error := deadlineError waited began duration now then return waited.fail error
          let next ← if waited.connection.isNone then do
              let connected ← connect path
              match connected with
              | .error error => pure (waited.fail error.message)
              | .ok connection => pure { waited with connection }
            else pure waited
          connectedProgram fuel child path boot diagnostic began duration now next) := by
      split
      · exact .pure waitedAbsent
      · apply ReapingProgram.bind (.any child Runtime.clock)
        intro clock _
        cases clock with
        | error => exact .pure waitedAbsent
        | ok now =>
          dsimp only
          split
          · exact .pure waitedAbsent
          · split
            · apply ReapingProgram.bind (.any child (connect path))
              intro connected _
              cases connected with
              | error error =>
                exact connected_exit_none fuel child path boot diagnostic began duration now
                  (fun state absentState => ih state absentState) (waited.fail error.message) waitedAbsent
              | ok connection =>
                exact connected_exit_none fuel child path boot diagnostic began duration now
                  (fun state absentState => ih state absentState) {waited with connection} waitedAbsent
            · exact connected_exit_none fuel child path boot diagnostic began duration now
                (fun state absentState => ih state absentState) waited waitedAbsent
    set_option smartUnfolding false in
      with_unfolding_all exact normalized

theorem observe_exit_reaping_source (fuel : Nat) {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) :
    ReapingProgram child (fun result => result = none) (observeExit fuel child) := by
  induction fuel with
  | zero => exact .pure rfl
  | succ fuel ih =>
    unfold observeExit
    apply ReapingProgram.observation
    intro result notReaped
    cases result with
    | error => exact .pure rfl
    | ok result =>
      cases result with
      | some code => exact False.elim (notReaped code rfl)
      | none =>
        apply ReapingProgram.bind (.any child (Runtime.poll [] 100))
        intro ignored _
        exact ih

theorem reap_reaping_source {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (state : State) (absent : state.exitCode = none) :
    ReapingProgram child (fun after => after.exitCode = none) (reap child state) := by
  unfold reap
  simp only [absent, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  apply ReapingProgram.bind (.any child (Program.effect (.terminate child)))
  intro ignored _
  apply ReapingProgram.bind (observe_exit_reaping_source _ child)
  intro observed none
  subst observed
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  apply ReapingProgram.bind (.any child (Runtime.perform {op := .signal, first := child.pid.toUInt64, second := 9}))
  intro ignored _
  apply ReapingProgram.bind (observe_exit_reaping_source _ child)
  intro observed none
  subst observed
  exact .pure rfl

theorem initial_reaping_source {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (directory : String) (duration : Nat)
    (transport : Transport.State) (boot diagnostic : Reply) :
    ReapingProgram child (fun after => after.exitCode = none)
      (initialProgram child directory duration transport boot diagnostic) := by
  unfold initialProgram
  split
  · apply ReapingProgram.bind (.any child Runtime.clock)
    intro began _
    cases began with
    | error => exact .pure rfl
    | ok began => exact loop_reaping_source _ child _ _ _ _ _ _ rfl
  · exact .pure rfl

theorem final_reaping_source {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (state : State) (absent : state.exitCode = none) :
    ReapingProgram child (fun result => result.cleanup = "unknown") (finalProgram child state) := by
  unfold finalProgram
  apply ReapingProgram.bind (reap_reaping_source child state absent)
  intro reaped none
  have finish : ReapingProgram child (fun result => result.cleanup = "unknown")
      (pure (Result.ofState
        (if reaped.exitCode != some 33 then reaped.fail "VM ended without a complete exit" else reaped)
        (if (if reaped.exitCode != some 33 then reaped.fail "VM ended without a complete exit" else reaped).exitCode.isSome
          then "complete" else "unknown"))) := by
    apply ReapingProgram.pure
    simp only [none, Result.ofState, State.fail]
    rfl
  cases connection : reaped.connection with
  | none => exact finish
  | some fd =>
    apply ReapingProgram.bind (.any child (close fd))
    intro ignored _
    exact finish

-- §AR-host-boundary.interfaces: This view is the actual successful-spawn
-- continuation, with the original descriptor, initialization and finalization
-- source programs. It does not replace any process or syscall by a helper axiom.
def spawnedProgram (bundle : Validation.Bundle) (directory : String) (duration : Nat)
    (transport : Transport.State) (child : IO.Process.Child (arguments bundle directory).toStdioConfig) :
    Program Result := do
  let boot ← Program.effect (.descriptor child.stdout)
  let diagnostic ← Program.effect (.descriptor child.stderr)
  let state ← initialProgram child directory duration transport boot diagnostic
  finalProgram child state

theorem spawned_reaping_source (bundle : Validation.Bundle) (directory : String) (duration : Nat)
    (transport : Transport.State) (child : IO.Process.Child (arguments bundle directory).toStdioConfig) :
    ReapingProgram child (fun result => result.cleanup = "unknown")
      (spawnedProgram bundle directory duration transport child) := by
  unfold spawnedProgram
  apply ReapingProgram.bind (.any child (Program.effect (.descriptor child.stdout)))
  intro boot _
  apply ReapingProgram.bind (.any child (Program.effect (.descriptor child.stderr)))
  intro diagnostic _
  apply ReapingProgram.bind (initial_reaping_source child directory duration transport boot diagnostic)
  intro state absent
  exact final_reaping_source child state absent

theorem run_spawned_program (bundle : Validation.Bundle) (directory : String) (duration : Nat)
    (transport : Transport.State) :
    VirtualMachine.run bundle directory duration transport =
      (Program.effect (.spawn (arguments bundle directory))).bind (fun created => match created with
        | .error _ => pure ⟨transport, .empty, none, "unknown", some "VM process creation failed"⟩
        | .ok child => spawnedProgram bundle directory duration transport child) := by
  unfold VirtualMachine.run
  dsimp only
  apply congrArg (Program.bind (Program.effect (.spawn (arguments bundle directory))))
  funext created
  cases created with
  | error => rfl
  | ok child =>
    unfold spawnedProgram
    apply congrArg (Program.bind (Program.effect (.descriptor child.stdout)))
    funext boot
    apply congrArg (Program.bind (Program.effect (.descriptor child.stderr)))
    funext diagnostic
    unfold initialProgram finalProgram
    cases first : descriptor boot <;> cases second : descriptor diagnostic
    all_goals try rfl
    change (Runtime.clock.bind _) = ((Runtime.clock.bind _).bind _)
    apply Eq.trans ?_ (program_bind_assoc Runtime.clock _ _).symm
    apply congrArg (Program.bind Runtime.clock)
    funext began
    cases began <;> rfl

-- §FS-host-boundary.ownership: Known cleanup is sourced from the SAME actual
-- returned spawn/Child and a later successful tryWait. Unknown/error/lost
-- creation and waits are never promoted to a no-child or reaped certificate.
theorem actual_run_reaping_source (bundle : Validation.Bundle) (directory : String) (duration : Nat)
    (transport : Transport.State) {events : List Program.Event} {result : Result}
    (source : Program.Returns (VirtualMachine.run bundle directory duration transport) events result)
    (known : result.cleanup ≠ "unknown") :
    ∃ child status before after,
      events = .returned (.spawn (arguments bundle directory)) (.ok child) ::
        (before ++ .returned (.tryWait child) (.ok (some status)) :: after) := by
  rw [run_spawned_program] at source
  dsimp only [Program.effect, Program.bind] at source
  cases source with
  | call _ _ created tail result rest =>
    cases created with
    | error error =>
      obtain ⟨rfl, rfl⟩ := Program.returns_pure _ rest
      exact False.elim (known rfl)
    | ok child =>
      have actual : Program.Returns (spawnedProgram bundle directory duration transport child) tail result := rest
      rcases (spawned_reaping_source bundle directory duration transport child).returns actual with unknown |
          ⟨status, member⟩
      · exact False.elim (known unknown)
      · obtain ⟨before, after, trace⟩ := List.append_of_mem member
        exact ⟨child, status, before, after, by rw [trace]⟩

end LeanCage.Host.VirtualMachine
