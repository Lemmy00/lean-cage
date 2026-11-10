import VirtualMachineProofs.Ready

namespace LeanCage.Host.VirtualMachine
open Filesystem

-- §AR-host-boundary.interfaces: These proof views are definitionally the real loop continuations.
def afterSend (fuel : Nat) {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (path : ByteArray) (boot diagnostic : UInt64)
    (began duration now : Nat) (state : State) : Program State := do
  if state.error.isSome then return state
  if state.channelEof && state.exitCode.isSome && !state.bootOpen && !state.diagnosticOpen then return state
  let descriptors := events state boot diagnostic
  let ready ← Runtime.poll descriptors 100
  let .ok ready := ready | return state.fail "VM readiness observation failed"
  let next ← consumeReady descriptors ready boot diagnostic now state
  if next.error.isSome then return next
  loop fuel child path boot diagnostic began duration next

def connectedProgram (fuel : Nat) {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (path : ByteArray) (boot diagnostic : UInt64)
    (began duration now : Nat) (state : State) : Program State := do
  if state.error.isSome then return state
  if state.exitCode.isSome && state.connection.isNone then return state.fail "VM failed to start"
  let state ← if state.cancellation && state.sent.isNone then
      match state.connection with
      | none => pure state
      | some fd => do
        let sent ← Runtime.perform { op := .write, first := fd, left := "C".toUTF8 }
        if sent.1 == 1 && sent.2.isEmpty then pure { state with sent := some now }
        else pure (state.fail "VM cancellation transmission failed")
    else pure state
  afterSend fuel child path boot diagnostic began duration now state

theorem after_send_progress (fuel : Nat) {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (path : ByteArray) (boot diagnostic : UInt64)
    (began duration now : Nat)
    (later : ∀ state trace after, Program.Returns
      (loop fuel child path boot diagnostic began duration state) trace after → Progress state after trace)
    (state : State) {trace : List Program.Event} {after : State}
    (run : Program.Returns (afterSend fuel child path boot diagnostic began duration now state) trace after) :
    Progress state after trace := by
  unfold afterSend at run
  split at run
  · obtain ⟨rfl, rfl⟩ := Program.returns_pure _ run
    exact .refl _ _
  · split at run
    · obtain ⟨rfl, rfl⟩ := Program.returns_pure _ run
      exact .refl _ _
    · obtain ⟨pollTrace, ready, tail, pollRun, rest, shape⟩ := Program.returns_bind_split _ _ run
      cases ready with
      | error error =>
        obtain ⟨rfl, rfl⟩ := Program.returns_pure _ rest
        exact .fail _ _ _
      | ok ready =>
        obtain ⟨first, next, last, consumed, ending, readShape⟩ := Program.returns_bind_split _ _ rest
        have firstProgress := consume_ready_progress (events state boot diagnostic) ready boot diagnostic now
          state (events_selected state boot diagnostic) consumed
        try dsimp only at ending
        split at ending
        · obtain ⟨rfl, equal⟩ := Program.returns_pure _ ending
          cases equal
          have all := (Progress.refl state pollTrace).trans firstProgress
          simpa only [shape, readShape, List.append_nil] using all
        · have all := ((Progress.refl state pollTrace).trans firstProgress).trans
            (later next last after ending)
          simpa only [shape, readShape, List.append_assoc] using all

theorem connected_progress (fuel : Nat) {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (path : ByteArray) (boot diagnostic : UInt64)
    (began duration now : Nat)
    (later : ∀ state trace after, Program.Returns
      (loop fuel child path boot diagnostic began duration state) trace after → Progress state after trace)
    (state : State) {trace : List Program.Event} {after : State}
    (run : Program.Returns (connectedProgram fuel child path boot diagnostic began duration now state) trace after) :
    Progress state after trace := by
  unfold connectedProgram at run
  split at run
  · obtain ⟨rfl, rfl⟩ := Program.returns_pure _ run
    exact .refl _ _
  · split at run
    · obtain ⟨rfl, rfl⟩ := Program.returns_pure _ run
      exact .fail _ _ _
    · try dsimp only at run
      split at run
      · split at run
        · exact after_send_progress fuel child path boot diagnostic began duration now later state run
        · rename_i fd selected
          dsimp only [Runtime.perform, Program.liftFilesystem, Filesystem.Program.effect, Program.bind] at run
          cases run with
          | call _ _ reply tail _ ending =>
            try dsimp only [Program.bind] at ending
            split at ending
            · have rest := after_send_progress fuel child path boot diagnostic began duration now later
                { state with sent := some now } ending
              have first : Progress state { state with sent := some now }
                  [.returned (.filesystem { op := .write, first := fd, left := "C".toUTF8 }) reply] :=
                .unchanged _ _ _ rfl rfl rfl (fun _ known => known)
              exact first.trans rest
            · have rest := after_send_progress fuel child path boot diagnostic began duration now later
                (state.fail "VM cancellation transmission failed") ending
              exact (Progress.fail state _ [_]).trans rest
      · exact after_send_progress fuel child path boot diagnostic began duration now later state run

-- §FS-host-boundary.transport: The complete actual loop produces one ordered read-derived stream.
theorem loop_progress (fuel : Nat) {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (path : ByteArray) (boot diagnostic : UInt64)
    (began duration : Nat) (state : State) {trace : List Program.Event} {after : State}
    (run : Program.Returns (loop fuel child path boot diagnostic began duration state) trace after) :
    Progress state after trace := by
  induction fuel generalizing state trace after with
  | zero =>
    obtain ⟨rfl, rfl⟩ := Program.returns_pure _ run
    exact .fail _ _ _
  | succ fuel ih =>
    unfold loop at run
    dsimp only [Program.effect, Program.bind] at run
    cases run with
    | call _ _ observed tail _ rest =>
      dsimp only [Program.bind] at rest
      let waited : State := match (generalizing := false) observed with
        | .ok (some code) => { state with exitCode := some code }
        | .ok none => state
        | .error error => state.fail error
      have normalized : Program.Returns (if waited.error.isSome then pure waited else do
        let clock ← Runtime.clock
        let .ok now := clock | return waited.fail "VM clock observation failed"
        if let some error := deadlineError waited began duration now then return waited.fail error
        let next ← if waited.connection.isNone then do
            let connected ← connect path
            match connected with
            | .error error => pure (waited.fail error.message)
            | .ok connection => pure { waited with connection }
          else pure waited
        connectedProgram fuel child path boot diagnostic began duration now next) tail after := by
        set_option smartUnfolding false in
          with_unfolding_all exact rest
      have rest := normalized
      have initial : Progress state waited [.returned (.tryWait child) observed] := by
        dsimp only [waited]
        cases observed with
        | error error => exact .fail _ _ _
        | ok value =>
          cases value <;> exact .unchanged _ _ _ rfl rfl rfl (fun _ known => known)
      have final : Progress waited after tail := by
        split at rest
        · obtain ⟨rfl, rfl⟩ := Program.returns_pure _ rest
          exact .refl _ _
        · obtain ⟨clockTrace, clock, ending, clockRun, rest, clockShape⟩ :=
            Program.returns_bind_split _ _ rest
          cases clock with
          | error error =>
            obtain ⟨rfl, rfl⟩ := Program.returns_pure _ rest
            exact .fail _ _ _
          | ok now =>
            try dsimp only at rest
            split at rest
            · obtain ⟨rfl, rfl⟩ := Program.returns_pure _ rest
              exact .fail _ _ _
            · try dsimp only at rest
              split at rest
              · rename_i absent
                obtain ⟨first, connected, last, source, ending, connectShape⟩ :=
                  Program.returns_bind_split _ _ rest
                cases connected with
                | error error =>
                  simp only [program_pure_bind] at ending
                  have next := connected_progress fuel child path boot diagnostic began duration now
                    (fun state trace after run => ih state run) (waited.fail error.message) ending
                  have earlier := (Progress.fail waited error.message (clockTrace ++ first)).trans next
                  simpa only [clockShape, connectShape, List.append_assoc] using earlier
                | ok connection =>
                  simp only [program_pure_bind] at ending
                  have next := connected_progress fuel child path boot diagnostic began duration now
                    (fun state trace after run => ih state run) { waited with connection } ending
                  have opened : Progress waited { waited with connection } (clockTrace ++ first) := by
                    apply Progress.unchanged waited { waited with connection } (clockTrace ++ first) rfl rfl rfl
                    intro fd known
                    have : waited.connection = none := by simpa using absent
                    rw [this] at known
                    cases known
                  have earlier := opened.trans next
                  simpa only [clockShape, connectShape, List.append_assoc] using earlier
              · simp only [program_pure_bind] at rest
                have next := connected_progress fuel child path boot diagnostic began duration now
                  (fun state trace after run => ih state run) waited rest
                have earlier := (Progress.refl waited clockTrace).trans next
                simpa only [clockShape] using earlier
      exact initial.trans final

end LeanCage.Host.VirtualMachine
