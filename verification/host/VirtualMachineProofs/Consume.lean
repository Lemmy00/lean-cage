import VirtualMachineProofs.Runtime

namespace LeanCage.Host.VirtualMachine
open Filesystem

-- §AR-host-boundary.interfaces: This pure view is checked equal to the actual effect continuation.
def consumeResult (fd boot diagnostic : UInt64) (now : Nat) (state : State)
    (read : Filesystem.Result Runtime.Read) : State :=
  match read with
  | .error error => state.fail error.message
  | .ok .pending => state
  | .ok .eof =>
    if fd == 3 then { state with cancellation := true, controlOpen := false }
    else if fd == boot then { state with bootOpen := false }
    else if fd == diagnostic then { state with diagnosticOpen := false }
    else { state with channelEof := true, ended := some now, transport := state.transport.step .eof }
  | .ok (.data part) =>
    if fd == 3 then
      if part == "C".toUTF8 then { state with cancellation := true, controlOpen := false }
      else state.fail "invalid parent cancellation event"
    else if fd == boot then
      match collect state.boot part with
      | .error error => state.fail error
      | .ok bytes => { state with boot := bytes }
    else if fd == diagnostic then
      match collect state.diagnostic part with
      | .error error => state.fail error
      | .ok bytes => { state with diagnostic := bytes }
    else
      let transport := state.transport.step (.data part)
      match transport.error with
      | some error => ({ state with transport } : State).fail error.message
      | none => { state with transport }

def readBudget (fd boot diagnostic : UInt64) (state : State) : Nat :=
  if fd == 3 then 1
  else if fd == boot then min chunkMax (diagnosticMax + 1 - state.boot.size)
  else if fd == diagnostic then min chunkMax (diagnosticMax + 1 - state.diagnostic.size)
  else chunkMax

-- §FS-host-boundary.transport: The requested size is bounded before the native read allocates
-- bytes.
theorem read_budget_bound (fd boot diagnostic : UInt64) (state : State) :
    readBudget fd boot diagnostic state ≤ chunkMax := by
  unfold readBudget
  split
  · decide
  · split
    · exact Nat.min_le_left _ _
    · split
      · exact Nat.min_le_left _ _
      · exact Nat.le_refl _

theorem consume_factor (fd boot diagnostic : UInt64) (now : Nat) (state : State) :
    consume fd boot diagnostic now state =
      (Runtime.read fd (readBudget fd boot diagnostic state)).bind
        (fun read => pure (consumeResult fd boot diagnostic now state read)) := by
  unfold consume readBudget
  dsimp only
  congr 1
  funext read
  cases read with
  | error error => rfl
  | ok read =>
    cases read with
    | pending => rfl
    | eof =>
      simp only [consumeResult]
      split
      · rfl
      · split
        · rfl
        · split <;> rfl
    | data part =>
      simp only [consumeResult]
      split
      · split <;> rfl
      · split
        · cases collect state.boot part <;> rfl
        · split
          · cases collect state.diagnostic part <;> rfl
          · cases (state.transport.step (.data part)).error <;> rfl

theorem consume_returns (fd boot diagnostic : UInt64) (now : Nat) (state : State)
    {events : List Program.Event} {after : State}
    (run : Program.Returns (consume fd boot diagnostic now state) events after) :
    ∃ observed, Program.Returns (Runtime.read fd (readBudget fd boot diagnostic state)) events observed ∧
      after = consumeResult fd boot diagnostic now state observed := by
  rw [consume_factor] at run
  obtain ⟨first, observed, last, source, returned, shape⟩ := Program.returns_bind_split _ _ run
  obtain ⟨rfl, equal⟩ := Program.returns_pure _ returned
  simp only [List.append_nil] at shape
  cases shape
  exact ⟨observed, source, equal⟩

theorem consume_connection (fd boot diagnostic : UInt64) (now : Nat) (state : State)
    (observed : Filesystem.Result Runtime.Read) :
    (consumeResult fd boot diagnostic now state observed).connection = state.connection := by
  cases observed with
  | error error => rfl
  | ok observed =>
    cases observed with
    | pending => rfl
    | eof =>
      dsimp only [consumeResult]
      split
      · rfl
      · split
        · rfl
        · split <;> rfl
    | data part =>
      dsimp only [consumeResult]
      split
      · split <;> rfl
      · split
        · cases collect state.boot part <;> rfl
        · split
          · cases collect state.diagnostic part <;> rfl
          · cases (state.transport.step (.data part)).error <;> rfl

theorem collect_source (bytes part result : ByteArray) (run : collect bytes part = .ok result) :
    result = bytes ++ part ∧ result.size ≤ diagnosticMax := by
  unfold collect at run
  split at run
  · contradiction
  · rename_i bound
    cases run
    exact ⟨rfl, by simpa only [ByteArray.size_append] using Nat.le_of_not_gt bound⟩

def State.Bounded (state : State) : Prop :=
  state.transport.Bounded ∧ state.boot.size ≤ diagnosticMax ∧ state.diagnostic.size ≤ diagnosticMax

theorem consume_result_bounded (fd boot diagnostic : UInt64) (now : Nat) (state : State)
    (observed : Filesystem.Result Runtime.Read) (bound : state.Bounded) :
    (consumeResult fd boot diagnostic now state observed).Bounded := by
  cases observed with
  | error error => exact bound
  | ok observed =>
    cases observed with
    | pending => exact bound
    | eof =>
      dsimp only [consumeResult]
      split
      · exact bound
      · split
        · exact bound
        · split
          · exact bound
          · exact ⟨Transport.bounded_step _ bound.1 .eof, bound.2⟩
    | data part =>
      dsimp only [consumeResult]
      split
      · split <;> exact bound
      · split
        · cases collected : collect state.boot part with
          | error error => exact bound
          | ok bytes => exact ⟨bound.1, (collect_source _ _ _ collected).2, bound.2.2⟩
        · split
          · cases collected : collect state.diagnostic part with
            | error error => exact bound
            | ok bytes => exact ⟨bound.1, bound.2.1, (collect_source _ _ _ collected).2⟩
          · cases (state.transport.step (.data part)).error <;>
              exact ⟨Transport.bounded_step _ bound.1 (.data part), bound.2⟩

-- §FS-host-boundary.transport: Oversized diagnostics retain the previous bytes and report.
theorem boot_overflow_retains (boot diagnostic : UInt64) (now : Nat) (state : State) (part : ByteArray)
    (separate : boot ≠ 3) (oversized : diagnosticMax < state.boot.size + part.size) :
    consumeResult boot boot diagnostic now state (.ok (.data part)) =
      state.fail "VM diagnostic bound exceeded" := by
  simp [consumeResult, separate, collect, oversized]

theorem diagnostic_overflow_retains (boot diagnostic : UInt64) (now : Nat) (state : State)
    (part : ByteArray) (control : diagnostic ≠ 3) (separate : diagnostic ≠ boot)
    (oversized : diagnosticMax < state.diagnostic.size + part.size) :
    consumeResult diagnostic boot diagnostic now state (.ok (.data part)) =
      state.fail "VM diagnostic bound exceeded" := by
  simp [consumeResult, control, separate, collect, oversized]

theorem stream_source_one (state : Transport.State) (connection : Option UInt64)
    (fd : UInt64) (frame : Transport.Event) (observation : Program.Event)
    (selected : connection = some fd) (origin : ReadOrigin fd frame observation) :
    StreamSource state (state.step frame) connection [observation] :=
  ⟨[frame], rfl, .read selected origin .nil⟩

-- §FS-host-boundary.transport: Only the selected connection can supply decoder bytes or EOF.
theorem consume_result_source (fd boot diagnostic : UInt64) (now : Nat) (state : State)
    {events : List Program.Event} {observed : Filesystem.Result Runtime.Read}
    (selected : fd ≠ 3 → fd ≠ boot → fd ≠ diagnostic → state.connection = some fd)
    (run : Program.Returns (Runtime.read fd (readBudget fd boot diagnostic state)) events observed) :
    StreamSource state.transport (consumeResult fd boot diagnostic now state observed).transport
      state.connection events := by
  cases observed with
  | error error => exact stream_source_refl _ _ _
  | ok observed =>
    cases observed with
    | pending => exact stream_source_refl _ _ _
    | eof =>
      dsimp only [consumeResult]
      split
      · exact stream_source_refl _ _ _
      · rename_i control
        split
        · exact stream_source_refl _ _ _
        · rename_i bootDifferent
          split
          · exact stream_source_refl _ _ _
          · rename_i diagnosticDifferent
            obtain ⟨observation, shape, origin⟩ := runtime_read_eof fd _ run
            rw [shape]
            exact stream_source_one state.transport state.connection fd .eof observation
              (selected (by simpa using control) (by simpa using bootDifferent)
                (by simpa using diagnosticDifferent)) origin
    | data part =>
      dsimp only [consumeResult]
      split
      · split <;> exact stream_source_refl _ _ _
      · rename_i control
        split
        · cases collect state.boot part <;> exact stream_source_refl _ _ _
        · rename_i bootDifferent
          split
          · cases collect state.diagnostic part <;> exact stream_source_refl _ _ _
          · rename_i diagnosticDifferent
            obtain ⟨observation, shape, origin, _⟩ := runtime_read_data fd _ run
            rw [shape]
            have one := stream_source_one state.transport state.connection fd (.data part) observation
              (selected (by simpa using control) (by simpa using bootDifferent)
                (by simpa using diagnosticDifferent)) origin
            cases (state.transport.step (.data part)).error <;> exact one

theorem consume_source (fd boot diagnostic : UInt64) (now : Nat) (state : State)
    {events : List Program.Event} {after : State}
    (selected : fd ≠ 3 → fd ≠ boot → fd ≠ diagnostic → state.connection = some fd)
    (run : Program.Returns (consume fd boot diagnostic now state) events after) :
    after.connection = state.connection ∧
      StreamSource state.transport after.transport state.connection events ∧
      (state.Bounded → after.Bounded) := by
  obtain ⟨observed, source, rfl⟩ := consume_returns fd boot diagnostic now state run
  exact ⟨consume_connection fd boot diagnostic now state observed,
    consume_result_source fd boot diagnostic now state selected source,
    consume_result_bounded fd boot diagnostic now state observed⟩

end LeanCage.Host.VirtualMachine
