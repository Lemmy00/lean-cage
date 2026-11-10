import VirtualMachineProofs.Run

namespace LeanCage.Host.VirtualMachine
open Filesystem

-- §FS-host-boundary.ownership: VM control mutates neither host names nor object attributes.
def NamespacePassiveRequest (request : Request) : Prop :=
  match request.op with
  | .openAt => request.second = readFlags ∨ request.second = directoryFlags
  | .mkdirAt | .unlinkAt | .renameNew | .temporary | .setAttribute => False
  | _ => True

def BoundedEffect : {α : Type} → Effect α → Prop
  | _, .filesystem request =>
      (request.op = .read → 0 < request.second.toNat ∧ request.second.toNat ≤ chunkMax) ∧
      NamespacePassiveRequest request
  | _, _ => True

def BoundedEvent : Program.Event → Prop
  | .returned effect _ => BoundedEffect effect
  | .lost effect => BoundedEffect effect

-- §FS-host-boundary.transport: This source certificate includes every reply and lost prefix.
inductive ReadSafe {α : Type} : Program α → Prop where
  | pure (value : α) : ReadSafe (.pure value)
  | call {β : Type} (effect : Effect β) (next : β → Program α)
      (bound : BoundedEffect effect) (tail : ∀ reply, ReadSafe (next reply)) :
      ReadSafe (.call effect next)

theorem read_safe_bind {α β : Type} {program : Program α} {next : α → Program β}
    (before : ReadSafe program) (after : ∀ value, ReadSafe (next value)) :
    ReadSafe (program.bind next) := by
  induction before with
  | pure value => exact after value
  | call effect next bound tail ih => exact .call effect _ bound ih

theorem read_safe_prefix {α : Type} {program : Program α} {trace : List Program.Event}
    (safe : ReadSafe program) (run : Program.Prefix program trace) :
    ∀ event ∈ trace, BoundedEvent event := by
  induction run with
  | empty => simp
  | returned effect next reply tail run ih =>
    cases safe with
    | call _ _ bound following =>
      intro event member
      rcases List.mem_cons.mp member with rfl | member
      · exact bound
      · exact ih (following reply) event member
  | lost effect next =>
    cases safe with
    | call _ _ bound _ => simpa [BoundedEvent] using bound

theorem prefix_of_return_bind {α β : Type} {program : Program α} {next : α → Program β}
    {first last : List Program.Event} {value : α} (returned : Program.Returns program first value)
    (tail : Program.Prefix (next value) last) : Program.Prefix (program.bind next) (first ++ last) := by
  induction returned with
  | pure => exact tail
  | call effect rest reply events value before ih =>
    exact .returned effect (fun reply => (rest reply).bind next) reply _ (ih tail)

-- §FS-host-boundary.ownership: The shared source traversal also retains actual spawn arguments.
def ProfileEffect (spawnAllowed : IO.Process.SpawnArgs → Prop) : {α : Type} → Effect α → Prop
  | _, .spawn arguments => spawnAllowed arguments
  | _, other => BoundedEffect other

inductive SourceProfile (spawnAllowed : IO.Process.SpawnArgs → Prop) {α : Type} : Program α → Prop where
  | pure (value : α) : SourceProfile spawnAllowed (.pure value)
  | call {β : Type} (effect : Effect β) (next : β → Program α)
      (bound : ProfileEffect spawnAllowed effect) (tail : ∀ reply, SourceProfile spawnAllowed (next reply)) :
      SourceProfile spawnAllowed (.call effect next)

theorem source_profile_bind {α β : Type} {spawnAllowed : IO.Process.SpawnArgs → Prop}
    {program : Program α} {next : α → Program β} (before : SourceProfile spawnAllowed program)
    (after : ∀ value, SourceProfile spawnAllowed (next value)) : SourceProfile spawnAllowed (program.bind next) := by
  induction before with
  | pure value => exact after value
  | call effect next bound tail ih => exact .call effect _ bound ih

private theorem profile_read_bound {α : Type} {spawnAllowed : IO.Process.SpawnArgs → Prop} (effect : Effect α)
    (profile : ProfileEffect spawnAllowed effect) : BoundedEffect effect := by
  cases effect <;> first | exact profile | trivial

theorem source_profile_read_safe {α : Type} {spawnAllowed : IO.Process.SpawnArgs → Prop} {program : Program α}
    (source : SourceProfile spawnAllowed program) : ReadSafe program := by
  induction source with
  | pure => exact .pure _
  | call effect next bound following ih => exact .call effect next (profile_read_bound effect bound) ih

private theorem read_safe_true_profile {α : Type} {program : Program α}
    (source : ReadSafe program) : SourceProfile (fun _ => True) program := by
  induction source with
  | pure => exact .pure _
  | call effect next bound following ih =>
    apply SourceProfile.call effect next _ ih
    cases effect <;> first | exact bound | trivial

theorem perform_profile {spawnAllowed : IO.Process.SpawnArgs → Prop} (request : Request) (bound : BoundedEffect (.filesystem request)) :
    SourceProfile spawnAllowed (Runtime.perform request) :=
  .call (.filesystem request) _ bound (fun _ => .pure _)

theorem runtime_read_profile {spawnAllowed : IO.Process.SpawnArgs → Prop} (fd : UInt64) (amount : Nat) : SourceProfile spawnAllowed (Runtime.read fd amount) := by
  unfold Runtime.read
  split
  · exact .pure _
  · rename_i valid
    have valid : amount ≠ 0 ∧ amount ≤ chunkMax := by simpa using valid
    apply source_profile_bind (perform_profile _ ?_)
    · intro reply
      split
      · split <;> exact .pure _
      · split
        · exact .pure _
        · split <;> exact .pure _
    · constructor
      · intro _
        have fit : amount < 2 ^ 64 := by
          have : chunkMax < 2 ^ 64 := by decide
          omega
        simpa only [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt fit] using
          And.intro (Nat.pos_of_ne_zero valid.1) valid.2
      · trivial

theorem consume_profile {spawnAllowed : IO.Process.SpawnArgs → Prop} (fd boot diagnostic : UInt64) (now : Nat) (state : State) :
    SourceProfile spawnAllowed (consume fd boot diagnostic now state) := by
  rw [consume_factor]
  exact source_profile_bind (runtime_read_profile _ _) (fun _ => .pure _)

theorem runtime_clock_profile {spawnAllowed : IO.Process.SpawnArgs → Prop} : SourceProfile spawnAllowed Runtime.clock := by
  unfold Runtime.clock
  apply source_profile_bind (perform_profile _ (by constructor; exact (fun impossible => by cases impossible); trivial))
  intro reply
  split
  · exact .pure _
  · dsimp only
    split <;> exact .pure _

theorem runtime_poll_profile {spawnAllowed : IO.Process.SpawnArgs → Prop} (descriptors : List (UInt64 × Nat)) (milliseconds : Nat) :
    SourceProfile spawnAllowed (Runtime.poll descriptors milliseconds) := by
  unfold Runtime.poll
  split
  · exact .pure _
  · apply source_profile_bind (perform_profile _ (by constructor; exact (fun impossible => by cases impossible); trivial))
    intro reply
    split
    · exact .pure _
    · split <;> exact .pure _

theorem close_profile {spawnAllowed : IO.Process.SpawnArgs → Prop} (fd : UInt64) : SourceProfile spawnAllowed (close fd) :=
  source_profile_bind (perform_profile _ (by constructor; exact (fun impossible => by cases impossible); trivial)) (fun _ => .pure _)

theorem connect_profile {spawnAllowed : IO.Process.SpawnArgs → Prop} (path : ByteArray) : SourceProfile spawnAllowed (connect path) := by
  unfold connect
  split
  · exact .pure _
  · apply source_profile_bind (perform_profile _ (by constructor; exact (fun impossible => by cases impossible); trivial))
    intro created
    split
    · apply source_profile_bind (perform_profile _ (by constructor; exact (fun impossible => by cases impossible); trivial))
      intro connected
      split
      · exact .pure _
      · apply source_profile_bind (close_profile _)
        intro result
        split <;> exact .pure _
    · exact .pure _

theorem consume_ready_profile {spawnAllowed : IO.Process.SpawnArgs → Prop} (descriptors : List (UInt64 × Nat)) (ready : List Nat)
    (boot diagnostic : UInt64) (now : Nat) (state : State) :
    SourceProfile spawnAllowed (consumeReady descriptors ready boot diagnostic now state) := by
  induction descriptors generalizing ready state with
  | nil => cases ready <;> exact .pure _
  | cons descriptor descriptors ih =>
    cases descriptor with
    | mk fd flags =>
      cases ready with
      | nil => exact .pure _
      | cons flag ready =>
        unfold consumeReady
        dsimp only
        split
        · simp only [program_pure_bind]
          split
          · exact .pure _
          · exact ih ready state
        · apply source_profile_bind (consume_profile fd boot diagnostic now state)
          intro next
          split
          · exact .pure _
          · exact ih ready next

theorem after_send_profile {spawnAllowed : IO.Process.SpawnArgs → Prop} (fuel : Nat) {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (path : ByteArray) (boot diagnostic : UInt64)
    (began duration now : Nat) (state : State)
    (later : ∀ next, SourceProfile spawnAllowed (loop fuel child path boot diagnostic began duration next)) :
    SourceProfile spawnAllowed (afterSend fuel child path boot diagnostic began duration now state) := by
  unfold afterSend
  split
  · exact .pure _
  · split
    · exact .pure _
    · apply source_profile_bind (runtime_poll_profile _ _)
      intro ready
      cases ready with
      | error error => exact .pure _
      | ok ready =>
        apply source_profile_bind (consume_ready_profile _ _ _ _ _ _)
        intro next
        split
        · exact .pure _
        · exact later next

theorem connected_profile {spawnAllowed : IO.Process.SpawnArgs → Prop} (fuel : Nat) {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (path : ByteArray) (boot diagnostic : UInt64)
    (began duration now : Nat) (state : State)
    (later : ∀ next, SourceProfile spawnAllowed (loop fuel child path boot diagnostic began duration next)) :
    SourceProfile spawnAllowed (connectedProgram fuel child path boot diagnostic began duration now state) := by
  unfold connectedProgram
  split
  · exact .pure _
  · split
    · exact .pure _
    · dsimp only
      split
      · split
        · simp only [program_pure_bind]
          exact after_send_profile _ _ _ _ _ _ _ _ _ later
        · apply source_profile_bind (perform_profile _ (by constructor; exact (fun impossible => by cases impossible); trivial))
          intro reply
          split <;> simp only [program_pure_bind] <;>
            exact after_send_profile _ _ _ _ _ _ _ _ _ later
      · simp only [program_pure_bind]
        exact after_send_profile _ _ _ _ _ _ _ _ _ later

-- §FS-host-boundary.transport: All emitted reads remain bounded even if the last operation is lost.
theorem loop_profile {spawnAllowed : IO.Process.SpawnArgs → Prop} (fuel : Nat) {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (path : ByteArray) (boot diagnostic : UInt64)
    (began duration : Nat) (state : State) :
    SourceProfile spawnAllowed (loop fuel child path boot diagnostic began duration state) := by
  induction fuel generalizing state with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold loop
    dsimp only [Program.effect, Program.bind]
    apply SourceProfile.call _ _ (by trivial)
    intro observed
    dsimp only [Program.bind]
    let waited : State := match (generalizing := false) observed with
      | .ok (some code) => { state with exitCode := some code }
      | .ok none => state
      | .error error => state.fail error
    have safe : SourceProfile spawnAllowed (if waited.error.isSome then pure waited else do
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
      · exact .pure _
      · apply source_profile_bind runtime_clock_profile
        intro clock
        cases clock with
        | error error => exact .pure _
        | ok now =>
          dsimp only
          split
          · exact .pure _
          · try dsimp only
            split
            · apply source_profile_bind (connect_profile path)
              intro connected
              cases connected <;> simp only [program_pure_bind] <;>
                exact connected_profile _ _ _ _ _ _ _ _ _ ih
            · simp only [program_pure_bind]
              exact connected_profile _ _ _ _ _ _ _ _ _ ih
    set_option smartUnfolding false in
      with_unfolding_all exact safe

theorem observe_exit_profile {spawnAllowed : IO.Process.SpawnArgs → Prop} (fuel : Nat) {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) : SourceProfile spawnAllowed (observeExit fuel child) := by
  induction fuel with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold observeExit
    apply SourceProfile.call _ _ (by trivial)
    intro observed
    dsimp only [Program.bind]
    cases observed with
    | error error => exact .pure _
    | ok status =>
      cases status with
      | some code => exact .pure _
      | none => exact source_profile_bind (runtime_poll_profile [] 100) (fun _ => ih)

theorem reap_profile {spawnAllowed : IO.Process.SpawnArgs → Prop} {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (state : State) : SourceProfile spawnAllowed (reap child state) := by
  unfold reap
  split
  · exact .pure _
  · apply SourceProfile.call _ _ (by trivial)
    intro ignored
    dsimp only [Program.bind]
    apply source_profile_bind (observe_exit_profile 30 child)
    intro observed
    split
    · exact .pure _
    · apply source_profile_bind (perform_profile _ (by constructor; exact (fun impossible => by cases impossible); trivial))
      intro ignored
      exact source_profile_bind (observe_exit_profile 50 child) (fun _ => .pure _)

theorem final_program_profile {spawnAllowed : IO.Process.SpawnArgs → Prop} {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (state : State) : SourceProfile spawnAllowed (finalProgram child state) := by
  unfold finalProgram
  apply source_profile_bind (reap_profile child state)
  intro reaped
  cases connection : reaped.connection with
  | none => exact .pure _
  | some fd =>
    exact source_profile_bind (close_profile fd) (fun _ => .pure _)

-- §FS-host-boundary.acceptance: Lost effects have the same bounded source request as returning
-- ones.
theorem run_profile {spawnAllowed : IO.Process.SpawnArgs → Prop} (bundle : Validation.Bundle) (directory : String) (duration : Nat)
    (transport : Transport.State) (allowed : spawnAllowed (arguments bundle directory)) : SourceProfile spawnAllowed (VirtualMachine.run bundle directory duration transport) := by
  unfold VirtualMachine.run
  dsimp only [Program.effect, Program.bind]
  apply SourceProfile.call (.spawn (arguments bundle directory)) _ allowed
  intro created
  dsimp only [Program.bind]
  cases created with
  | error error => exact .pure _
  | ok child =>
    apply SourceProfile.call _ _ (by trivial)
    intro boot
    dsimp only [Program.effect, Program.bind]
    apply SourceProfile.call _ _ (by trivial)
    intro diagnostic
    dsimp only [Program.bind]
    cases firstDescriptor : descriptor boot with
    | none =>
      have safe := final_program_profile (spawnAllowed := spawnAllowed) child
        (({ transport } : State).fail "VM stream ownership could not be established")
      set_option smartUnfolding false in with_unfolding_all exact safe
    | some bootFd =>
      cases secondDescriptor : descriptor diagnostic with
      | none =>
        have safe := final_program_profile (spawnAllowed := spawnAllowed) child
          (({ transport } : State).fail "VM stream ownership could not be established")
        set_option smartUnfolding false in with_unfolding_all exact safe
      | some diagnosticFd =>
        apply source_profile_bind runtime_clock_profile
        intro began
        cases began with
        | error error =>
          have safe := final_program_profile (spawnAllowed := spawnAllowed) child (({ transport } : State).fail error.message)
          set_option smartUnfolding false in with_unfolding_all exact safe
        | ok began =>
          apply source_profile_bind (loop_profile _ child _ bootFd diagnosticFd began duration { transport })
          intro state
          have safe := final_program_profile (spawnAllowed := spawnAllowed) child state
          set_option smartUnfolding false in with_unfolding_all exact safe

-- §FS-host-boundary.transport: Existing read-bound interfaces consume the stronger source proof.
theorem perform_read_safe (request : Request) (bound : BoundedEffect (.filesystem request)) :
    ReadSafe (Runtime.perform request) :=
  source_profile_read_safe (perform_profile (spawnAllowed := fun _ => True) request bound)

theorem runtime_read_safe (fd : UInt64) (amount : Nat) : ReadSafe (Runtime.read fd amount) :=
  source_profile_read_safe (runtime_read_profile (spawnAllowed := fun _ => True) fd amount)

theorem consume_read_safe (fd boot diagnostic : UInt64) (now : Nat) (state : State) :
    ReadSafe (consume fd boot diagnostic now state) :=
  source_profile_read_safe (consume_profile (spawnAllowed := fun _ => True) fd boot diagnostic now state)

theorem runtime_clock_safe : ReadSafe Runtime.clock :=
  source_profile_read_safe (runtime_clock_profile (spawnAllowed := fun _ => True) )

theorem runtime_poll_safe (descriptors : List (UInt64 × Nat)) (milliseconds : Nat) :
    ReadSafe (Runtime.poll descriptors milliseconds) :=
  source_profile_read_safe (runtime_poll_profile (spawnAllowed := fun _ => True) descriptors milliseconds)

theorem close_read_safe (fd : UInt64) : ReadSafe (close fd) :=
  source_profile_read_safe (close_profile (spawnAllowed := fun _ => True) fd)

theorem connect_read_safe (path : ByteArray) : ReadSafe (connect path) :=
  source_profile_read_safe (connect_profile (spawnAllowed := fun _ => True) path)

theorem consume_ready_read_safe (descriptors : List (UInt64 × Nat)) (ready : List Nat)
    (boot diagnostic : UInt64) (now : Nat) (state : State) :
    ReadSafe (consumeReady descriptors ready boot diagnostic now state) :=
  source_profile_read_safe (consume_ready_profile (spawnAllowed := fun _ => True) descriptors ready boot diagnostic now state)

theorem after_send_read_safe (fuel : Nat) {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (path : ByteArray) (boot diagnostic : UInt64)
    (began duration now : Nat) (state : State)
    (later : ∀ next, ReadSafe (loop fuel child path boot diagnostic began duration next)) :
    ReadSafe (afterSend fuel child path boot diagnostic began duration now state) :=
  source_profile_read_safe (after_send_profile (spawnAllowed := fun _ => True) fuel child path boot diagnostic began duration now state (fun next => read_safe_true_profile (later next)))

theorem connected_read_safe (fuel : Nat) {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (path : ByteArray) (boot diagnostic : UInt64)
    (began duration now : Nat) (state : State)
    (later : ∀ next, ReadSafe (loop fuel child path boot diagnostic began duration next)) :
    ReadSafe (connectedProgram fuel child path boot diagnostic began duration now state) :=
  source_profile_read_safe (connected_profile (spawnAllowed := fun _ => True) fuel child path boot diagnostic began duration now state (fun next => read_safe_true_profile (later next)))

theorem loop_read_safe (fuel : Nat) {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (path : ByteArray) (boot diagnostic : UInt64)
    (began duration : Nat) (state : State) :
    ReadSafe (loop fuel child path boot diagnostic began duration state) :=
  source_profile_read_safe (loop_profile (spawnAllowed := fun _ => True) fuel child path boot diagnostic began duration state)

theorem observe_exit_read_safe (fuel : Nat) {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) : ReadSafe (observeExit fuel child) :=
  source_profile_read_safe (observe_exit_profile (spawnAllowed := fun _ => True) fuel child)

theorem reap_read_safe {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (state : State) : ReadSafe (reap child state) :=
  source_profile_read_safe (reap_profile (spawnAllowed := fun _ => True) child state)

theorem final_program_read_safe {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (state : State) : ReadSafe (finalProgram child state) :=
  source_profile_read_safe (final_program_profile (spawnAllowed := fun _ => True) child state)

theorem run_read_safe (bundle : Validation.Bundle) (directory : String) (duration : Nat)
    (transport : Transport.State) : ReadSafe (VirtualMachine.run bundle directory duration transport) :=
  source_profile_read_safe (run_profile (spawnAllowed := fun _ => True) bundle directory duration transport True.intro)

theorem actual_prefix_read_bounds (bundle : Validation.Bundle) (directory : String) (duration : Nat)
    (transport : Transport.State) {trace : List Program.Event}
    (prefixRun : Program.Prefix (VirtualMachine.run bundle directory duration transport) trace) :
    ∀ event ∈ trace, BoundedEvent event :=
  read_safe_prefix (run_read_safe bundle directory duration transport) prefixRun

def ProfileEvent (spawnAllowed : IO.Process.SpawnArgs → Prop) : Program.Event → Prop
  | .returned effect _ => ProfileEffect spawnAllowed effect
  | .lost effect => ProfileEffect spawnAllowed effect

theorem source_profile_prefix {α : Type} {spawnAllowed : IO.Process.SpawnArgs → Prop}
    {program : Program α} {events : List Program.Event} (profile : SourceProfile spawnAllowed program)
    (active : Program.Prefix program events) : ∀ event ∈ events, ProfileEvent spawnAllowed event := by
  induction active with
  | empty => simp
  | returned effect next reply events source ih =>
    cases profile with
    | call _ _ allowed following =>
      intro event member
      rcases List.mem_cons.mp member with rfl | later
      · exact allowed
      · exact ih (following reply) event later
  | lost effect next =>
    cases profile with
    | call _ _ allowed following => simpa [ProfileEvent] using allowed

def SpawnEvent (allowed : IO.Process.SpawnArgs → Prop) : Program.Event → Prop
  | .returned (.spawn arguments) _ => allowed arguments
  | .lost (.spawn arguments) => allowed arguments
  | _ => True

-- §FS-host-boundary.ownership: Every actual/lost spawn uses these fixed owned-run arguments.
theorem actual_prefix_spawn_arguments (bundle : Validation.Bundle) (directory : String) (duration : Nat)
    (transport : Transport.State) {events : List Program.Event}
    (active : Program.Prefix (VirtualMachine.run bundle directory duration transport) events) :
    ∀ event ∈ events, SpawnEvent (fun args => args = arguments bundle directory) event := by
  have source := run_profile (spawnAllowed := fun args => args = arguments bundle directory)
    bundle directory duration transport rfl
  intro event member
  have observed := source_profile_prefix source active event member
  cases event with
  | returned effect reply => cases effect <;> first | exact observed | trivial
  | lost effect => cases effect <;> first | exact observed | trivial

theorem lost_read_not_observation (fd : UInt64) (frame : Transport.Event) (request : Request) :
    ¬ ReadOrigin fd frame (.lost (.filesystem request)) := by
  intro origin
  cases origin

end LeanCage.Host.VirtualMachine
