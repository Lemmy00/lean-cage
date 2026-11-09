import Effects

namespace LeanCage.Entry

-- §FS-entry.release: The read is cut from the executed setup, before any descriptor mutation.
def beforeRelease (p : Inputs) : List Command :=
  signalSetup p ++
    [cmd p 1 { op := .traceMe } (beforeHandles := true),
     cmd p 1 { op := .stop } (beforeHandles := true)]

def releaseCommand (p : Inputs) : Command :=
  cmd p 1 { op := .readByte, a := p.failure.toUInt64 } (.byte 165) true

def afterRelease (p : Inputs) : List Command :=
  handleSetup p ++ rootSetup p ++ credentialSetup p ++ filterSetup p

theorem setup_release_cut (p : Inputs) (normal : p.fault = "normal") :
    setup p = beforeRelease p ++ releaseCommand p :: afterRelease p := by
  simp [setup, beforeRelease, releaseCommand, afterRelease, handshake, normal,
    List.append_assoc]

def BeforeReleaseOp (request : Request) : Prop :=
  request.op = .signalMask ∨ request.op = .signalDefault ∨
    request.op = .traceMe ∨ request.op = .stop

theorem before_release_operations (p : Inputs) :
    ∀ command ∈ beforeRelease p, BeforeReleaseOp command.request := by
  intro command member
  simp only [beforeRelease, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with signal | rfl | rfl
  · simp only [signalSetup, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_filterMap] at signal
    rcases signal with (rfl | ⟨i, _, result⟩) | rfl
    · simp [BeforeReleaseOp, cmd]
    · split at result <;> simp_all [cmd]
      cases result
      simp [BeforeReleaseOp]
    · simp [BeforeReleaseOp, cmd]
  · simp [BeforeReleaseOp, cmd]
  · simp [BeforeReleaseOp, cmd]

theorem before_release_advance_handles (fs : Filesystem) (request : Request)
    (initial observed : State) (operation : BeforeReleaseOp request) :
    (advance fs request initial observed).handles = initial.handles := by
  rcases operation with op | op | op | op <;>
    simp [advance, collateral, update, op]

theorem before_release_advance_filters (fs : Filesystem) (request : Request)
    (initial observed : State) (operation : BeforeReleaseOp request) :
    (advance fs request initial observed).filters = initial.filters := by
  rcases operation with op | op | op | op <;>
    simp [advance, collateral, update, op]

-- §AR-entry.effects: Every intervening step uses the individual kernel-return contract.
theorem accepted_before_release_handles {fs : Filesystem} (platform : PrimitiveContract fs)
    {commands : List Command} {trace : List (Request × Reply)}
    (accepted : Accepted commands trace)
    (guards : ∀ command ∈ commands, GuardSound command)
    (operations : ∀ command ∈ commands, BeforeReleaseOp command.request)
    {initial final : State} (execution : KernelTrace platform initial trace final) :
    final.handles = initial.handles := by
  induction accepted generalizing initial with
  | nil => cases execution; rfl
  | cons command reply accepted rest ih =>
    cases execution with
    | cons _ _ effect remaining =>
      rename_i middle
      have guard := guards command (by simp)
      have step := platform.successful _ _ _ _ effect guard.1 (guard.2 reply accepted)
      have preserved := before_release_advance_handles fs command.request initial middle
        (operations command (by simp))
      obtain later := ih (fun command member => guards command (by simp [member]))
        (fun command member => operations command (by simp [member])) remaining
      exact later.trans ((congrArg State.handles step).trans preserved)

theorem accepted_before_release_filters {fs : Filesystem} (platform : PrimitiveContract fs)
    {commands : List Command} {trace : List (Request × Reply)}
    (accepted : Accepted commands trace)
    (guards : ∀ command ∈ commands, GuardSound command)
    (operations : ∀ command ∈ commands, BeforeReleaseOp command.request)
    {initial final : State} (execution : KernelTrace platform initial trace final) :
    final.filters = initial.filters := by
  induction accepted generalizing initial with
  | nil => cases execution; rfl
  | cons command reply accepted rest ih =>
    cases execution with
    | cons _ _ effect remaining =>
      rename_i middle
      have guard := guards command (by simp)
      have step := platform.successful _ _ _ _ effect guard.1 (guard.2 reply accepted)
      have preserved := before_release_advance_filters fs command.request initial middle
        (operations command (by simp))
      obtain later := ih (fun command member => guards command (by simp [member]))
        (fun command member => operations command (by simp [member])) remaining
      exact later.trans ((congrArg State.filters step).trans preserved)

-- §FS-entry.release: The actual read retains the original child endpoint and exact accepted byte.
theorem admission_release_read_cut {fs : Filesystem} (platform : PrimitiveContract fs)
    (p : Inputs) (normal : p.fault = "normal")
    {initial final : State} {trace : List (Request × Reply)} {target : Request}
    (control : AtExec (admission p) trace target)
    (execution : KernelTrace platform initial trace final) :
    ∃ before after reply atRead afterRead,
      trace = before ++ ((releaseCommand p).request, reply) :: after ∧
      Accepted (beforeRelease p) before ∧
      KernelTrace platform initial before atRead ∧
      platform.returns .kernel atRead (releaseCommand p).request reply afterRead ∧
      KernelTrace platform afterRead after final ∧
      atRead.handles = initial.handles ∧ reply.1 = 1 ∧ reply.2 = (⟨#[165]⟩ : ByteArray) := by
  obtain ⟨_, accepted, _, _⟩ := admission_at_exec p control
  rw [setup_release_cut p normal] at accepted
  obtain ⟨before, rest, rfl, leading, trailing⟩ := accepted_append accepted
  obtain ⟨atRead, leadingRun, remaining⟩ := returned_append execution
  cases trailing with
  | cons command reply good tail =>
    cases remaining with
    | cons _ _ effect suffix =>
      refine ⟨before, _, reply, atRead, _, rfl, leading, leadingRun, effect, suffix, ?_, ?_⟩
      · exact accepted_before_release_handles platform leading
          (fun command member => setup_guards_sound p normal command (by
            rw [setup_release_cut p normal]; exact List.mem_append_left _ member))
          (before_release_operations p) leadingRun
      · have checked : reply.1 = 1 ∧ (reply.2 == (⟨#[165]⟩ : ByteArray)) = true := by
          simpa [releaseCommand, cmd, Expected.accepts] using good
        refine ⟨checked.1, ?_⟩
        apply ByteArray.ext
        have bytes : (reply.2.data == #[165]) = true := checked.2
        simpa only [beq_iff_eq] using bytes

end LeanCage.Entry
