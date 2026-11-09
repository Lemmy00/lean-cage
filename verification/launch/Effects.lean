import Admission

namespace LeanCage.Entry

-- §AR-entry.effects: Recognize ordinary successful returns of individually specified operations.
def successfulReturn (request : Request) (reply : Reply) : Bool :=
  match request.op with
  | .dup2 | .dup3 => request.b ≤ 2147483647 && reply.1 == request.b
  | .setsid => 1 ≤ reply.1 && reply.1 ≤ 2147483647
  | .umask => reply.1 ≤ 511
  | .readByte => reply.1 == 1
  | .fsuid | .fsgid => request.a == 4294967295
  | .capget | .getresuid | .getresgid | .getgroups => true
  | .prctl =>
    if request.a == 21 || request.a == 23 then true
    else if request.a == 4 || request.a == 24 || request.a == 28 ||
        request.a == 38 || request.a == 47 then reply.1 == 0 else false
  | .exec | .exit | .write => false
  | _ => reply.1 == 0

-- §AR-entry.effects: A filter can synthesize a return without executing the requested syscall.
inductive ReturnOrigin where
  | kernel
  | intercepted
  deriving DecidableEq

-- §AR-entry.effects: prctl's operation code crosses the signed C-int ABI without truncation.
def primitiveInput (request : Request) : Bool :=
  match request.op with
  | .prctl => request.a ≤ 2147483647
  | _ => true

-- §FS-entry.provenance: Each premise concerns one operation and an actual kernel-origin return.
structure PrimitiveContract (fs : Filesystem) where
  returns : ReturnOrigin → State → Request → Reply → State → Prop
  successful : ∀ before request reply after,
    returns .kernel before request reply after → primitiveInput request = true →
      successfulReturn request reply = true →
      after = advance fs request before after
  seccompQuery : ∀ before request reply after,
    returns .kernel before request reply after → request.op = .prctl → request.a = 21 →
      reply.1 = 0 → before.filters = []

-- §AR-entry.effects: The broader execution relation retains intercepted calls and false successes.
inductive ReturnedTrace {fs : Filesystem} (platform : PrimitiveContract fs) :
    State → List (Request × Reply) → State → Prop
  | nil (state : State) : ReturnedTrace platform state [] state
  | cons {before middle after : State} (origin : ReturnOrigin) (request : Request) (reply : Reply)
      {trace : List (Request × Reply)}
      (effect : platform.returns origin before request reply middle)
      (rest : ReturnedTrace platform middle trace after) :
      ReturnedTrace platform before ((request, reply) :: trace) after

-- §AR-entry.caller: The native caller must prove this kernel-origin premise before composition.
-- Loss or blocking is any unfinished prefix; an intercepted return cannot supply this premise.
inductive KernelTrace {fs : Filesystem} (platform : PrimitiveContract fs) :
    State → List (Request × Reply) → State → Prop
  | nil (state : State) : KernelTrace platform state [] state
  | cons {before middle after : State} (request : Request) (reply : Reply)
      {trace : List (Request × Reply)}
      (effect : platform.returns .kernel before request reply middle)
      (rest : KernelTrace platform middle trace after) :
      KernelTrace platform before ((request, reply) :: trace) after

theorem kernel_trace_returned {fs : Filesystem} {platform : PrimitiveContract fs}
    {initial final : State} {trace : List (Request × Reply)}
    (execution : KernelTrace platform initial trace final) :
    ReturnedTrace platform initial trace final := by
  induction execution with
  | nil state => exact .nil state
  | cons request reply effect _ ih => exact .cons .kernel request reply effect ih

def GuardSound (command : Command) : Prop :=
  primitiveInput command.request = true ∧
    ∀ reply, command.expected.accepts reply = true → successfulReturn command.request reply = true

-- §AR-entry.effects: Only the concrete operations emitted by setup use the success/update rule.
theorem setup_guards_sound (p : Inputs) (normal : p.fault = "normal") : ∀ command ∈ setup p, GuardSound command := by
  intro command member
  simp only [setup, List.mem_append] at member
  rcases member with ((((h | h) | h) | h) | h) | h
  · simp only [signalSetup, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_filterMap] at h
    rcases h with (rfl | ⟨i, _, h⟩) | rfl
    · simp [GuardSound, primitiveInput, cmd, successfulReturn, Expected.accepts]
    · split at h <;> simp_all [cmd]
      cases h
      simp [GuardSound, primitiveInput, successfulReturn, Expected.accepts]
    · simp [GuardSound, primitiveInput, cmd, successfulReturn, Expected.accepts]
  · simp only [handshake, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | rfl | rfl | rfl
    · simp [normal] at h
    · simp [GuardSound, primitiveInput, cmd, successfulReturn, Expected.accepts]
    · simp [GuardSound, primitiveInput, cmd, successfulReturn, Expected.accepts]
    · simp only [GuardSound, primitiveInput, cmd, successfulReturn, Expected.accepts]
      refine ⟨True.intro, ?_⟩
      intro reply accepted
      simp only [Bool.and_eq_true] at accepted
      exact accepted.1
  · simp only [handleSetup, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;>
      simp [GuardSound, primitiveInput, cmd, successfulReturn, Expected.accepts]
  · simp only [rootSetup, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;>
      simp [GuardSound, primitiveInput, cmd, successfulReturn, Expected.accepts]
  · simp only [credentialSetup, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_map] at h
    rcases h with (((h | h) | h) | h) | h
    · rcases h with rfl | rfl <;> simp [GuardSound, primitiveInput, cmd, successfulReturn, Expected.accepts]
    · rcases h with rfl; simp [GuardSound, primitiveInput, cmd, successfulReturn, Expected.accepts]
    · obtain ⟨i, _, rfl⟩ := h; simp [GuardSound, primitiveInput, cmd, successfulReturn, Expected.accepts]
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [GuardSound, primitiveInput, cmd, successfulReturn, Expected.accepts]
    · simp [normal] at h
  · simp only [filterSetup, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;>
      simp [GuardSound, primitiveInput, cmd, successfulReturn, Expected.accepts]

theorem accepted_observed {fs : Filesystem} (platform : PrimitiveContract fs)
    {commands : List Command} {trace : List (Request × Reply)}
    (accepted : Accepted commands trace) (guards : ∀ command ∈ commands, GuardSound command)
    {initial final : State} (execution : KernelTrace platform initial trace final) :
    ∃ observed, final = afterObserved fs commands initial observed := by
  induction accepted generalizing initial with
  | nil => cases execution; exact ⟨fun _ => final, rfl⟩
  | cons command reply accepted rest ih =>
    cases execution with
    | cons _ _ effect remaining =>
      rename_i middle
      have sound := guards command (by simp)
      have update := platform.successful _ _ _ _ effect sound.1 (sound.2 reply accepted)
      obtain ⟨observed, result⟩ := ih (fun c member => guards c (by simp [member])) remaining
      refine ⟨fun n => match n with | 0 => middle | n + 1 => observed n, ?_⟩
      change final = afterObserved fs _ (advance fs command.request initial middle) observed
      rw [← update]
      exact result

theorem accepted_state {fs : Filesystem} (platform : PrimitiveContract fs)
    {commands : List Command} {trace : List (Request × Reply)}
    (accepted : Accepted commands trace) (guards : ∀ command ∈ commands, GuardSound command)
    (neutral : ∀ initial observed, afterObserved fs commands initial observed = after fs commands initial)
    {initial final : State} (execution : KernelTrace platform initial trace final) :
    final = after fs commands initial := by
  obtain ⟨observed, result⟩ := accepted_observed platform accepted guards execution
  exact result.trans (neutral initial observed)

theorem accepted_append {left right : List Command} {trace : List (Request × Reply)}
    (accepted : Accepted (left ++ right) trace) :
    ∃ first second, trace = first ++ second ∧ Accepted left first ∧ Accepted right second := by
  induction left generalizing trace with
  | nil => exact ⟨[], trace, rfl, .nil, accepted⟩
  | cons command rest ih =>
    cases accepted with
    | cons _ reply good remaining =>
      obtain ⟨first, second, rfl, a, b⟩ := ih remaining
      exact ⟨(command.request, reply) :: first, second, rfl, .cons command reply good a, b⟩

theorem returned_append {fs : Filesystem} {platform : PrimitiveContract fs}
    {initial final : State} {left right : List (Request × Reply)}
    (execution : KernelTrace platform initial (left ++ right) final) :
    ∃ middle, KernelTrace platform initial left middle ∧ KernelTrace platform middle right final := by
  induction left generalizing initial with
  | nil => exact ⟨initial, .nil initial, execution⟩
  | cons event rest ih =>
    cases execution with
    | cons request reply effect remaining =>
      obtain ⟨middle, a, b⟩ := ih remaining
      exact ⟨middle, .cons request reply effect a, b⟩

def beforeFilter (p : Inputs) : List Command :=
  signalSetup p ++ handshake p ++ handleSetup p ++ rootSetup p ++ credentialSetup p

-- §FS-entry.control: Later capset/dumpability operations absorb the permitted side effects.
theorem before_filter_collateral_neutral (fs : Filesystem) (p : Inputs) (initial : State)
    (normal : p.fault = "normal") (observed : Nat → State) :
    afterObserved fs (beforeFilter p) initial observed = after fs (beforeFilter p) initial := by
  exact entry_prefix_collateral_neutral fs p initial normal observed

theorem setup_filter_cut (p : Inputs) : setup p = beforeFilter p ++ filterSetup p := by
  simp only [setup, beforeFilter, List.append_assoc]

set_option maxRecDepth 10000 in
theorem before_filter_preserves (fs : Filesystem) (p : Inputs) (initial : State)
    (normal : p.fault = "normal") :
    (after fs (beforeFilter p) initial).filters = initial.filters := by
  rw [after_projection fs (beforeFilter p) initial State.filters filterStep (update_filters fs)]
  have norm : beforeFilter p = beforeFilter {p with fault := "normal"} := by
    simp [beforeFilter, signalSetup, handshake, handleSetup, rootSetup, credentialSetup, cmd, normal]
  rw [norm]
  rfl

-- §FS-entry.control: The actual GET_SECCOMP return supplies the absent inherited-filter premise.
theorem observed_no_inherited_filter {fs : Filesystem} (platform : PrimitiveContract fs)
    (p : Inputs) (normal : p.fault = "normal") {initial final : State}
    {trace : List (Request × Reply)} (accepted : Accepted (setup p) trace)
    (execution : KernelTrace platform initial trace final) : initial.filters = [] := by
  rw [setup_filter_cut] at accepted
  obtain ⟨first, second, rfl, leading, suffix⟩ := accepted_append accepted
  obtain ⟨middle, before, remaining⟩ := returned_append execution
  have current := accepted_state platform leading
    (fun command member => setup_guards_sound p normal command (by
      rw [setup_filter_cut]; exact List.mem_append_left _ member))
    (fun initial observed => before_filter_collateral_neutral fs p initial normal observed) before
  have filters : middle.filters = initial.filters := by
    rw [current, before_filter_preserves fs p initial normal]
  cases suffix with
  | cons command reply good rest =>
    cases remaining with
    | cons request response effect _ =>
      have zero : reply.1 = 0 := by simpa [filterSetup, cmd, Expected.accepts] using good
      have absent := platform.seccompQuery _ _ _ _ effect rfl rfl zero
      exact filters.symm.trans absent

theorem input_handle_bounds (p : Inputs) (valid : inputsValid p = true) :
    4 ≤ p.input.toNat ∧ 4 ≤ p.output.toNat ∧ 4 ≤ p.errors.toNat ∧ 4 ≤ p.failure.toNat := by
  simp only [inputsValid, handlesValid, Bool.and_eq_true, List.all_cons,
    List.all_nil, Bool.and_true, decide_eq_true_eq, UInt32.le_iff_toNat_le] at valid
  simp only [UInt32.toNat_ofNat] at valid
  omega

theorem input_handles_distinct (p : Inputs) (valid : inputsValid p = true) :
    [p.input, p.output, p.errors, p.failure].Pairwise (· ≠ ·) := by
  simp only [inputsValid, handlesValid, Bool.and_eq_true, bne_iff_ne] at valid
  simp_all [List.pairwise_cons]

theorem input_identity_specified (p : Inputs) (valid : inputsValid p = true) :
    p.uid ≠ 4294967295 := by
  have upper : p.uid ≤ 100999 := by
    simp only [inputsValid, Bool.and_eq_true, decide_eq_true_eq] at valid
    exact valid.1.1.1.1.1.2
  intro same
  exact (by decide : ¬ (4294967295 : UInt32) ≤ 100999) (same ▸ upper)

-- §FS-entry.control: Application checks and individual Linux effects establish these values.
theorem admission_value_state {fs : Filesystem} (platform : PrimitiveContract fs)
    (p : Inputs) (normal : p.fault = "normal") (initial current : State)
    (kernelWidth : initial.boundingCaps &&& 18446741874686296064 = 0)
    {trace : List (Request × Reply)} {request : Request}
    (control : AtExec (admission p) trace request)
    (effects : KernelTrace platform initial trace current) :
    Restricted fs p initial current ∧ request.op = .exec ∧ request.text = p.argv[0]! ∧
      request.args = p.argv ∧ request.data = environmentBytes := by
  obtain ⟨valid, accepted, target, _⟩ := admission_at_exec p control
  have reached := accepted_state platform accepted (setup_guards_sound p normal)
    (fun initial observed => setup_collateral_neutral fs p initial normal observed) effects
  have noInherited := observed_no_inherited_filter platform p normal accepted effects
  have bounds := input_handle_bounds p valid
  subst current
  obtain ⟨uid, gid, groups, effective, permitted, inheritable, ambient, securebits,
    dumpable, nnp, filters, mask, root, cwd, permissions⟩ :=
      after_values fs p initial normal (input_identity_specified p valid)
  refine ⟨?_, ?_⟩
  · exact ⟨uid, gid, groups, effective, permitted, inheritable,
      after_bounding_empty fs p initial normal kernelWidth, ambient, securebits, dumpable, nnp,
      by simpa [noInherited] using filters, after_signal_defaults fs p initial normal,
      mask, root, cwd, permissions,
      after_handle_objects fs p initial normal bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2⟩
  · subst request
    simp [execRequest, normal]

end LeanCage.Entry
