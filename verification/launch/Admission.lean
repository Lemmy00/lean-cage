import StateProofs

namespace LeanCage.Entry

-- §FS-entry.control: Check every possible future request, including error and unexpected returns.
inductive Only {α : Type} (allowed : Request → Prop) : Script α → Prop
  | pure (value : α) : Only allowed (.pure value)
  | call (request : Request) (next : Reply → Script α) (valid : allowed request)
      (rest : ∀ reply, Only allowed (next reply)) : Only allowed (.call request next)

theorem only_bind {α β : Type} {allowed : Request → Prop} {program : Script α}
    {next : α → Script β} (before : Only allowed program)
    (after : ∀ value, Only allowed (next value)) : Only allowed (program.bind next) := by
  induction before with
  | pure value => exact after value
  | call request rest valid _ ih => exact .call request _ valid (fun reply => ih reply)

theorem only_mono {α : Type} {allowed stronger : Request → Prop} {program : Script α}
    (safe : Only stronger program) (weaken : ∀ request, stronger request → allowed request) :
    Only allowed program := by
  induction safe with
  | pure value => exact .pure value
  | call request rest valid _ ih => exact .call request _ (weaken request valid) ih

theorem only_prefix {α : Type} {allowed : Request → Prop} {program last : Script α}
    {trace : List (Request × Reply)} (safe : Only allowed program)
    (execution : Script.Prefix program trace last) :
    (∀ event ∈ trace, allowed event.1) ∧ Only allowed last := by
  induction execution with
  | refl => exact ⟨by simp, safe⟩
  | step request next reply rest ih =>
    cases safe with
    | call _ _ valid remaining =>
      obtain ⟨history, final⟩ := ih (remaining reply)
      exact ⟨by simpa using And.intro valid history, final⟩

-- §FS-entry.control: Failure reporting can write or exit; no response can reopen setup.
theorem terminate_only (p : Inputs) (failure : Failure) :
    Only (fun request => request.op = .write ∨ request.op = .exit)
      (terminate Script.effect p failure) := by
  unfold terminate
  split <;> simp only [bind, Script.bind, Script.effect, pure]
  · exact .call _ _ (Or.inl rfl) (fun _ => .call _ _ (Or.inr rfl) (fun _ => .pure _))
  · exact .call _ _ (Or.inr rfl) (fun _ => .pure _)

theorem failure_never_exec {p : Inputs} {failure : Failure}
    {trace : List (Request × Reply)} {last : Script UInt32}
    (execution : Script.Prefix (terminate Script.effect p failure) trace last) :
    ∀ event ∈ trace, event.1.op ≠ .exec := by
  intro event member
  have fact := (only_prefix (terminate_only p failure) execution).1 event member
  rcases fact with h | h <;> simp [h]

theorem terminate_no_exec (p : Inputs) (failure : Failure) :
    Only (fun request => request.op ≠ .exec) (terminate Script.effect p failure) := by
  apply only_mono (terminate_only p failure)
  intro request h
  rcases h with h | h <;> simp [h]

-- §FS-entry.check: The post-setup check branch has no exec request for any result.
theorem finish_preflight_no_exec (p : Inputs) (check : p.preflight = true)
    (outcome : Option Failure) :
    Only (fun request => request.op ≠ .exec) (finishSetup Script.effect p outcome) := by
  cases outcome with
  | some failure => exact terminate_no_exec p failure
  | none =>
    simp only [finishSetup, check, ↓reduceIte, bind, Script.effect, Script.bind, pure]
    exact .call _ _ (by decide) (fun _ => .call _ _ (by decide) (fun _ => .pure _))

theorem commands_only {α : Type} (commands : List Command) (allowed : Request → Prop)
    (next : Option Failure → Script α)
    (setupSafe : ∀ command ∈ commands, allowed command.request)
    (finishSafe : ∀ outcome, Only allowed (next outcome)) :
    Only allowed ((runCommands Script.effect commands).bind next) := by
  induction commands with
  | nil => exact finishSafe none
  | cons command rest ih =>
    change Only allowed (.call command.request (fun reply =>
      (if command.expected.accepts reply then runCommands Script.effect rest
        else .pure (some (commandFailure command reply))).bind next))
    apply Only.call _ _ (setupSafe command (by simp))
    intro reply
    split
    · apply ih
      intro c member
      exact setupSafe c (by simp [member])
    · exact finishSafe (some (commandFailure command reply))

theorem setup_no_exec (p : Inputs) :
    ∀ command ∈ setup p, command.request.op ≠ .exec := by
  intro command member
  simp only [setup, List.mem_append] at member
  rcases member with ((((h | h) | h) | h) | h) | h
  · simp only [signalSetup, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_filterMap] at h
    rcases h with (rfl | ⟨i, _, h⟩) | rfl
    · simp [cmd]
    · split at h <;> simp_all [cmd]
      cases h
      simp
    · simp [cmd]
  · simp only [handshake, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | rfl | rfl | rfl
    · split at h <;> simp_all [cmd]
    · simp [cmd]
    · simp [cmd]
    · simp [cmd]
  · simp only [handleSetup, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [cmd]
  · simp only [rootSetup, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> simp [cmd]
  · simp only [credentialSetup, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_map] at h
    rcases h with (((h | h) | h) | h) | h
    · rcases h with rfl | rfl <;> simp [cmd]
    · rcases h with rfl; simp [cmd]
    · obtain ⟨i, _, rfl⟩ := h; simp [cmd]
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [cmd]
    · split at h <;> simp_all [cmd]
  · simp only [filterSetup, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> simp [cmd]

theorem preflight_no_exec (p : Inputs) (check : p.preflight = true) :
    Only (fun request => request.op ≠ .exec) (admission p) := by
  unfold admission execute
  split
  · simpa only [bind, Script.bind, pure] using terminate_no_exec p ⟨p.failure, 1, 22⟩
  · exact commands_only _ _ _ (setup_no_exec p) (finish_preflight_no_exec p check)

theorem preflight_prefix_no_exec {p : Inputs} (check : p.preflight = true)
    {trace : List (Request × Reply)} {last : Script UInt32}
    (execution : Script.Prefix (admission p) trace last) :
    (∀ event ∈ trace, event.1.op ≠ .exec) ∧ Only (fun request => request.op ≠ .exec) last :=
  only_prefix (preflight_no_exec p check) execution

-- §FS-entry.control: A pending exec in any finite prefix, with arbitrary preceding returns.
inductive AtExec {α : Type} : Script α → List (Request × Reply) → Request → Prop
  | ready (request : Request) (next : Reply → Script α) (exec : request.op = .exec) :
      AtExec (.call request next) [] request
  | returned (request : Request) (next : Reply → Script α) (reply : Reply)
      {trace : List (Request × Reply)} {target : Request}
      (rest : AtExec (next reply) trace target) :
      AtExec (.call request next) ((request, reply) :: trace) target

theorem only_excludes_exec {α : Type} {program : Script α}
    (safe : Only (fun request => request.op ≠ .exec) program)
    {trace : List (Request × Reply)} {target : Request} : ¬AtExec program trace target := by
  intro h
  induction h with
  | ready request next exec => cases safe with | call _ _ valid _ => exact valid exec
  | returned request next reply rest ih => cases safe with | call _ _ _ rest => exact ih (rest reply)

inductive Accepted : List Command → List (Request × Reply) → Prop
  | nil : Accepted [] []
  | cons (command : Command) (reply : Reply) {commands : List Command} {trace : List (Request × Reply)}
      (accepted : command.expected.accepts reply = true) (rest : Accepted commands trace) :
      Accepted (command :: commands) ((command.request, reply) :: trace)

theorem finish_at_exec (p : Inputs) {trace : List (Request × Reply)} {target : Request}
    (h : AtExec (finishSetup Script.effect p none) trace target) :
    trace = [] ∧ target = execRequest p ∧ p.preflight = false := by
  cases check : p.preflight with
  | true => exact False.elim (only_excludes_exec (finish_preflight_no_exec p check none) h)
  | false =>
    simp only [finishSetup, check, Bool.false_eq_true, ↓reduceIte, bind, Script.bind,
      Script.effect] at h
    cases h with
    | ready => exact ⟨rfl, rfl, rfl⟩
    | returned request next reply rest =>
      exact False.elim (only_excludes_exec (terminate_no_exec p ⟨3, 8, replyError reply⟩) rest)

theorem commands_at_exec (p : Inputs) (commands : List Command)
    (noExec : ∀ command ∈ commands, command.request.op ≠ .exec)
    {trace : List (Request × Reply)} {target : Request}
    (h : AtExec ((runCommands Script.effect commands).bind (finishSetup Script.effect p)) trace target) :
    Accepted commands trace ∧ target = execRequest p ∧ p.preflight = false := by
  induction commands generalizing trace with
  | nil =>
    obtain ⟨rfl, rfl, check⟩ := finish_at_exec p h
    exact ⟨.nil, rfl, check⟩
  | cons command rest ih =>
    change AtExec (.call command.request (fun reply =>
      (if command.expected.accepts reply then runCommands Script.effect rest
        else .pure (some (commandFailure command reply))).bind (finishSetup Script.effect p))) trace target at h
    cases h with
    | ready request next exec => exact False.elim (noExec command (by simp) exec)
    | returned request next reply remaining =>
      cases accepted : command.expected.accepts reply with
      | false =>
        simp only [accepted, Bool.false_eq_true, ↓reduceIte, Script.bind] at remaining
        exact False.elim (only_excludes_exec (terminate_no_exec p (commandFailure command reply)) remaining)
      | true =>
        simp only [accepted, ↓reduceIte] at remaining
        obtain ⟨history, target, check⟩ := ih (fun c member => noExec c (by simp [member])) remaining
        exact ⟨.cons command reply accepted history, target, check⟩

-- §FS-entry.control: Reaching the actual exec request requires every concrete setup check.
theorem admission_at_exec (p : Inputs) {trace : List (Request × Reply)} {target : Request}
    (execution : AtExec (admission p) trace target) :
    inputsValid p = true ∧ Accepted (setup p) trace ∧
      target = execRequest p ∧ p.preflight = false := by
  unfold admission execute at execution
  cases valid : inputsValid p with
  | false =>
    simp only [valid, Bool.not_false, ↓reduceIte] at execution
    exact False.elim (only_excludes_exec (terminate_no_exec p ⟨p.failure, 1, 22⟩) execution)
  | true =>
    simp only [valid, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind] at execution
    exact ⟨rfl, commands_at_exec p (setup p) (setup_no_exec p) execution⟩

-- §FS-entry.control: The first failed return selects the terminal handler in executing code.
theorem failed_command_terminal (p : Inputs) (command : Command) (rest : List Command)
    (reply : Reply) (failed : command.expected.accepts reply = false) :
    ((runCommands Script.effect (command :: rest)).bind fun result =>
      match result with
      | some failure => terminate Script.effect p failure
      | none => .pure 0) =
    .call command.request (fun response =>
      if command.expected.accepts response then
        (runCommands Script.effect rest).bind (fun result =>
          match result with
          | some failure => terminate Script.effect p failure
          | none => .pure 0)
      else terminate Script.effect p (commandFailure command response)) ∧
    (if command.expected.accepts reply then runCommands Script.effect rest
      else pure (some (commandFailure command reply))) =
      (Script.pure (some (commandFailure command reply))) := by
  constructor
  · simp only [runCommands, bind, Script.effect, Script.bind, pure]
    congr 1
    funext response
    split <;> rfl
  · simp [failed, pure]

theorem accepted_command_reply {commands : List Command} {trace : List (Request × Reply)}
    (accepted : Accepted commands trace) (command : Command) (member : command ∈ commands) :
    ∃ reply, (command.request, reply) ∈ trace ∧ command.expected.accepts reply = true := by
  induction accepted with
  | nil => contradiction
  | cons first reply good remaining ih =>
    rcases List.mem_cons.mp member with same | rest
    · subst command
      exact ⟨reply, by simp, good⟩
    · obtain ⟨response, present, accepted⟩ := ih rest
      exact ⟨response, List.mem_cons_of_mem _ present, accepted⟩

-- §FS-entry.release: Actual exec requires a successful read of the supervisor's exact byte.
theorem admission_requires_release (p : Inputs)
    {trace : List (Request × Reply)} {request : Request}
    (control : AtExec (admission p) trace request) :
    ∃ reply, ({ op := Op.readByte, a := p.failure.toUInt64 }, reply) ∈ trace ∧
      reply.1 = 1 ∧ reply.2 = (⟨#[165]⟩ : ByteArray) := by
  have accepted := (admission_at_exec p control).2.1
  let release := cmd p 1 { op := .readByte, a := p.failure.toUInt64 } (.byte 165) true
  have member : release ∈ setup p := by
    simp only [setup, List.mem_append, handshake, List.mem_cons, List.not_mem_nil, or_false]
    simp only [release, or_true, true_or]
  obtain ⟨reply, present, read⟩ := accepted_command_reply accepted release member
  refine ⟨reply, present, ?_⟩
  have checked : reply.1 = 1 ∧ (reply.2 == (⟨#[165]⟩ : ByteArray)) = true := by
    simpa [release, cmd, Expected.accepts] using read
  refine ⟨checked.1, ?_⟩
  apply ByteArray.ext
  have bytes : (reply.2.data == #[165]) = true := checked.2
  simpa only [beq_iff_eq] using bytes

end LeanCage.Entry
