import Effects

namespace LeanCage.Entry

-- §AR-entry.acceptance: These are control witnesses; VM evidence checks real primitive behavior.
def Expected.witness : Expected → Reply
  | .exact value => (value, .empty)
  | .processId => (42, .empty)
  | .fileMode => (0, .empty)
  | .bytes output => (0, output)
  | .byte value => (1, ⟨#[value]⟩)

theorem expected_witness (expected : Expected) : expected.accepts expected.witness = true := by
  cases expected with
  | exact value => simp [Expected.accepts, Expected.witness]
  | processId => decide
  | fileMode => decide
  | bytes output =>
    change (output.data == output.data) = true
    simp
  | byte value =>
    change ((⟨#[value]⟩ : ByteArray).data == (⟨#[value]⟩ : ByteArray).data) = true
    simp

def acceptedTrace (commands : List Command) : List (Request × Reply) :=
  commands.map (fun command => (command.request, command.expected.witness))

theorem accepted_trace (commands : List Command) : Accepted commands (acceptedTrace commands) := by
  induction commands with
  | nil => exact .nil
  | cons command rest ih => exact .cons command _ (expected_witness command.expected) ih

theorem commands_exec_witness (p : Inputs) (run : p.preflight = false) (commands : List Command) :
    AtExec ((runCommands Script.effect commands).bind (finishSetup Script.effect p))
      (acceptedTrace commands) (execRequest p) := by
  induction commands with
  | nil =>
    change AtExec (finishSetup Script.effect p none) [] (execRequest p)
    simp only [finishSetup, run, Bool.false_eq_true, ↓reduceIte, bind, Script.bind, Script.effect]
    exact .ready _ _ rfl
  | cons command rest ih =>
    change AtExec (.call command.request (fun reply =>
      (if command.expected.accepts reply then runCommands Script.effect rest
        else .pure (some (commandFailure command reply))).bind (finishSetup Script.effect p)))
      ((command.request, command.expected.witness) :: acceptedTrace rest) (execRequest p)
    apply AtExec.returned
    simpa only [expected_witness, ↓reduceIte] using ih

def exampleInputs : Inputs :=
  ⟨100000, "/m3-runs/100000/root", 4, 5, 6, 60, #["/bin/sh", "-c", "printf entry-proof"], false, "normal"⟩

theorem example_inputs_valid : inputsValid exampleInputs = true := by
  simp only [inputsValid, handlesValid, exampleInputs, LeanCageM3.argvValid,
    ← Array.all_toList, ← Array.foldl_toList, String.contains_char_eq]
  decide

-- §FS-entry.control: The checked control admits a useful workload, as exercised separately in VM.
theorem useful_entry_witness :
    AtExec (admission exampleInputs) (acceptedTrace (setup exampleInputs)) (execRequest exampleInputs) := by
  unfold admission execute
  simp only [example_inputs_valid, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind]
  exact commands_exec_witness exampleInputs rfl (setup exampleInputs)

-- §AR-entry.acceptance: An inhabited effect-contract model, separately from physical VM evidence.
inductive WitnessReturns (fs : Filesystem) : ReturnOrigin → State → Request → Reply → State → Prop
  | kernel (before : State) (request : Request) (reply : Reply)
      (query : request.op = .prctl → request.a = 21 → reply.1 = 0 → before.filters = []) :
      WitnessReturns fs .kernel before request reply
        (if successfulReturn request reply then update fs request before else before)
  | intercepted (before : State) (request : Request) (reply : Reply) :
      WitnessReturns fs .intercepted before request reply before

theorem canonical_advance (fs : Filesystem) (request : Request) (before : State) :
    advance fs request before (update fs request before) = update fs request before := by
  cases request with
  | mk op a b c text args data => cases op <;> rfl

def witnessPlatform (fs : Filesystem) : PrimitiveContract fs where
  returns := WitnessReturns fs
  successful := by
    intro before request reply after effect _ success
    cases effect with
    | kernel _ _ _ _ =>
      simp only [success, ↓reduceIte]
      exact (canonical_advance fs request before).symm
  seccompQuery := by
    intro before request reply after effect operation code zero
    cases effect with
    | kernel _ _ _ query => exact query operation code zero

def withoutFilter (command : Command) : Bool := command.request.op != .filter

theorem without_filter_step (command : Command) (filters : List ByteArray)
    (absent : withoutFilter command = true) : filterStep command.request filters = filters := by
  cases command with
  | mk request expected stage failure =>
    cases request with
    | mk op a b c text args data =>
      cases op <;> try rfl
      change false = true at absent
      contradiction

theorem without_filter_state (fs : Filesystem) (commands : List Command)
    (absent : commands.all withoutFilter = true) (initial : State) :
    (after fs commands initial).filters = initial.filters := by
  induction commands generalizing initial with
  | nil => rfl
  | cons command rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at absent
    change (after fs rest (update fs command.request initial)).filters = _
    rw [ih absent.2, update_filters, without_filter_step command _ absent.1]

theorem without_filter_witness (fs : Filesystem) (commands : List Command)
    (guards : ∀ command ∈ commands, GuardSound command)
    (absent : commands.all withoutFilter = true) (initial : State) (clean : initial.filters = []) :
    KernelTrace (witnessPlatform fs) initial (acceptedTrace commands) (after fs commands initial) := by
  induction commands generalizing initial with
  | nil => exact .nil initial
  | cons command rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at absent
    have sound := guards command (by simp)
    have success := sound.2 command.expected.witness (expected_witness command.expected)
    change KernelTrace (witnessPlatform fs) initial
      ((command.request, command.expected.witness) :: acceptedTrace rest)
      (after fs rest (update fs command.request initial))
    refine KernelTrace.cons (middle := update fs command.request initial)
      command.request command.expected.witness ?_ ?_
    · change WitnessReturns fs .kernel initial command.request command.expected.witness _
      simpa only [success, ↓reduceIte] using
        WitnessReturns.kernel (fs := fs) initial command.request command.expected.witness (fun _ _ _ => clean)
    · apply ih (fun c member => guards c (by simp [member])) absent.2
      rw [update_filters, without_filter_step command _ absent.1, clean]

theorem kernel_trace_append {fs : Filesystem} {platform : PrimitiveContract fs}
    {initial middle final : State} {left right : List (Request × Reply)}
    (first : KernelTrace platform initial left middle) (second : KernelTrace platform middle right final) :
    KernelTrace platform initial (left ++ right) final := by
  induction first with
  | nil => exact second
  | cons request reply effect _ ih => exact .cons request reply effect (ih second)

def beforeInstall (p : Inputs) : List Command := beforeFilter p ++ (filterSetup p).take 2

set_option maxRecDepth 10000 in
theorem before_install_without_filter (p : Inputs) (normal : p.fault = "normal") :
    (beforeInstall p).all withoutFilter = true := by
  have normalized : beforeInstall p = beforeInstall {p with fault := "normal"} := by
    simp [beforeInstall, beforeFilter, signalSetup, handshake, handleSetup, rootSetup,
      credentialSetup, filterSetup, cmd, normal]
  rw [normalized]
  rfl

theorem setup_install_cut (p : Inputs) :
    setup p = beforeInstall p ++ (filterSetup p).drop 2 := by
  rw [setup_filter_cut, beforeInstall, List.append_assoc, List.take_append_drop]

theorem setup_effect_witness (fs : Filesystem) (p : Inputs) (normal : p.fault = "normal")
    (initial : State) (clean : initial.filters = []) :
    KernelTrace (witnessPlatform fs) initial (acceptedTrace (setup p)) (after fs (setup p) initial) := by
  have leading := without_filter_witness fs (beforeInstall p)
    (fun command member => setup_guards_sound p normal command (by
      rw [setup_install_cut]; exact List.mem_append_left _ member))
    (before_install_without_filter p normal) initial clean
  have tail : KernelTrace (witnessPlatform fs) (after fs (beforeInstall p) initial)
      (acceptedTrace ((filterSetup p).drop 2))
      (after fs ((filterSetup p).drop 2) (after fs (beforeInstall p) initial)) := by
    change KernelTrace (witnessPlatform fs) _ [(_, (0, ByteArray.empty))] _
    apply KernelTrace.cons
    · change WitnessReturns fs .kernel _ _ (0, ByteArray.empty) _
      simpa only [successfulReturn, ↓reduceIte] using
        WitnessReturns.kernel (fs := fs) (after fs (beforeInstall p) initial)
          (cmd p 7 {op := .filter, data := if p.fault == "filter_fail" then .empty else LeanCageM3.Filter.bytes}).request
          (0, ByteArray.empty) (by intro impossible; contradiction)
    · exact .nil _
  rw [setup_install_cut, after_append]
  simpa only [acceptedTrace, List.map_append] using kernel_trace_append leading tail

def exampleFilesystem : Filesystem := ⟨fun _ _ _ => 10, fun _ _ _ => 20⟩

def exampleInitial : State where
  handles := fun fd => if fd = 4 then some ⟨100, true, false, false⟩
    else if fd = 5 then some ⟨101, false, true, false⟩
    else if fd = 6 then some ⟨102, false, true, false⟩
    else if fd = 60 then some ⟨103, true, true, true⟩
    else some ⟨999, true, true, false⟩
  uid := IDs.leased 0
  gid := IDs.leased 0
  groups := [0]
  effectiveCaps := 2199023255551
  permittedCaps := 2199023255551
  inheritableCaps := 0
  boundingCaps := 2199023255551
  ambientCaps := 0
  securebits := 0
  dumpable := 1
  noNewPrivs := false
  filters := []
  defaults := 0
  signalMask := 0
  root := 1
  cwd := 1
  umask := 18

-- §AR-entry.acceptance: A non-restricted initial state inhabits the full body effect premises.
theorem inhabited_body_contract :
    exampleInitial.uid.real = 0 ∧ exampleInitial.groups ≠ [] ∧ exampleInitial.noNewPrivs = false ∧
    KernelTrace (witnessPlatform exampleFilesystem) exampleInitial
      (acceptedTrace (setup exampleInputs)) (after exampleFilesystem (setup exampleInputs) exampleInitial) ∧
    Restricted exampleFilesystem exampleInputs exampleInitial
      (after exampleFilesystem (setup exampleInputs) exampleInitial) := by
  have effects := setup_effect_witness exampleFilesystem exampleInputs rfl exampleInitial rfl
  exact ⟨rfl, by decide, rfl, effects,
    (admission_value_state (witnessPlatform exampleFilesystem) exampleInputs rfl exampleInitial _
      (by decide) useful_entry_witness effects).1⟩

end LeanCage.Entry
