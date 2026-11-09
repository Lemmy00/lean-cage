import Witnesses
import StartupProofs
import CallerState

namespace LeanCage.Entry

-- §FS-entry.release: A kernel read authorizes setup only for this count and byte value.
def ReleaseAccepted (count byte : Nat) : Prop := count = 1 ∧ byte = 165

theorem admission_release_values (p : Inputs) {trace : List (Request × Reply)} {request : Request}
    (control : AtExec (admission p) trace request) :
    ∃ reply, ({ op := Op.readByte, a := p.failure.toUInt64 }, reply) ∈ trace ∧
      ReleaseAccepted reply.1.toNat (reply.2.data[0]!).toNat ∧ reply.2.size = 1 := by
  obtain ⟨reply, member, count, bytes⟩ := admission_requires_release p control
  refine ⟨reply, member, ?_⟩
  rw [count, bytes]
  constructor
  · simp [ReleaseAccepted]
  · rfl

-- §FS-entry.provenance: A Linux origin law describes one operation.
structure OriginContract {fs : Filesystem} (platform : PrimitiveContract fs) where
  returns : TracerControl → ReturnOrigin → State → Request → Reply → State → Prop
  erases : ∀ control origin before request reply after,
    returns control origin before request reply after → control.nonSubstituting →
    platform.returns origin before request reply after
  unmediated : ∀ control origin before request reply after,
    returns control origin before request reply after → control.nonSubstituting →
    before.filters = [] → origin = .kernel

-- §FS-entry.provenance: The execution relation retains foreign tracers and fabricated returns.
inductive TracedReturns {fs : Filesystem} {platform : PrimitiveContract fs}
    (runtime : OriginContract platform) :
    State → List (Request × Reply) → List TracerControl → State → Prop
  | nil (state : State) : TracedReturns runtime state [] [] state
  | cons (control : TracerControl) (origin : ReturnOrigin) (request : Request) (reply : Reply)
      {before middle after : State} {trace : List (Request × Reply)}
      {controls : List TracerControl}
      (effect : runtime.returns control origin before request reply middle)
      (rest : TracedReturns runtime middle trace controls after) :
      TracedReturns runtime before ((request, reply) :: trace) (control :: controls) after

theorem traced_returns_erased {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {initial final : State}
    {trace : List (Request × Reply)} {controls : List TracerControl}
    (execution : TracedReturns runtime initial trace controls final) :
    (∀ control ∈ controls, control.nonSubstituting) →
    ReturnedTrace platform initial trace final := by
  induction execution with
  | nil state => intro safe; exact .nil state
  | cons control origin request reply effect _ ih =>
    intro safe
    exact .cons origin request reply (runtime.erases _ _ _ _ _ _ effect (safe control (by simp)))
      (ih (by intro selected member; exact safe selected (by simp [member])))

def FilterAtEnd : List Command → Prop
  | [] => True
  | command :: rest => (rest = [] ∨ command.request.op ≠ .filter) ∧ FilterAtEnd rest

theorem filter_at_end_append (left right : List Command)
    (leading : ∀ command ∈ left, command.request.op ≠ .filter)
    (trailing : FilterAtEnd right) : FilterAtEnd (left ++ right) := by
  induction left with
  | nil => exact trailing
  | cons command rest ih =>
    exact ⟨Or.inr (leading command (by simp)), ih (by
      intro current member
      exact leading current (by simp [member]))⟩

theorem advance_filters_nonfilter (fs : Filesystem) (request : Request)
    (before observed : State) (notFilter : request.op ≠ .filter) :
    (advance fs request before observed).filters = before.filters := by
  cases tag : request.op <;> simp_all [advance, collateral, update]
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

-- §FS-entry.provenance: Clean lineage and tracer control establish genuine setup returns.
theorem accepted_kernel_from_clean {fs : Filesystem} (platform : PrimitiveContract fs)
    (runtime : OriginContract platform) (commands : List Command)
    {trace : List (Request × Reply)} {controls : List TracerControl} {initial final : State}
    (accepted : Accepted commands trace)
    (guards : ∀ command ∈ commands, GuardSound command)
    (order : FilterAtEnd commands) (clean : initial.filters = [])
    (tracer : ∀ control ∈ controls, control.nonSubstituting)
    (execution : TracedReturns runtime initial trace controls final) :
    KernelTrace platform initial trace final := by
  induction commands generalizing trace controls initial with
  | nil => cases accepted; cases execution; exact .nil _
  | cons command commands ih =>
    cases accepted with
    | cons _ reply good remaining =>
      cases execution with
      | cons control origin _ _ effect rest =>
        have genuine := runtime.unmediated _ _ _ _ _ _ effect (tracer control (by simp)) clean
        subst origin
        have returned := runtime.erases _ _ _ _ _ _ effect (tracer control (by simp))
        apply KernelTrace.cons command.request reply returned
        cases commands with
        | nil => cases remaining; cases rest; exact .nil _
        | cons next commands =>
          have noFilter : command.request.op ≠ .filter := by
            rcases order.1 with impossible | safe
            · cases impossible
            · exact safe
          have sound := guards command (by simp)
          have changed := platform.successful _ _ _ _ returned sound.1 (sound.2 reply good)
          have nextClean := congrArg State.filters changed
          rw [advance_filters_nonfilter fs command.request initial _ noFilter, clean] at nextClean
          exact ih remaining (by
            intro current member
            exact guards current (by simp [member])) order.2 nextClean (by
              intro current member
              exact tracer current (by simp [member])) rest

theorem setup_filter_at_end (p : Inputs) (normal : p.fault = "normal") :
    FilterAtEnd (setup p) := by
  rw [setup_install_cut]
  apply filter_at_end_append
  · intro command member
    have absent := (List.all_eq_true.mp (before_install_without_filter p normal)) command member
    intro same
    unfold withoutFilter at absent
    rw [same] at absent
    contradiction
  · simp [filterSetup, FilterAtEnd]

-- §FS-entry.provenance: The running production startup supplies command acceptance itself.
theorem production_kernel_from_clean {fs : Filesystem} (platform : PrimitiveContract fs)
    (runtime : OriginContract platform) (args : List String) (initial current : State)
    {trace : List (Request × Reply)} {request : Request} {controls : List TracerControl}
    (control : Startup.AtExec (Worker.startup false args) trace request)
    (clean : initial.filters = [])
    (tracer : ∀ context ∈ controls, context.nonSubstituting)
    (effects : TracedReturns runtime initial trace controls current) :
    KernelTrace platform initial trace current := by
  obtain ⟨p, _, enabled, admission⟩ := startup_at_exec false args control
  have normal := Worker.production_mode p enabled
  have accepted := (admission_at_exec p admission).2.1
  exact accepted_kernel_from_clean platform runtime (setup p) accepted
    (setup_guards_sound p normal) (setup_filter_at_end p normal) clean tracer effects

theorem production_origin_values {fs : Filesystem} (platform : PrimitiveContract fs)
    (runtime : OriginContract platform) (args : List String) (initial current : State)
    (kernelWidth : initial.boundingCaps &&& 18446741874686296064 = 0)
    {trace : List (Request × Reply)} {request : Request} {controls : List TracerControl}
    (control : Startup.AtExec (Worker.startup false args) trace request)
    (clean : initial.filters = [])
    (tracer : ∀ context ∈ controls, context.nonSubstituting)
    (effects : TracedReturns runtime initial trace controls current) :
    ∃ p, ParsedHandoff args p ∧ p.fault = "normal" ∧ Restricted fs p initial current ∧
      request.op = .exec ∧ request.text = p.argv[0]! ∧ request.args = p.argv ∧
      request.data = environmentBytes := by
  exact production_startup_values platform args initial current kernelWidth control
    (production_kernel_from_clean platform runtime args initial current control clean tracer effects)

theorem production_origin_image {fs : Filesystem} (platform : PrimitiveContract fs)
    (runtime : OriginContract platform) (execution : ExecContract) (execControl : TracerControl)
    (args : List String) (initial current : State) (image : Image)
    (kernelWidth : initial.boundingCaps &&& 18446741874686296064 = 0)
    {trace : List (Request × Reply)} {request : Request} {controls : List TracerControl}
    (control : Startup.AtExec (Worker.startup false args) trace request)
    (clean : initial.filters = [])
    (tracer : ∀ context ∈ controls, context.nonSubstituting)
    (effects : TracedReturns runtime initial trace controls current)
    (safeExec : execControl.nonSubstituting)
    (replaced : execution.replaced execControl current request image) :
    ∃ p, ParsedHandoff args p ∧ p.fault = "normal" ∧ ImageRestricted fs p initial image := by
  exact production_startup_image platform execution execControl args initial current image kernelWidth control
    (production_kernel_from_clean platform runtime args initial current control clean tracer effects) safeExec replaced

end LeanCage.Entry
