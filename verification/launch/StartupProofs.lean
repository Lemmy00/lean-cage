import Execution

namespace LeanCage.Entry

-- §FS-entry.runtime: The actual startup interpreter can stop at any read/call or be lost.
-- Reads have arbitrary bytes/errors; native returns retain the script's complete trace.
inductive Startup.AtExec {α : Type} : Startup α → List (Request × Reply) → Request → Prop
  | ready (request : Request) (next : Reply → Startup α) (exec : request.op = .exec) :
      AtExec (.call request next) [] request
  | returned (request : Request) (next : Reply → Startup α) (reply : Reply)
      {trace : List (Request × Reply)} {target : Request}
      (rest : AtExec (next reply) trace target) :
      AtExec (.call request next) ((request, reply) :: trace) target
  | inspected (path : String) (limit : Nat) (next : Except IO.Error ByteArray → Startup α)
      (reply : Except IO.Error ByteArray) {trace : List (Request × Reply)} {target : Request}
      (rest : AtExec (next reply) trace target) :
      AtExec (.inspect path limit next) trace target

theorem startup_admission_at_exec {α : Type} (program : Script α)
    {trace : List (Request × Reply)} {request : Request}
    (control : Startup.AtExec (Startup.admission program) trace request) :
    AtExec program trace request := by
  induction program generalizing trace with
  | pure value => cases control
  | call current next ih =>
    cases control with
    | ready _ _ exec => exact .ready _ _ exec
    | returned _ _ reply rest => exact .returned current next reply (ih reply rest)

-- §AR-entry.caller: Any actual startup path reaching exec has parsed the original private argv.
theorem startup_at_exec (allowTestModes : Bool) (args : List String)
    {trace : List (Request × Reply)} {request : Request}
    (control : Startup.AtExec (Worker.startup allowTestModes args) trace request) :
    ∃ p, Worker.parse args = some p ∧ Worker.enabled allowTestModes p = true ∧
      AtExec (admission p) trace request := by
  simp only [Worker.startup, Startup.read, bind, Startup.bind, pure] at control
  cases control with
  | inspected _ _ _ marker rest =>
    cases marker with
    | error error => cases rest
    | ok marker =>
      by_cases rejected : (marker != "LeanCage-M3-root-VM-v1".toUTF8) = true
      · simp only [rejected, ↓reduceIte] at rest
        cases rest
      · simp only [rejected] at rest
        cases rest with
        | inspected _ _ _ status rest =>
          cases status with
          | error error => cases rest
          | ok status =>
            cases decoded : String.fromUTF8? status with
            | none => simp only [decoded] at rest; cases rest
            | some status =>
              simp only [decoded] at rest
              by_cases rejected : (!(status.splitOn "\n").contains "Threads:\t1") = true
              · simp only [rejected, ↓reduceIte] at rest
                cases rest
              · simp only [rejected] at rest
                cases accepted : Worker.parse args with
                | none => simp only [accepted] at rest; cases rest
                | some p =>
                  simp only [accepted] at rest
                  by_cases enabled : Worker.enabled allowTestModes p = true
                  · simp [enabled] at rest
                    exact ⟨p, rfl, enabled, startup_admission_at_exec _ rest⟩
                  · simp [enabled] at rest
                    cases rest

-- §FS-entry.control: This starts at the real worker control, including malformed argv and reads.
theorem production_startup_values {fs : Filesystem} (platform : PrimitiveContract fs)
    (args : List String) (initial current : State)
    (kernelWidth : initial.boundingCaps &&& 18446741874686296064 = 0)
    {trace : List (Request × Reply)} {request : Request}
    (control : Startup.AtExec (Worker.startup false args) trace request)
    (effects : KernelTrace platform initial trace current) :
    ∃ p, ParsedHandoff args p ∧ p.fault = "normal" ∧ Restricted fs p initial current ∧
      request.op = .exec ∧ request.text = p.argv[0]! ∧ request.args = p.argv ∧
      request.data = environmentBytes := by
  obtain ⟨p, accepted, production, control⟩ := startup_at_exec false args control
  exact ⟨p, worker_parse_exact args p accepted, Worker.production_mode p production,
    admission_value_state platform p (Worker.production_mode p production)
      initial current kernelWidth control effects⟩

theorem production_startup_image {fs : Filesystem} (platform : PrimitiveContract fs)
    (execution : ExecContract) (execControl : TracerControl) (args : List String) (initial current : State) (image : Image)
    (kernelWidth : initial.boundingCaps &&& 18446741874686296064 = 0)
    {trace : List (Request × Reply)} {request : Request}
    (control : Startup.AtExec (Worker.startup false args) trace request)
    (effects : KernelTrace platform initial trace current)
    (safeExec : execControl.nonSubstituting)
    (replaced : execution.replaced execControl current request image) :
    ∃ p, ParsedHandoff args p ∧ p.fault = "normal" ∧ ImageRestricted fs p initial image := by
  obtain ⟨p, accepted, production, control⟩ := startup_at_exec false args control
  exact ⟨p, worker_parse_exact args p accepted, Worker.production_mode p production,
    admission_image_state platform execution execControl p (Worker.production_mode p production)
      initial current image kernelWidth control effects safeExec replaced⟩

-- §FS-entry.inputs: No metadata reply can turn malformed private argv into an exec request.
theorem rejected_startup_no_exec (allowTestModes : Bool) (args : List String)
    (rejected : Worker.parse args = none)
    {trace : List (Request × Reply)} {request : Request} :
    ¬Startup.AtExec (Worker.startup allowTestModes args) trace request := by
  intro control
  obtain ⟨p, accepted, _, _⟩ := startup_at_exec allowTestModes args control
  rw [rejected] at accepted
  contradiction

-- §FS-entry.check: The caller's actual check word selects a path that cannot execute a workload.
theorem check_startup_no_exec (allowTestModes : Bool) (args : List String)
    {trace : List (Request × Reply)} {request : Request} :
    ¬Startup.AtExec (Worker.startup allowTestModes ("check" :: args)) trace request := by
  intro control
  obtain ⟨p, accepted, _, control⟩ := startup_at_exec allowTestModes _ control
  obtain ⟨mode, _, _, _, _, _, _, original, _, preflight, _⟩ :=
    worker_parse_exact _ p accepted
  have selected : "check" = mode := (List.cons.inj original).1
  have check : p.preflight = true := by simpa [← selected] using preflight
  exact preflight_no_image check control

end LeanCage.Entry
