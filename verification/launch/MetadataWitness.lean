import MetadataOrigins
import EntryGuarantee

set_option autoImplicit false

namespace LeanCage.Entry

namespace MetadataWitness

open LeanCageM3.Metadata

def handle : Handle := ⟨3000, true, false, true⟩

-- §AR-entry.acceptance: This model retains both useful metadata reads and returned open errors.
inductive Effect : State → LeanCageM3.Metadata.Request → LeanCageM3.Metadata.Reply → State → Prop
  | opened (before : State) (path : String) (fresh : before.handles 1 = none) :
      Effect before ⟨.open, 0, 0, path⟩ (1, .empty) (MetadataFrame.opened before 1 handle)
  | failed (before : State) (path : String) : Effect before ⟨.open, 0, 0, path⟩ (0 - 5, .empty) before
  | read (before : State) (fd : UInt32) (amount : UInt64) (reply : LeanCageM3.Metadata.Reply) :
      Effect before ⟨.read, fd, amount, ""⟩ reply before
  | closed (before : State) (fd : UInt32) (reply : LeanCageM3.Metadata.Reply) :
      Effect before ⟨.close, fd, 0, ""⟩ reply (MetadataFrame.closed before fd)

def platform : MetadataFrame.PrimitiveContract where
  returned := Effect
  open_return := by
    intro before path reply after effect
    cases effect with
    | opened _ fresh => exact ⟨handle, fresh, rfl, rfl, rfl, rfl⟩
    | failed => rfl
  read_return := by intro before fd amount reply after effect; cases effect; rfl
  close_return := by intro before fd reply after effect fits; cases effect; rfl

def inputs : Inputs := { exampleInputs with argv := #["/bin/sh"] }

theorem inputs_valid : inputsValid inputs = true := by
  simp only [inputsValid, handlesValid, inputs, exampleInputs, LeanCageM3.argvValid,
    ← Array.all_toList, ← Array.foldl_toList, String.contains_char_eq]
  decide

-- §AR-entry.acceptance: The useful session result belongs to the same source-created PID two.
def reply : Expected → Reply
  | .processId => (2, .empty)
  | expected => expected.witness

theorem reply_accepted (expected : Expected) : expected.accepts (reply expected) = true := by
  cases expected with
  | processId => decide
  | exact value => simpa only [reply] using expected_witness (.exact value)
  | fileMode => decide
  | bytes value => simpa only [reply] using expected_witness (.bytes value)
  | byte value => simpa only [reply] using expected_witness (.byte value)

def trace (commands : List Command) : List (Request × Reply) :=
  commands.map (fun command => (command.request, reply command.expected))

theorem commands_control (p : Inputs) (run : p.preflight = false) (commands : List Command) :
    AtExec ((runCommands Script.effect commands).bind (finishSetup Script.effect p))
      (trace commands) (execRequest p) := by
  induction commands with
  | nil =>
    change AtExec (finishSetup Script.effect p none) [] (execRequest p)
    simp only [finishSetup, run, Bool.false_eq_true, ↓reduceIte, bind, Script.bind, Script.effect]
    exact .ready _ _ rfl
  | cons command rest ih =>
    change AtExec (.call command.request (fun answer =>
      (if command.expected.accepts answer then runCommands Script.effect rest
        else .pure (some (commandFailure command answer))).bind (finishSetup Script.effect p)))
      ((command.request, reply command.expected) :: trace rest) (execRequest p)
    apply AtExec.returned
    simpa only [reply_accepted, ↓reduceIte] using ih

theorem effects_without_filter (fs : Filesystem) (commands : List Command)
    (guards : ∀ command ∈ commands, GuardSound command)
    (absent : commands.all withoutFilter = true) (initial : State) (clean : initial.filters = []) :
    KernelTrace (witnessPlatform fs) initial (trace commands) (after fs commands initial) := by
  induction commands generalizing initial with
  | nil => exact .nil initial
  | cons command rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at absent
    have success := (guards command (by simp)).2 (reply command.expected) (reply_accepted command.expected)
    change KernelTrace (witnessPlatform fs) initial
      ((command.request, reply command.expected) :: trace rest)
      (after fs rest (update fs command.request initial))
    refine KernelTrace.cons (middle := update fs command.request initial)
      command.request (reply command.expected) ?_ ?_
    · change WitnessReturns fs .kernel initial command.request (reply command.expected) _
      simpa only [success, ↓reduceIte] using
        WitnessReturns.kernel (fs := fs) initial command.request (reply command.expected) (fun _ _ _ => clean)
    · apply ih (fun c member => guards c (by simp [member])) absent.2
      rw [update_filters, without_filter_step command _ absent.1, clean]

theorem setup_effects (fs : Filesystem) (p : Inputs) (normal : p.fault = "normal")
    (initial : State) (clean : initial.filters = []) :
    KernelTrace (witnessPlatform fs) initial (trace (setup p)) (after fs (setup p) initial) := by
  have leading := effects_without_filter fs (beforeInstall p)
    (fun command member => setup_guards_sound p normal command (by
      rw [setup_install_cut]; exact List.mem_append_left _ member))
    (before_install_without_filter p normal) initial clean
  have tail : KernelTrace (witnessPlatform fs) (after fs (beforeInstall p) initial)
      (trace ((filterSetup p).drop 2))
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
  simpa only [trace, List.map_append] using kernel_trace_append leading tail

theorem useful_control :
    AtExec (admission inputs) (trace (setup inputs)) (execRequest inputs) := by
  unfold admission execute
  simp only [inputs_valid, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind]
  exact commands_control inputs rfl (setup inputs)

-- §AR-entry.caller.values: The useful handoff uses the actual namespace-compatible four slots.
def args : List String :=
  ["run", "100000", "/m3-runs/100000/root", "4", "5", "6", "60", "normal",
   "/bin/sh"]

theorem parsed : Worker.parse args = some inputs := by
  change (if inputsValid inputs then some inputs else none) = some inputs
  rw [inputs_valid]
  rfl

-- §FS-entry.runtime: The fresh worker has closed stdout; setup has not restricted its authority.
def initial : State :=
  { exampleInitial with
    defaults := 65536
    signalMask := 18446744073709289215
    handles := fun fd =>
      if fd = 0 then some ⟨999, true, false, false⟩
      else if fd = 2 then some ⟨999, false, true, false⟩
      else if fd = 4 then some ⟨300, true, false, false⟩
      else if fd = 5 then some ⟨303, false, true, false⟩
      else if fd = 6 then some ⟨306, false, true, false⟩
      else if fd = 60 then some ⟨182, true, true, false⟩
      else none }

theorem initial_fresh : initial.handles 1 = none := rfl

def marker : ByteArray := "LeanCage-M3-root-VM-v1".toUTF8
def status : ByteArray := "Threads:\t1\n".toUTF8

theorem fromUTF8_roundtrip (text : String) : String.fromUTF8? text.toUTF8 = some text := by
  simp only [String.fromUTF8?, String.toUTF8_eq_toByteArray, dite_eq_left text.isValidUTF8,
    String.fromUTF8]

private theorem split_miss (position next start : String.Pos.Raw) (parts : List String)
    (more : position.atEnd "Threads:\t1\n" = false)
    (different : (position.get "Threads:\t1\n" == '\n') = false)
    (step : position.next "Threads:\t1\n" = next) :
    String.splitOnAux "Threads:\t1\n" "\n" start position 0 parts =
      String.splitOnAux "Threads:\t1\n" "\n" start next 0 parts := by
  rw [String.splitOnAux]
  rw [more]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if (position.get "Threads:\t1\n" == '\n') = true then _ else _) = _
  rw [different]
  change String.splitOnAux "Threads:\t1\n" "\n" start (position.next "Threads:\t1\n") 0 parts = _
  rw [step]

theorem status_threads : ("Threads:\t1\n".splitOn "\n").contains "Threads:\t1" = true := by
  change (String.splitOnAux "Threads:\t1\n" "\n" 0 0 0 []).contains "Threads:\t1" = true
  rw [split_miss 0 ⟨1⟩ 0 [] rfl rfl rfl]
  rw [split_miss ⟨1⟩ ⟨2⟩ 0 [] rfl rfl rfl]
  rw [split_miss ⟨2⟩ ⟨3⟩ 0 [] rfl rfl rfl]
  rw [split_miss ⟨3⟩ ⟨4⟩ 0 [] rfl rfl rfl]
  rw [split_miss ⟨4⟩ ⟨5⟩ 0 [] rfl rfl rfl]
  rw [split_miss ⟨5⟩ ⟨6⟩ 0 [] rfl rfl rfl]
  rw [split_miss ⟨6⟩ ⟨7⟩ 0 [] rfl rfl rfl]
  rw [split_miss ⟨7⟩ ⟨8⟩ 0 [] rfl rfl rfl]
  rw [split_miss ⟨8⟩ ⟨9⟩ 0 [] rfl rfl rfl]
  rw [split_miss ⟨9⟩ ⟨10⟩ 0 [] rfl rfl rfl]
  rw [String.splitOnAux]
  change (String.splitOnAux "Threads:\t1\n" "\n" ⟨11⟩ ⟨11⟩ 0 ["Threads:\t1"]).contains "Threads:\t1" = true
  rw [String.splitOnAux]
  rfl

def contentTrace (path : String) (limit : Nat) (bytes : ByteArray) :
    List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply) :=
  [(⟨.open, 0, 0, path⟩, (1, .empty)),
   (⟨.read, 1, (readAmount limit 0).toUInt64, ""⟩, (bytes.size.toUInt64, bytes)),
   (⟨.read, 1, (readAmount limit bytes.size).toUInt64, ""⟩, (0, .empty)),
   (⟨.close, 1, 0, ""⟩, (0, .empty))]

theorem close_run (path : String) (bytes : ByteArray) :
    Runs platform.returned (finish path 1 (.ok bytes)) (MetadataFrame.opened initial 1 handle)
      [(⟨.close, 1, 0, ""⟩, (0, .empty))] (.ok bytes) initial := by
  have run : Runs platform.returned (finish path 1 (.ok bytes)) (MetadataFrame.opened initial 1 handle)
      [(⟨.close, 1, 0, ""⟩, (0, .empty))] (.ok bytes)
      (MetadataFrame.closed (MetadataFrame.opened initial 1 handle) 1) :=
    .call _ _ (0, .empty) (Effect.closed _ _ _) (.pure _ _)
  rw [MetadataFrame.close_open initial 1 handle initial_fresh] at run
  exact run

theorem marker_content_run :
    Runs platform.returned (bounded "/leancage-m3-disposable-vm" 64) initial
      (contentTrace "/leancage-m3-disposable-vm" 64 marker) (.ok marker) initial := by
  refine Runs.call _ _ (1, .empty) (Effect.opened initial _ initial_fresh) ?_
  refine Runs.call _ _ (marker.size.toUInt64, marker) (Effect.read _ _ _ _) ?_
  refine Runs.call _ _ (0, .empty) (Effect.read _ _ _ _) ?_
  exact close_run _ _

theorem marker_run : ∃ trace,
    Runs platform.returned (bounded "/leancage-m3-disposable-vm" 64) initial trace (.ok marker) initial :=
  ⟨_, marker_content_run⟩

theorem status_content_run :
    Runs platform.returned (bounded "/proc/self/status" 8192) initial
      (contentTrace "/proc/self/status" 8192 status) (.ok status) initial := by
  refine Runs.call _ _ (1, .empty) (Effect.opened initial _ initial_fresh) ?_
  refine Runs.call _ _ (status.size.toUInt64, status) (Effect.read _ _ _ _) ?_
  refine Runs.call _ _ (0, .empty) (Effect.read _ _ _ _) ?_
  exact close_run _ _

theorem status_run : ∃ trace,
    Runs platform.returned (bounded "/proc/self/status" 8192) initial trace (.ok status) initial :=
  ⟨_, status_content_run⟩

theorem admission_state_from_kernel {α : Type} {fs : Filesystem}
    {metadata : State → LeanCageM3.Metadata.Request → LeanCageM3.Metadata.Reply → State → Prop}
    {native : PrimitiveContract fs} {program : Script α} {before after : State}
    {trace : List (Request × Reply)} {request : Request}
    (control : AtExec program trace request) (effects : KernelTrace native before trace after) :
    Startup.AtExecState metadata (native.returns .kernel) (Startup.admission program)
      before trace request after := by
  induction control generalizing before with
  | ready request next exec => cases effects; exact .ready request _ _ exec
  | returned request next reply rest ih =>
    cases effects with
    | cons _ _ operation remaining => exact .returned request _ reply operation (ih remaining)

theorem useful_startup :
    Startup.AtExecState platform.returned ((witnessPlatform exampleFilesystem).returns .kernel)
      (Worker.startup false args) initial (trace (setup inputs))
      (execRequest inputs) (after exampleFilesystem (setup inputs) initial) := by
  obtain ⟨markerTrace, markerRead⟩ := marker_run
  obtain ⟨statusTrace, statusRead⟩ := status_run
  simp only [Worker.startup, Startup.read, bind, Startup.bind, pure]
  refine Startup.AtExecState.inspected _ _ _ (.ok marker) markerRead ?_
  refine Startup.AtExecState.inspected _ _ _ (.ok status) statusRead ?_
  simp only [inspection, Except.mapError, status, fromUTF8_roundtrip, status_threads,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, parsed, Worker.enabled]
  change Startup.AtExecState _ _ (Startup.admission (admission inputs)) initial
    (trace (setup inputs)) (execRequest inputs)
    (after exampleFilesystem (setup inputs) initial)
  exact admission_state_from_kernel useful_control
    (setup_effects exampleFilesystem inputs rfl initial rfl)

def execution : ExecContract where
  replaced := fun _ before request image => request.op = .exec ∧
    image = ⟨execState before 1, request.text, request.args, request.data⟩
  inheritance := by
    intro control before request image replaced safe operation prerequisites
    rcases replaced with ⟨_, rfl⟩
    exact ⟨rfl, rfl, rfl, rfl⟩

-- §AR-entry.acceptance: The same useful startup reaches an inhabited successful image model.
theorem useful_startup_image :
    ∃ current image,
      initial.uid.real = 0 ∧ initial.groups ≠ [] ∧ initial.noNewPrivs = false ∧
      Startup.AtExecState platform.returned ((witnessPlatform exampleFilesystem).returns .kernel)
        (Worker.startup false args) initial (trace (setup inputs))
        (execRequest inputs) current ∧
      execution.replaced .detached current (execRequest inputs) image ∧
      ImageRestricted exampleFilesystem inputs initial image := by
  let current := after exampleFilesystem (setup inputs) initial
  let image : Image := ⟨execState current 1, (execRequest inputs).text,
    (execRequest inputs).args, (execRequest inputs).data⟩
  have effects := setup_effects exampleFilesystem inputs rfl initial rfl
  have replaced : execution.replaced .detached current (execRequest inputs) image := ⟨rfl, rfl⟩
  refine ⟨current, image, rfl, by decide, rfl, useful_startup, replaced, ?_⟩
  exact admission_image_state (witnessPlatform exampleFilesystem) execution .detached inputs rfl
    initial current image (by decide) useful_control effects (by trivial) replaced

-- §FS-metadata.loss: A real returning error witness restores the initial state without reading.
theorem failed_open :
    Runs platform.returned (bounded "/leancage-m3-disposable-vm" 64) initial
      [(⟨.open, 0, 0, "/leancage-m3-disposable-vm"⟩, (0 - 5, .empty))]
      (.error ⟨.open, 5, "/leancage-m3-disposable-vm"⟩) initial := by
  refine .call _ _ (0 - 5, .empty) (.failed initial _) ?_
  exact .pure _ _

theorem returned_error_startup :
    Startup.ReturnsState platform.returned ((witnessPlatform exampleFilesystem).returns .kernel)
      (Worker.startup false args) initial [] 125 initial := by
  simp only [Worker.startup, Startup.read, bind, Startup.bind, pure]
  refine .inspected _ _ _ (.error ⟨.open, 5, "/leancage-m3-disposable-vm"⟩) failed_open ?_
  exact .pure _ _

-- §FS-metadata.loss: The same program has a lost prefix with its metadata slot still open.
theorem interrupted_metadata :
    ∃ pending current,
      Prefix platform.returned (bounded "/leancage-m3-disposable-vm" 64) initial
        [(⟨.open, 0, 0, "/leancage-m3-disposable-vm"⟩, (1, .empty))] pending current ∧
      current.handles 1 = some handle ∧
      Execution platform.returned (fun _ _ _ => True)
        (bounded "/leancage-m3-disposable-vm" 64) initial (.lost current) ∧
      (Outcome.lost (α := Result) current).value? = none := by
  let current := MetadataFrame.opened initial 1 handle
  let pending := (loop 65 "/leancage-m3-disposable-vm" 1 64 .empty).bind
    (finish "/leancage-m3-disposable-vm" 1)
  have stopped : Prefix platform.returned (bounded "/leancage-m3-disposable-vm" 64) initial
      [(⟨.open, 0, 0, "/leancage-m3-disposable-vm"⟩, (1, .empty))] pending current :=
    .call _ _ (1, .empty) (Effect.opened initial _ initial_fresh) (.refl _ _)
  exact ⟨pending, current, stopped, rfl, .lost stopped True.intro, rfl⟩

end MetadataWitness

namespace CallerWitness

-- §AR-entry.acceptance: This inhabited model retains intercepted and unprotected primitive returns.
inductive RuntimeReturns (fs : Filesystem) (actual : TracerControl) :
    ReturnOrigin → State → Request → Reply → State → Prop
  | kernel {before after : State} {request : Request} {reply : Reply}
      (effect : WitnessReturns fs .kernel before request reply after) :
      RuntimeReturns fs actual .kernel before request reply after
  | intercepted (before : State) (request : Request) (reply : Reply) (filtered : before.filters ≠ []) :
      RuntimeReturns fs actual .intercepted before request reply before
  | rewritten (origin : ReturnOrigin) (before after : State) (request : Request) (reply : Reply)
      (unprotected : ¬actual.nonSubstituting) : RuntimeReturns fs actual origin before request reply after

def runtime (fs : Filesystem) : OriginContract (witnessPlatform fs) where
  returns := RuntimeReturns fs
  erases := by
    intro actual origin before request reply after operation safe
    cases operation with
    | kernel effect => exact effect
    | intercepted => exact .intercepted _ _ _
    | rewritten _ _ _ _ _ unprotected => exact False.elim (unprotected safe)
  unmediated := by
    intro actual origin before request reply after operation safe clean
    cases operation with
    | kernel => rfl
    | intercepted _ _ _ filtered => exact False.elim (filtered clean)
    | rewritten _ _ _ _ _ unprotected => exact False.elim (unprotected safe)

inductive MetadataRuntimeReturns (actual : TracerControl) : ReturnOrigin → State →
    LeanCageM3.Metadata.Request → LeanCageM3.Metadata.Reply → State → Prop
  | kernel {before after : State} {request : LeanCageM3.Metadata.Request} {reply : LeanCageM3.Metadata.Reply}
      (effect : MetadataWitness.Effect before request reply after) :
      MetadataRuntimeReturns actual .kernel before request reply after
  | intercepted (before after : State) (request : LeanCageM3.Metadata.Request)
      (reply : LeanCageM3.Metadata.Reply) (filtered : before.filters ≠ []) :
      MetadataRuntimeReturns actual .intercepted before request reply after
  | rewritten (origin : ReturnOrigin) (before after : State) (request : LeanCageM3.Metadata.Request)
      (reply : LeanCageM3.Metadata.Reply) (unprotected : ¬actual.nonSubstituting) :
      MetadataRuntimeReturns actual origin before request reply after

def metadataRuntime : MetadataOriginContract MetadataWitness.platform where
  returns := MetadataRuntimeReturns
  erases := by
    intro actual origin before request reply after operation safe genuine
    cases operation with
    | kernel effect => exact effect
    | intercepted => contradiction
    | rewritten _ _ _ _ _ unprotected => exact False.elim (unprotected safe)
  unmediated := by
    intro actual origin before request reply after operation safe clean
    cases operation with
    | kernel => rfl
    | intercepted _ _ _ _ filtered => exact False.elim (filtered clean)
    | rewritten _ _ _ _ _ unprotected => exact False.elim (unprotected safe)

-- §AR-entry.acceptance: These are the complete object/flag projections of the actual worker table.
def objects (fd : Nat) : Option Nat :=
  if fd = 0 ∨ fd = 2 then some 999
  else if fd = 4 then some 300
  else if fd = 5 then some 303
  else if fd = 6 then some 306
  else if fd = 60 then some 182
  else none

def cloexec (_ : Nat) : Bool := false
def ordinaryRead (fd : Nat) : Bool := fd == 0 || fd == 4
def ordinaryWrite (fd : Nat) : Bool := fd == 2 || fd == 5 || fd == 6

theorem initial_loaded :
    PhysicalHandoff.loadedHandles objects cloexec
      (PhysicalHandoff.descriptorAccess objects ordinaryRead)
      (PhysicalHandoff.descriptorAccess objects ordinaryWrite) MetadataWitness.initial := by
  funext fd
  by_cases zero : fd = 0
  · subst fd; rfl
  by_cases two : fd = 2
  · subst fd; rfl
  by_cases four : fd = 4
  · subst fd; rfl
  by_cases five : fd = 5
  · subst fd; rfl
  by_cases six : fd = 6
  · subst fd; rfl
  by_cases sixty : fd = 60
  · subst fd; rfl
  have zero' : fd.toNat ≠ 0 := fun h => zero (UInt32.toNat.inj h)
  have two' : fd.toNat ≠ 2 := fun h => two (UInt32.toNat.inj h)
  have four' : fd.toNat ≠ 4 := fun h => four (UInt32.toNat.inj h)
  have five' : fd.toNat ≠ 5 := fun h => five (UInt32.toNat.inj h)
  have six' : fd.toNat ≠ 6 := fun h => six (UInt32.toNat.inj h)
  have sixty' : fd.toNat ≠ 60 := fun h => sixty (UInt32.toNat.inj h)
  simp [MetadataWitness.initial, objects, zero, two, four, five, six, sixty,
    zero', two', four', five', six', sixty']

theorem initial_prepared_sources : PreparedSources MetadataWitness.inputs MetadataWitness.initial := by
  refine PhysicalHandoff.loaded_prepared_sources MetadataWitness.inputs 100 101 102 60
    false false false false initial_loaded ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | exact ⟨rfl, rfl⟩ | rfl

-- §AR-entry.caller.values: These exact canonical bytes are in the actual source image's argv.
def argumentBytes : List (List UInt8) :=
  [[114,117,110], [49,48,48,48,48,48],
   [47,109,51,45,114,117,110,115,47,49,48,48,48,48,48,47,114,111,111,116],
   [52], [53], [54], [54,48], [110,111,114,109,97,108], [47,98,105,110,47,115,104]]

theorem source_arguments_match :
    MetadataWitness.args.map (fun text => text.toUTF8.data.toList) = argumentBytes := by decide

theorem source_signal_mask : MetadataWitness.initial.signalMask = 18446744073709289215 := rfl
theorem source_sigchld_default : MetadataWitness.initial.defaults &&& 65536 = 65536 := by decide

-- §AR-entry.acceptance: The same loaded worker inputs feed real metadata, body and image consumers.
theorem useful_loaded_worker_entry (control : TracerControl) :
    ∃ current image,
      PhysicalHandoff.loadedHandles objects cloexec
        (PhysicalHandoff.descriptorAccess objects ordinaryRead)
        (PhysicalHandoff.descriptorAccess objects ordinaryWrite) MetadataWitness.initial ∧
      MetadataWitness.args.map (fun text => text.toUTF8.data.toList) = argumentBytes ∧
      Startup.AtExecState MetadataWitness.platform.returned
        ((witnessPlatform exampleFilesystem).returns .kernel)
        (Worker.startup false MetadataWitness.args) MetadataWitness.initial
        (MetadataWitness.trace (setup MetadataWitness.inputs)) (execRequest MetadataWitness.inputs) current ∧
      MetadataWitness.execution.replaced control current (execRequest MetadataWitness.inputs) image ∧
      ImageRestricted exampleFilesystem MetadataWitness.inputs MetadataWitness.initial image ∧
      ImageStdio MetadataWitness.inputs MetadataWitness.initial image := by
  obtain ⟨current, image, _, _, _, run, replaced, restricted⟩ := MetadataWitness.useful_startup_image
  exact ⟨current, image, initial_loaded, source_arguments_match, run, replaced, restricted,
    image_has_supplied_stdio restricted initial_prepared_sources⟩

open CallerPhysical

def tracedContext (owner : ProcessIdentity) (before : Context) : Context :=
  { before with tracer := some owner, options := 0, issued := [] }

def HandleObjectsFrom (before after : UInt32 → Option Handle) : Prop :=
  ∀ fd handle, after fd = some handle →
    ∃ old previous, before old = some previous ∧ previous.object = handle.object

theorem duplicate_objects_from (before : UInt32 → Option Handle) (source target : UInt32) (flag : Bool) :
    HandleObjectsFrom before (duplicate before source target flag) := by
  intro fd handle present
  unfold duplicate at present
  split at present
  · cases prior : before source with
    | none => simp only [prior, Option.map_none] at present; contradiction
    | some previous =>
      simp only [prior, Option.map_some, Option.some.injEq] at present
      subst handle
      exact ⟨source, previous, prior, rfl⟩
  · exact ⟨fd, handle, present, rfl⟩

theorem handle_step_objects_from (request : Request) (before : UInt32 → Option Handle) :
    HandleObjectsFrom before (handleStep request before) := by
  cases operation : request.op <;> simp only [handleStep, operation]
  all_goals try exact (by intro fd handle present; exact ⟨fd, handle, present, rfl⟩)
  · split
    · intro fd handle present; exact ⟨fd, handle, present, rfl⟩
    · exact duplicate_objects_from _ _ _ _
  · exact duplicate_objects_from _ _ _ _
  · intro fd handle present
    dsimp only at present
    split at present
    · split at present
      · cases prior : before fd with
        | none => simp only [prior, Option.map_none] at present; contradiction
        | some previous =>
          simp only [prior, Option.map_some, Option.some.injEq] at present
          subst handle
          exact ⟨fd, previous, prior, rfl⟩
      · contradiction
    · exact ⟨fd, handle, present, rfl⟩

theorem kernel_effect_objects_from {fs : Filesystem} {before after : State} {request : Request} {reply : Reply}
    (effect : WitnessReturns fs .kernel before request reply after) : HandleObjectsFrom before.handles after.handles := by
  cases effect with
  | kernel state request reply query =>
    split
    · rw [update_handles]
      exact handle_step_objects_from _ _
    · intro fd handle present; exact ⟨fd, handle, present, rfl⟩

def HandlesBounded (handles : UInt32 → Option Handle) : Prop :=
  ∀ fd handle, handles fd = some handle → fd.toNat ≤ 2147483647

theorem duplicate_bounded {before : UInt32 → Option Handle} (bounded : HandlesBounded before)
    (source target : UInt32) (flag : Bool) (targetBound : target.toNat ≤ 2147483647) :
    HandlesBounded (duplicate before source target flag) := by
  intro fd handle present
  unfold duplicate at present
  split at present
  · rename_i same
    simpa only [same] using targetBound
  · exact bounded fd handle present

theorem handle_step_bounded (request : Request) (before : UInt32 → Option Handle) (bounded : HandlesBounded before)
    (target : request.op = .dup2 ∨ request.op = .dup3 → request.b.toUInt32.toNat ≤ 2147483647) :
    HandlesBounded (handleStep request before) := by
  cases operation : request.op <;> simp only [handleStep, operation]
  all_goals try exact bounded
  · split
    · exact bounded
    · exact duplicate_bounded bounded _ _ _ (target (Or.inl operation))
  · exact duplicate_bounded bounded _ _ _ (target (Or.inr operation))
  · intro fd handle present
    dsimp only at present
    split at present
    · split at present
      · cases prior : before fd with
        | none => simp only [prior, Option.map_none] at present; contradiction
        | some previous => exact bounded fd previous prior
      · contradiction
    · exact bounded fd handle present

theorem kernel_effect_bounded {fs : Filesystem} {before after : State} {request : Request} {reply : Reply}
    (bounded : HandlesBounded before.handles)
    (target : request.op = .dup2 ∨ request.op = .dup3 → request.b.toUInt32.toNat ≤ 2147483647)
    (effect : WitnessReturns fs .kernel before request reply after) : HandlesBounded after.handles := by
  cases effect
  split
  · rw [update_handles]
    exact handle_step_bounded _ _ bounded target
  · exact bounded

theorem kernel_trace_bounded {fs : Filesystem} {before after : State} {trace : List (Request × Reply)}
    (effects : KernelTrace (witnessPlatform fs) before trace after) (bounded : HandlesBounded before.handles)
    (targets : ∀ pair ∈ trace, pair.1.op = .dup2 ∨ pair.1.op = .dup3 → pair.1.b.toUInt32.toNat ≤ 2147483647) :
    HandlesBounded after.handles := by
  induction effects with
  | nil => exact bounded
  | cons request reply operation rest ih =>
    exact ih (kernel_effect_bounded bounded (targets (request, reply) (by simp)) operation)
      (by intro pair member; exact targets pair (by simp [member]))

theorem initial_handles_bounded : HandlesBounded MetadataWitness.initial.handles := by
  intro fd handle present
  by_cases zero : fd = 0
  · subst fd; decide
  by_cases two : fd = 2
  · subst fd; decide
  by_cases four : fd = 4
  · subst fd; decide
  by_cases five : fd = 5
  · subst fd; decide
  by_cases six : fd = 6
  · subst fd; decide
  by_cases sixty : fd = 60
  · subst fd; decide
  simp only [MetadataWitness.initial, zero, two, four, five, six, sixty, ↓reduceIte] at present
  contradiction

-- §AR-entry.effects: This pure relation connects retained descriptor objects between sampled ticks.
def DescriptorObjectsFrom (before after : Nat → Option Nat) : Prop :=
  ∀ fd object, fd ≤ 2147483647 → after fd = some object →
    ∃ old, old ≤ 2147483647 ∧ before old = some object

def stateObjects (state : State) (fd : Nat) : Option Nat :=
  if fd ≤ 2147483647 then (state.handles fd.toUInt32).map Handle.object else none

def stateFlags (state : State) (fd : Nat) : Bool :=
  if fd ≤ 2147483647 then ((state.handles fd.toUInt32).map Handle.cloexec).getD false else false

def FlagsOutside (before after : Nat → Bool) (fd : Nat) : Prop :=
  ∀ query, query ≤ 2147483647 → query ≠ fd → after query = before query

theorem metadata_open_flags (before : State) :
    FlagsOutside (stateFlags before) (stateFlags (MetadataFrame.opened before 1 MetadataWitness.handle)) 1 := by
  intro query bounded different
  have different' : query.toUInt32 ≠ 1 := by
    intro same
    have narrow : query.toUInt32.toNat = query := by
      apply UInt32.toNat_ofNat_of_lt'
      change query < 4294967296
      omega
    have equal := congrArg UInt32.toNat same
    rw [narrow] at equal
    exact different equal
  simp only [stateFlags, bounded, ↓reduceIte, MetadataFrame.opened, different']

theorem kernel_descriptor_objects_from {fs : Filesystem} {before after : State} {request : Request} {reply : Reply}
    (bounded : HandlesBounded before.handles) (effect : WitnessReturns fs .kernel before request reply after) :
    DescriptorObjectsFrom (stateObjects before) (stateObjects after) := by
  intro fd object valid present
  simp only [stateObjects, valid, ↓reduceIte] at present
  cases current : after.handles fd.toUInt32 with
  | none => simp only [current, Option.map_none] at present; contradiction
  | some handle =>
    simp only [current, Option.map_some, Option.some.injEq] at present
    obtain ⟨old, previous, prior, same⟩ := kernel_effect_objects_from effect _ _ current
    have oldBound := bounded old previous prior
    refine ⟨old.toNat, oldBound, ?_⟩
    simp only [stateObjects, oldBound, ↓reduceIte, Nat.toUInt32, UInt32.ofNat_toNat, prior, Option.map_some]
    exact congrArg some (same.trans present)

theorem runtime_descriptor_objects_from {fs : Filesystem} {actual : TracerControl}
    {before after : State} {request : Request} {reply : Reply}
    (operation : (runtime fs).returns actual .kernel before request reply after) (safe : actual.nonSubstituting)
    (bounded : HandlesBounded before.handles) : DescriptorObjectsFrom (stateObjects before) (stateObjects after) :=
  kernel_descriptor_objects_from bounded ((runtime fs).erases actual .kernel before request reply after operation safe)

-- §AR-metadata.primitives: Open adds a fresh ordinary object; other calls retain objects.
inductive DescriptorEffect (before after : Nat → Option Nat) : Prop
  | retained (frame : DescriptorObjectsFrom before after) : DescriptorEffect before after
  | opened (fd identity : Nat) (bounded : fd ≤ 2147483647) (fresh : before fd = none)
      (table : after = fun slot => if slot = fd then some (3 * identity) else before slot) :
      DescriptorEffect before after

theorem metadata_descriptor_effect {before after : State} {request : LeanCageM3.Metadata.Request}
    {reply : LeanCageM3.Metadata.Reply} (operation : MetadataWitness.Effect before request reply after) :
    DescriptorEffect (stateObjects before) (stateObjects after) := by
  cases operation with
  | opened path fresh =>
    apply DescriptorEffect.opened 1 1000 (by decide)
    · change (before.handles 1).map Handle.object = none
      rw [fresh]
      rfl
    · funext slot
      by_cases one : slot = 1
      · subst slot; rfl
      by_cases bounded : slot ≤ 2147483647
      · have different : slot.toUInt32 ≠ 1 := by
          intro same
          have narrow : slot.toUInt32.toNat = slot := by
            apply UInt32.toNat_ofNat_of_lt'
            change slot < 4294967296
            omega
          have equal := congrArg UInt32.toNat same
          rw [narrow] at equal
          exact one equal
        simp only [stateObjects, bounded, ↓reduceIte, MetadataFrame.opened, different, one]
      · simp only [stateObjects, bounded, one, ↓reduceIte]
  | failed =>
    apply DescriptorEffect.retained
    intro fd object bounded present
    exact ⟨fd, bounded, present⟩
  | read =>
    apply DescriptorEffect.retained
    intro fd object bounded present
    exact ⟨fd, bounded, present⟩
  | closed closed reply =>
    apply DescriptorEffect.retained
    intro fd object bounded present
    simp only [stateObjects, bounded, ↓reduceIte, MetadataFrame.closed] at present
    split at present
    · contradiction
    · exact ⟨fd, bounded, by simpa only [stateObjects, bounded, ↓reduceIte] using present⟩

theorem metadata_effect_bounded {before after : State} {request : LeanCageM3.Metadata.Request}
    {reply : LeanCageM3.Metadata.Reply} (bounded : HandlesBounded before.handles)
    (operation : MetadataWitness.Effect before request reply after) : HandlesBounded after.handles := by
  cases operation with
  | opened =>
    intro fd handle present
    dsimp only [MetadataFrame.opened] at present
    split at present
    · rename_i same
      subst fd
      decide
    · exact bounded fd handle present
  | failed => exact bounded
  | read => exact bounded
  | closed =>
    intro fd handle present
    dsimp only [MetadataFrame.closed] at present
    split at present
    · contradiction
    · exact bounded fd handle present

theorem metadata_runtime_descriptor_effect {actual : TracerControl} {before after : State}
    {request : LeanCageM3.Metadata.Request} {reply : LeanCageM3.Metadata.Reply}
    (operation : metadataRuntime.returns actual .kernel before request reply after) (safe : actual.nonSubstituting) :
    DescriptorEffect (stateObjects before) (stateObjects after) :=
  metadata_descriptor_effect (metadataRuntime.erases actual .kernel before request reply after operation safe rfl)

-- §AR-metadata.primitives: The same open carries its object update and outside-descriptor flags.
inductive DescriptorCapabilityEffect (before after : Nat → Option Nat) (beforeFlags afterFlags : Nat → Bool) : Prop
  | retained (frame : DescriptorObjectsFrom before after) : DescriptorCapabilityEffect before after beforeFlags afterFlags
  | opened (fd identity : Nat) (bounded : fd ≤ 2147483647) (fresh : before fd = none)
      (table : after = fun slot => if slot = fd then some (3 * identity) else before slot)
      (flags : FlagsOutside beforeFlags afterFlags fd) : DescriptorCapabilityEffect before after beforeFlags afterFlags

theorem metadata_descriptor_capability_effect {before after : State} {request : LeanCageM3.Metadata.Request}
    {reply : LeanCageM3.Metadata.Reply} (operation : MetadataWitness.Effect before request reply after) :
    DescriptorCapabilityEffect (stateObjects before) (stateObjects after) (stateFlags before) (stateFlags after) := by
  cases operation with
  | opened path fresh =>
    have effect := metadata_descriptor_effect (MetadataWitness.Effect.opened before path fresh)
    cases effect with
    | retained frame => exact .retained frame
    | opened fd identity bounded prior table =>
      have one : fd = 1 := by
        by_cases different : fd = 1
        · exact different
        · have same := congrFun table 1
          have priorOne : stateObjects before 1 = none := by
            change (before.handles 1).map Handle.object = none
            rw [fresh]; rfl
          have different' : 1 ≠ fd := Ne.symm different
          simp only [different', ↓reduceIte, priorOne] at same
          change some 3000 = none at same
          contradiction
      subst fd
      exact .opened 1 identity bounded prior table (metadata_open_flags before)
  | failed =>
    apply DescriptorCapabilityEffect.retained
    intro fd object bounded present
    exact ⟨fd, bounded, present⟩
  | read =>
    apply DescriptorCapabilityEffect.retained
    intro fd object bounded present
    exact ⟨fd, bounded, present⟩
  | closed =>
    apply DescriptorCapabilityEffect.retained
    intro fd object bounded present
    simp only [stateObjects, bounded, ↓reduceIte, MetadataFrame.closed] at present
    split at present
    · contradiction
    · exact ⟨fd, bounded, by simpa only [stateObjects, bounded, ↓reduceIte] using present⟩

-- §AR-entry.effects: These are individual native effects in an inhabited runtime model.
inductive NativeOperation {fs : Filesystem} {platform : PrimitiveContract fs}
    (originRuntime : OriginContract platform) (mayTrace : ProcessIdentity → Prop) (owner child : ProcessIdentity) :
    Nat → Context → ReturnOrigin → State → Request → Reply → Context → State → Prop
  | frame (position : Nat) (before : Context) (origin : ReturnOrigin) (state result : State)
      (request : Request) (reply : Reply) (alive : before.childAlive = true)
      (effect : originRuntime.returns (control owner child before) origin state request reply result)
      (ordinary : request.op ≠ .traceMe ∨ origin ≠ .kernel ∨ reply.1 ≠ 0 ∨ ¬ContextSafe owner before) :
      NativeOperation originRuntime mayTrace owner child position before origin state request reply before result
  | traced (position : Nat) (before : Context) (state result : State) (request : Request) (reply : Reply)
      (untraced : before.tracer = none) (parent : before.parentAlive = true) (alive : before.childAlive = true)
      (effect : originRuntime.returns (control owner child before) .kernel state request reply result)
      (operation : request.op = .traceMe) (returned : reply.1 = 0) :
      NativeOperation originRuntime mayTrace owner child position before .kernel state request reply
        (tracedContext owner before) result
  | placed (position : Nat) (before : Context) (origin : ReturnOrigin) (state result : State)
      (request : Request) (reply : Reply) (group : Nat) (alive : before.childAlive = true)
      (effect : originRuntime.returns (control owner child before) origin state request reply result)
      (permitted : request.op = .write ∨ origin = .intercepted ∨ ¬(control owner child before).nonSubstituting) :
      NativeOperation originRuntime mayTrace owner child position before origin state request reply
        { before with cgroup := some group } result
  | rewritten (position : Nat) (before after : Context) (origin : ReturnOrigin) (state result : State)
      (request : Request) (reply : Reply) (alive : before.childAlive = true)
      (effect : originRuntime.returns (control owner child before) origin state request reply result)
      (unprotected : ¬(control owner child before).nonSubstituting) :
      NativeOperation originRuntime mayTrace owner child position before origin state request reply after result

def primitiveNative {fs : Filesystem} {platform : PrimitiveContract fs}
    (originRuntime : OriginContract platform) (mayTrace : ProcessIdentity → Prop) (owner child : ProcessIdentity) :
    NativeContract originRuntime mayTrace owner child where
  returned := NativeOperation originRuntime mayTrace owner child
  live := by intro position before origin state request reply after result operation; cases operation <;> assumption
  effect := by intro position before origin state request reply after result operation; cases operation <;> assumption
  projection := by
    intro position before origin state request reply after result operation
    cases operation with
    | frame =>
      exact Or.inl ⟨by assumption, .nativeFrame before before rfl rfl rfl rfl rfl rfl rfl⟩
    | traced =>
      exact Or.inr (Or.inl ⟨by assumption, rfl, by assumption, .traceMe before (by assumption) (by assumption) (by assumption)⟩)
    | placed => exact Or.inr (Or.inr ⟨_, by assumption, .placement before _⟩)
    | rewritten =>
      have unprotected : ¬(control owner child before).nonSubstituting := by assumption
      have unprotected' : ¬ContextSafe owner before := fun safe => unprotected (context_safe_non_substituting safe)
      exact Or.inl ⟨Or.inr (Or.inr (Or.inr unprotected')), .nativeUnsafe before after unprotected'⟩
  scope := by
    intro position before origin state request reply after result operation safe genuine notWrite
    cases operation with
    | frame => exact ⟨rfl, rfl⟩
    | traced => exact ⟨rfl, rfl⟩
    | placed =>
      have permitted : request.op = .write ∨ origin = .intercepted ∨ ¬(control owner child before).nonSubstituting := by assumption
      rcases permitted with write | intercepted | unprotected
      · exact False.elim (notWrite write)
      · cases genuine.symm.trans intercepted
      · exact False.elim (unprotected safe)
    | rewritten => exact False.elim ((by assumption : ¬(control owner child before).nonSubstituting) safe)

inductive MetadataOperation {platform : MetadataFrame.PrimitiveContract}
    (originRuntime : MetadataOriginContract platform) (owner child : ProcessIdentity) :
    Nat → Context → ReturnOrigin → State → LeanCageM3.Metadata.Request →
      LeanCageM3.Metadata.Reply → Context → State → Prop
  | frame (position : Nat) (before : Context) (origin : ReturnOrigin) (state result : State)
      (request : LeanCageM3.Metadata.Request) (reply : LeanCageM3.Metadata.Reply) (alive : before.childAlive = true)
      (effect : originRuntime.returns (control owner child before) origin state request reply result) :
      MetadataOperation originRuntime owner child position before origin state request reply before result
  | rewritten (position : Nat) (before after : Context) (origin : ReturnOrigin) (state result : State)
      (request : LeanCageM3.Metadata.Request) (reply : LeanCageM3.Metadata.Reply) (alive : before.childAlive = true)
      (effect : originRuntime.returns (control owner child before) origin state request reply result)
      (unprotected : ¬(control owner child before).nonSubstituting) :
      MetadataOperation originRuntime owner child position before origin state request reply after result

def primitiveMetadata {platform : MetadataFrame.PrimitiveContract}
    (originRuntime : MetadataOriginContract platform) (mayTrace : ProcessIdentity → Prop) (owner child : ProcessIdentity) :
    MetadataContract originRuntime mayTrace owner child where
  returned := MetadataOperation originRuntime owner child
  live := by intro position before origin state request reply after result operation; cases operation <;> assumption
  projection := by
    intro position before origin state request reply after result operation safe genuine
    cases operation with
    | frame => exact .nativeFrame before before rfl rfl rfl rfl rfl rfl rfl
    | rewritten => exact False.elim ((by assumption : ¬(control owner child before).nonSubstituting) safe)

theorem fixed_primitive_label {ticks : List Tick} {start position selectedOffset : Nat} {selectedTick : Tick}
    {label : Option PrimitiveLabel} (ordinal : position = start + selectedOffset)
    (selected : TickAt ticks selectedOffset selectedTick) (actual : selectedTick.primitive = label) :
    ∀ offset tick, position = start + offset → TickAt ticks offset tick → tick.primitive = label := by
  intro offset tick current found
  have sameOffset := Nat.add_left_cancel (ordinal.symm.trans current)
  subst offset
  have sameTick := Option.some.inj ((tickAt_getElem selected).symm.trans (tickAt_getElem found))
  cases sameTick
  exact actual

-- §AR-entry.caller.origin: This runtime adapter samples one operation in the actual fixed journal.
def recordedSupervisor (mayTrace : ProcessIdentity → Prop) (owner child : ProcessIdentity)
    (start : Nat) (ticks : List Tick) : SupervisorContract mayTrace owner child where
  returned := fun position before state action after result =>
    ∃ offset tick, position = start + offset ∧ TickAt ticks offset tick ∧
      tick.before = before ∧ tick.after = after ∧ tick.action = action ∧
      Step mayTrace owner child before action after ∧ action ≠ .native ∧ action ≠ .traceMe ∧
      result = state
  projection := by
    intro position before state action after result operation
    obtain ⟨_, _, _, _, _, _, _, step, _, _, _⟩ := operation
    exact step
  separate := by
    intro position before state action after result operation
    obtain ⟨_, _, _, _, _, _, _, _, native, _, _⟩ := operation
    exact native
  noTraceMe := by
    intro position before state action after result operation
    obtain ⟨_, _, _, _, _, _, _, _, _, traceMe, _⟩ := operation
    exact traceMe
  frame := by
    intro position before state action after result operation allowed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, frame⟩ := operation
    exact frame

theorem recorded_supervisor_recording (mayTrace : ProcessIdentity → Prop) (owner child : ProcessIdentity)
    (start : Nat) (ticks : List Tick)
    (writes : ∀ offset tick, TickAt ticks offset tick → WriteSourceOrExternal owner child tick) :
    SupervisorRecording (recordedSupervisor mayTrace owner child start ticks) start ticks := by
  constructor
  · intro position before state action after result operation
    obtain ⟨offset, tick, ordinal, selected, initial, final, actual, _, _, _, _⟩ := operation
    exact ⟨offset, tick, ordinal, selected, initial, final, actual⟩
  · intro position before state action after result operation offset tick ordinal selected actor fd bytes lost wrote
    exact writes offset tick selected actor fd bytes lost wrote

-- §AR-entry.effects: A returned native call is restricted to its actual selected primitive tick.
def recordedNative {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity}
    (base : NativeContract runtime mayTrace owner child) (start : Nat) (ticks : List Tick) :
    NativeContract runtime mayTrace owner child where
  returned := fun position before origin state request reply after result =>
    base.returned position before origin state request reply after result ∧
    ∃ offset tick, position = start + offset ∧ TickAt ticks offset tick ∧
      tick.before = before ∧ tick.after = after ∧
      (tick.action = .native ∨
        (tick.action = .traceMe ∧ request.op = .traceMe ∧ origin = .kernel ∧ reply.1 = 0) ∨
        (∃ group, tick.action = .placement group ∧
          (request.op = .write ∨ origin = .intercepted ∨
            ¬(control owner child before).nonSubstituting))) ∧
      NativeTable child state tick ∧ NativeSocket (control owner child before) child origin request reply tick.socket
        ∧ tick.primitive = some ⟨.native, request.op.code.toNat, decide (origin = .kernel)⟩
  live := by intro position before origin state request reply after result operation; exact base.live _ _ _ _ _ _ _ _ operation.1
  effect := by intro position before origin state request reply after result operation; exact base.effect _ _ _ _ _ _ _ _ operation.1
  projection := by intro position before origin state request reply after result operation; exact base.projection _ _ _ _ _ _ _ _ operation.1
  scope := by intro position before origin state request reply after result operation; exact base.scope _ _ _ _ _ _ _ _ operation.1

theorem recorded_native_recording {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity}
    (base : NativeContract runtime mayTrace owner child) (start : Nat) (ticks : List Tick) :
    NativeRecording (recordedNative base start ticks) start ticks := by
  constructor
  · intro position before origin state request reply after result operation
    obtain ⟨offset, tick, ordinal, selected, initial, final, action, table, socket, label⟩ := operation.2
    exact ⟨offset, tick, ordinal, selected, initial, final, action, table, socket⟩
  · intro position before origin state request reply after result operation
    obtain ⟨offset, tick, ordinal, selected, _, _, _, _, _, label⟩ := operation.2
    exact fixed_primitive_label ordinal selected label

-- §AR-metadata.primitives: Unsafe metadata remains broad; genuine safe calls sample native ticks.
def recordedMetadata {platform : MetadataFrame.PrimitiveContract} {runtime : MetadataOriginContract platform}
    {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity}
    (base : MetadataContract runtime mayTrace owner child) (start : Nat) (ticks : List Tick) :
    MetadataContract runtime mayTrace owner child where
  returned := fun position before origin state request reply after result =>
    base.returned position before origin state request reply after result ∧
    ∃ offset tick, position = start + offset ∧ TickAt ticks offset tick ∧
      tick.before = before ∧ tick.after = after ∧
      (origin = .kernel → (control owner child before).nonSubstituting → tick.action = .native) ∧
      NativeTable child state tick ∧
      runtime.returns (control owner child before) origin state request reply result ∧
      (origin = .kernel → (control owner child before).nonSubstituting →
        ∀ actor fd bytes lost, tick.socket ≠ .wrote actor fd bytes lost) ∧
      tick.primitive = some ⟨.metadata, metadataCode request.op, decide (origin = .kernel)⟩
  live := by intro position before origin state request reply after result operation; exact base.live _ _ _ _ _ _ _ _ operation.1
  projection := by intro position before origin state request reply after result operation; exact base.projection _ _ _ _ _ _ _ _ operation.1

theorem recorded_metadata_recording {platform : MetadataFrame.PrimitiveContract}
    {runtime : MetadataOriginContract platform} {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity}
    (base : MetadataContract runtime mayTrace owner child) (start : Nat) (ticks : List Tick) :
    MetadataRecording runtime owner child (recordedMetadata base start ticks).returned start ticks := by
  constructor
  · intro position before origin state request reply after result operation
    obtain ⟨offset, tick, ordinal, selected, initial, final, action, table, effect, quiet, label⟩ := operation.2
    exact ⟨offset, tick, ordinal, selected, initial, final, action, table, effect, quiet⟩
  · intro position before origin state request reply after result operation
    obtain ⟨offset, tick, ordinal, selected, _, _, _, _, _, _, label⟩ := operation.2
    exact fixed_primitive_label ordinal selected label

def stateTick (child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (before : Context) (action : Action) (after : Context)
    (state : State) (socket : SocketObservation) : Tick where
  before := before
  action := action
  after := after
  objects := fun actor fd => if actor = taskKey child then
    stateObjects state fd else otherObjects actor fd
  cloexec := fun actor fd => if actor = taskKey child then
    stateFlags state fd else otherFlags actor fd
  socket := socket
  source := none

theorem state_tick_table (child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (before : Context) (action : Action) (after : Context)
    (state : State) (socket : SocketObservation) :
    NativeTable child state (stateTick child otherObjects otherFlags before action after state socket) := by
  intro fd bounded
  simp only [stateTick, stateObjects, stateFlags, bounded, ↓reduceIte, Nat.toUInt32, UInt32.ofNat_toNat, and_self]

def nativeSocket (child : ProcessIdentity) (request : Request) (reply : Reply) : SocketObservation :=
  if request.op = .readByte ∧ reply.1 = 1 then
    .read child request.a.toNat 1 (reply.2.data.toList.map UInt8.toNat)
  else .none

theorem native_socket (actual : TracerControl) (child : ProcessIdentity) (request : Request) (reply : Reply) :
    NativeSocket actual child .kernel request reply (nativeSocket child request reply) := by
  constructor
  · intro safe reading genuine count bounded
    simp only [nativeSocket, reading, count, and_self, ↓reduceIte]
  · intro safe genuine actor descriptor bytes lost wrote
    unfold nativeSocket at wrote
    split at wrote <;> contradiction

def nativeTick (child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (before : Context) (action : Action) (after : Context)
    (state : State) (request : Request) (reply : Reply) : Tick :=
  { stateTick child otherObjects otherFlags before action after state (nativeSocket child request reply) with
    primitive := some ⟨.native, request.op.code.toNat, true⟩ }

def metadataTick (child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (context : Context) (state : State)
    (request : LeanCageM3.Metadata.Request) : Tick :=
  { stateTick child otherObjects otherFlags context .native context state .none with
    primitive := some ⟨.metadata, metadataCode request.op, true⟩ }

def kernelState (fs : Filesystem) (state : State) (request : Request) (reply : Reply) : State :=
  if successfulReturn request reply then update fs request state else state

def kernelTicks (fs : Filesystem) (child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (context : Context) (state : State) : List (Request × Reply) → List Tick
  | [] => []
  | (request, reply) :: trace =>
      nativeTick child otherObjects otherFlags context .native context state request reply ::
        kernelTicks fs child otherObjects otherFlags context (kernelState fs state request reply) trace

def metadataState (state : State) (request : LeanCageM3.Metadata.Request)
    (reply : LeanCageM3.Metadata.Reply) : State :=
  match request.op with
  | .open => if reply.1 = 1 then MetadataFrame.opened state 1 MetadataWitness.handle else state
  | .read => state
  | .close => MetadataFrame.closed state request.fd

theorem metadata_effect_state {before after : State} {request : LeanCageM3.Metadata.Request}
    {reply : LeanCageM3.Metadata.Reply} (operation : MetadataWitness.Effect before request reply after) :
    after = metadataState before request reply := by
  cases operation <;> rfl

def metadataTicks (child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (context : Context) (state : State) :
    List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply) → List Tick
  | [] => []
  | (request, reply) :: trace =>
      metadataTick child otherObjects otherFlags context state request ::
        metadataTicks child otherObjects otherFlags context (metadataState state request reply) trace

-- §AR-entry.caller.origin: Embedding retains each generated primitive's actual global ordinal.
def Embedded (slice : List Tick) (offset : Nat) (ticks : List Tick) : Prop :=
  ∀ index tick, TickAt slice index tick → TickAt ticks (offset + index) tick

theorem embedded_head {tick : Tick} {rest ticks : List Tick} {offset : Nat}
    (embedding : Embedded (tick :: rest) offset ticks) : TickAt ticks offset tick := by
  simpa only [Nat.add_zero] using embedding 0 tick rfl

theorem embedded_tail {tick : Tick} {rest ticks : List Tick} {offset : Nat}
    (embedding : Embedded (tick :: rest) offset ticks) : Embedded rest (offset + 1) ticks := by
  intro index selected member
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using embedding (index + 1) selected member

theorem embedded_preserve_suffix {slice : List Tick} {index : Nat} {tick : Tick}
    (selected : TickAt slice index tick) (suffix : List Tick) : TickAt (slice ++ suffix) index tick := by
  induction slice generalizing index with
  | nil => contradiction
  | cons current slice ih =>
    cases index with
    | zero => exact selected
    | succ index => exact ih selected

theorem embedded_append (front slice suffix : List Tick) : Embedded slice front.length (front ++ slice ++ suffix) := by
  intro index tick selected
  induction front with
  | nil => simpa only [List.nil_append, List.length_nil, Nat.zero_add] using embedded_preserve_suffix selected suffix
  | cons current front ih =>
    simpa only [List.cons_append, List.length_cons, Nat.succ_add, TickAt] using ih

theorem embedded_prefix {first last ticks : List Tick} {offset : Nat}
    (embedding : Embedded (first ++ last) offset ticks) : Embedded first offset ticks := by
  intro index tick selected
  exact embedding index tick (embedded_preserve_suffix selected last)

theorem embedded_drop_left {first last ticks : List Tick} {offset : Nat}
    (embedding : Embedded (first ++ last) offset ticks) : Embedded last (offset + first.length) ticks := by
  intro index tick selected
  have inside : TickAt (first ++ last) (first.length + index) tick := by
    simpa only [List.append_nil] using embedded_append first last [] index tick selected
  simpa only [Nat.add_assoc] using embedding (first.length + index) tick inside

theorem metadata_ticks_length (child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (context : Context) (state : State)
    (trace : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)) :
    (metadataTicks child otherObjects otherFlags context state trace).length = trace.length := by
  induction trace generalizing state with
  | nil => rfl
  | cons current trace ih => simpa only [metadataTicks, List.length_cons] using congrArg Nat.succ (ih _)

theorem kernel_ticks_length (fs : Filesystem) (child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (context : Context) (state : State) (trace : List (Request × Reply)) :
    (kernelTicks fs child otherObjects otherFlags context state trace).length = trace.length := by
  induction trace generalizing state with
  | nil => rfl
  | cons current trace ih => simpa only [kernelTicks, List.length_cons] using congrArg Nat.succ (ih _)

theorem kernel_split {fs : Filesystem} {platform : PrimitiveContract fs} {before after : State}
    (first last : List (Request × Reply)) (run : KernelTrace platform before (first ++ last) after) :
    ∃ middle, KernelTrace platform before first middle ∧ KernelTrace platform middle last after := by
  induction first generalizing before with
  | nil => exact ⟨before, .nil _, run⟩
  | cons current first ih =>
    cases run with
    | cons request reply operation rest =>
      obtain ⟨middle, leading, remaining⟩ := ih rest
      exact ⟨middle, .cons request reply operation leading, remaining⟩

theorem execution_append {fs : Filesystem} {platform : PrimitiveContract fs}
    {originRuntime : OriginContract platform} {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity}
    {supervisor : SupervisorContract mayTrace owner child} {native : NativeContract originRuntime mayTrace owner child}
    {history : List Nat} {position : Nat} {before middle after : Context} {initial changed result : State}
    {firstActions lastActions : List Action} {firstTrace lastTrace : List (Request × Reply)}
    {firstControls lastControls : List TracerControl}
    (first : CallerPhysical.Execution supervisor native history position before initial firstActions firstTrace firstControls middle changed)
    (last : CallerPhysical.Execution supervisor native history (position + firstActions.length) middle changed
      lastActions lastTrace lastControls after result) :
    CallerPhysical.Execution supervisor native history position before initial (firstActions ++ lastActions)
      (firstTrace ++ lastTrace) (firstControls ++ lastControls) after result := by
  induction first with
  | done position context state => simpa only [List.length_nil, Nat.add_zero, List.nil_append] using last
  | supervisor source operation rest ih =>
    apply CallerPhysical.Execution.supervisor source operation
    apply ih
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using last
  | native origin request reply operation rest ih =>
    apply CallerPhysical.Execution.native origin request reply operation
    apply ih
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using last

theorem kernel_frame_execution {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity}
    (fs : Filesystem) (otherObjects : Nat → Nat → Option Nat) (otherFlags : Nat → Nat → Bool)
    (context : Context) (alive : context.childAlive = true) (start : Nat) (ticks : List Tick)
    (supervisor : SupervisorContract mayTrace owner child) {before after : State}
    {trace : List (Request × Reply)} (effects : KernelTrace (witnessPlatform fs) before trace after)
    (ordinary : ∀ pair ∈ trace, pair.1.op ≠ .traceMe) (offset : Nat)
    (embedding : Embedded (kernelTicks fs child otherObjects otherFlags context before trace) offset ticks)
    (history : List Nat) :
    CallerPhysical.Execution supervisor (recordedNative (primitiveNative (runtime fs) mayTrace owner child) start ticks)
      history (start + offset) context before (trace.map (fun _ => Action.native)) trace
      (trace.map (fun _ => control owner child context)) context after := by
  induction effects generalizing offset with
  | nil state => exact .done _ _ _
  | cons request reply operation remaining ih =>
    cases operation with
    | kernel _ _ _ query =>
      apply CallerPhysical.Execution.native .kernel request reply
      · refine ⟨.frame _ context .kernel _ _ request reply alive (.kernel (.kernel _ _ _ query))
          (Or.inl (ordinary (request, reply) (by simp))), offset,
          nativeTick child otherObjects otherFlags context .native context _ request reply,
          rfl, embedded_head embedding, rfl, rfl, Or.inl rfl,
          state_tick_table child otherObjects otherFlags context .native context _ (nativeSocket child request reply),
          native_socket _ _ _ _, rfl⟩
      · simpa only [Nat.add_assoc] using ih (by intro pair member; exact ordinary pair (by simp [member]))
          (offset + 1) (embedded_tail embedding)

theorem kernel_ticks_journal (mayTrace : ProcessIdentity → Prop) (owner child : ProcessIdentity) (history : List Nat)
    (fs : Filesystem) (otherObjects : Nat → Nat → Option Nat) (otherFlags : Nat → Nat → Bool)
    (context : Context) (state : State) (trace : List (Request × Reply)) :
    Journal mayTrace owner child history context (kernelTicks fs child otherObjects otherFlags context state trace) context := by
  induction trace generalizing state with
  | nil => exact .done _
  | cons current trace ih =>
    exact .next (nativeTick child otherObjects otherFlags context .native context state current.1 current.2)
      True.intro (.nativeFrame context context rfl rfl rfl rfl rfl rfl rfl) (ih _)

theorem metadata_ticks_journal (mayTrace : ProcessIdentity → Prop) (owner child : ProcessIdentity) (history : List Nat)
    (otherObjects : Nat → Nat → Option Nat) (otherFlags : Nat → Nat → Bool)
    (context : Context) (state : State) (trace : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)) :
    Journal mayTrace owner child history context (metadataTicks child otherObjects otherFlags context state trace) context := by
  induction trace generalizing state with
  | nil => exact .done _
  | cons current trace ih =>
    exact .next (metadataTick child otherObjects otherFlags context state current.1)
      True.intro (.nativeFrame context context rfl rfl rfl rfl rfl rfl rfl) (ih _)

theorem journal_append {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity} {history : List Nat}
    {before middle after : Context} {first last : List Tick}
    (leading : Journal mayTrace owner child history before first middle)
    (remaining : Journal mayTrace owner child history middle last after) :
    Journal mayTrace owner child history before (first ++ last) after := by
  induction leading with
  | done => exact remaining
  | next tick source operation rest ih => exact .next tick source operation (ih remaining)

theorem trace_me_returned {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity}
    (fs : Filesystem) (otherObjects : Nat → Nat → Option Nat) (otherFlags : Nat → Nat → Bool)
    (context : Context) (untraced : context.tracer = none) (parent : context.parentAlive = true)
    (alive : context.childAlive = true) (start offset : Nat) (ticks : List Tick)
    {before after : State} (effect : WitnessReturns fs .kernel before { op := .traceMe } (0, .empty) after)
    (selected : TickAt ticks offset
      (nativeTick child otherObjects otherFlags context .traceMe (tracedContext owner context)
        before { op := .traceMe } (0, .empty))) :
    (recordedNative (primitiveNative (runtime fs) mayTrace owner child) start ticks).returned
      (start + offset) context .kernel before { op := .traceMe } (0, .empty) (tracedContext owner context) after := by
  refine ⟨.traced _ context before after _ _ untraced parent alive (.kernel effect) rfl rfl,
    offset, _, rfl, selected, rfl, rfl, Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩),
    state_tick_table child otherObjects otherFlags context .traceMe (tracedContext owner context) before
      (nativeSocket child { op := .traceMe } (0, .empty)),
    native_socket _ _ _ _, rfl⟩

theorem frame_returned {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity}
    (fs : Filesystem) (otherObjects : Nat → Nat → Option Nat) (otherFlags : Nat → Nat → Bool)
    (context : Context) (alive : context.childAlive = true) (start offset : Nat) (ticks : List Tick)
    {before after : State} {request : Request} {reply : Reply}
    (effect : WitnessReturns fs .kernel before request reply after) (ordinary : request.op ≠ .traceMe)
    (selected : TickAt ticks offset
      (nativeTick child otherObjects otherFlags context .native context before request reply)) :
    (recordedNative (primitiveNative (runtime fs) mayTrace owner child) start ticks).returned
      (start + offset) context .kernel before request reply context after := by
  refine ⟨.frame _ context .kernel before after request reply alive (.kernel effect) (Or.inl ordinary),
    offset, _, rfl, selected, rfl, rfl, Or.inl rfl,
    state_tick_table child otherObjects otherFlags context .native context before (nativeSocket child request reply),
    native_socket _ _ _ _, rfl⟩

def signalTrace : List (Request × Reply) := MetadataWitness.trace (signalSetup MetadataWitness.inputs)
def tailCommands : List Command := releaseCommand MetadataWitness.inputs :: afterRelease MetadataWitness.inputs
def tailTrace : List (Request × Reply) := MetadataWitness.trace tailCommands

def traceCommand : Command := cmd MetadataWitness.inputs 1 { op := .traceMe } (beforeHandles := true)
def stopCommand : Command := cmd MetadataWitness.inputs 1 { op := .stop } (beforeHandles := true)

theorem useful_commands_cut : setup MetadataWitness.inputs =
    signalSetup MetadataWitness.inputs ++ traceCommand :: stopCommand :: tailCommands := by
  rw [setup_release_cut MetadataWitness.inputs rfl]
  simp only [beforeRelease, List.append_assoc, List.cons_append, List.nil_append]
  rfl

theorem useful_trace_cut : MetadataWitness.trace (setup MetadataWitness.inputs) =
    signalTrace ++ ({ op := .traceMe }, (0, .empty)) :: ({ op := .stop }, (0, .empty)) :: tailTrace := by
  rw [setup_release_cut MetadataWitness.inputs rfl]
  simp only [beforeRelease, MetadataWitness.trace, List.map_append, List.map_cons,
    List.append_assoc, List.cons_append, List.nil_append]
  rfl

theorem signal_trace_ordinary : ∀ pair ∈ signalTrace, pair.1.op ≠ .traceMe := by
  have checked : signalTrace.all (fun pair => decide (pair.1.op ≠ .traceMe)) = true := by decide
  intro pair member
  exact of_decide_eq_true (List.all_eq_true.mp checked pair member)

theorem tail_trace_ordinary : ∀ pair ∈ tailTrace, pair.1.op ≠ .traceMe := by
  have checked : tailTrace.all (fun pair => decide (pair.1.op ≠ .traceMe)) = true := by decide
  intro pair member
  exact of_decide_eq_true (List.all_eq_true.mp checked pair member)

theorem signal_targets_bounded : ∀ pair ∈ signalTrace,
    pair.1.op = .dup2 ∨ pair.1.op = .dup3 → pair.1.b.toUInt32.toNat ≤ 2147483647 := by
  have checked : signalTrace.all (fun pair =>
      decide (pair.1.op = .dup2 ∨ pair.1.op = .dup3 → pair.1.b.toUInt32.toNat ≤ 2147483647)) = true := by decide
  intro pair member
  exact of_decide_eq_true (List.all_eq_true.mp checked pair member)

theorem tail_targets_bounded : ∀ pair ∈ tailTrace,
    pair.1.op = .dup2 ∨ pair.1.op = .dup3 → pair.1.b.toUInt32.toNat ≤ 2147483647 := by
  have checked : tailTrace.all (fun pair =>
      decide (pair.1.op = .dup2 ∨ pair.1.op = .dup3 → pair.1.b.toUInt32.toNat ≤ 2147483647)) = true := by decide
  intro pair member
  exact of_decide_eq_true (List.all_eq_true.mp checked pair member)

theorem witness_trace_accepted (commands : List Command) : Accepted commands (MetadataWitness.trace commands) := by
  induction commands with
  | nil => exact .nil
  | cons command commands ih => exact .cons command _ (MetadataWitness.reply_accepted _) ih

-- §AR-entry.acceptance: The same runtime effects expose the actual stopped descriptor table.
theorem useful_kernel_segments :
    ∃ signals traced stopped result,
      KernelTrace (witnessPlatform exampleFilesystem) MetadataWitness.initial signalTrace signals ∧
      WitnessReturns exampleFilesystem .kernel signals { op := .traceMe } (0, .empty) traced ∧
      WitnessReturns exampleFilesystem .kernel traced { op := .stop } (0, .empty) stopped ∧
      KernelTrace (witnessPlatform exampleFilesystem) stopped tailTrace result ∧
      result = after exampleFilesystem (setup MetadataWitness.inputs) MetadataWitness.initial ∧
      stopped.handles = MetadataWitness.initial.handles ∧ stopped.filters = [] := by
  have run := MetadataWitness.setup_effects exampleFilesystem MetadataWitness.inputs rfl MetadataWitness.initial rfl
  rw [useful_trace_cut] at run
  obtain ⟨signals, leading, rest⟩ := kernel_split signalTrace _ run
  cases rest with
  | cons _ _ traceMe rest =>
    cases rest with
    | cons _ _ stop remaining =>
      refine ⟨signals, _, _, _, leading, traceMe, stop, remaining, rfl, ?_, ?_⟩
      · have prefixRun := kernel_trace_append leading
          (KernelTrace.cons { op := .traceMe } (0, .empty) traceMe
            (KernelTrace.cons { op := .stop } (0, .empty) stop (KernelTrace.nil _)))
        apply accepted_before_release_handles (witnessPlatform exampleFilesystem)
          (witness_trace_accepted (beforeRelease MetadataWitness.inputs))
          (fun command member => setup_guards_sound MetadataWitness.inputs rfl command (by
            rw [setup_release_cut MetadataWitness.inputs rfl]; exact List.mem_append_left _ member))
          (before_release_operations MetadataWitness.inputs)
        exact prefixRun
      · have prefixRun := kernel_trace_append leading
          (KernelTrace.cons { op := .traceMe } (0, .empty) traceMe
            (KernelTrace.cons { op := .stop } (0, .empty) stop (KernelTrace.nil _)))
        have clean := accepted_before_release_filters (witnessPlatform exampleFilesystem)
          (witness_trace_accepted (beforeRelease MetadataWitness.inputs))
          (fun command member => setup_guards_sound MetadataWitness.inputs rfl command (by
            rw [setup_release_cut MetadataWitness.inputs rfl]; exact List.mem_append_left _ member))
          (before_release_operations MetadataWitness.inputs) prefixRun
        exact clean

-- §AR-entry.caller.origin: The source/kernel producer supplies consecutive actual parent ticks.
inductive SupervisorSlice (mayTrace : ProcessIdentity → Prop) (owner child : ProcessIdentity)
    (ticks : List Tick) : Nat → Context → Nat → Context → Prop
  | done (offset : Nat) (context : Context) : SupervisorSlice mayTrace owner child ticks offset context offset context
  | next {offset final : Nat} {before after : Context} (tick : Tick)
      (selected : TickAt ticks offset tick) (initial : tick.before = before)
      (operation : Step mayTrace owner child before tick.action tick.after)
      (native : tick.action ≠ .native) (traceMe : tick.action ≠ .traceMe)
      (rest : SupervisorSlice mayTrace owner child ticks (offset + 1) tick.after final after) :
      SupervisorSlice mayTrace owner child ticks offset before final after

-- §AR-entry.acceptance: A blocked STOP may return after this sequence of committed parent effects.
inductive SupervisorSegment {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity}
    (supervisor : SupervisorContract mayTrace owner child) : Point → Point → Prop
  | done (point : Point) : SupervisorSegment supervisor point point
  | next {before final : Point} {middle : Context} {changed : State} {action : Action}
      (operation : supervisor.returned before.position before.context before.state action middle changed)
      (rest : SupervisorSegment supervisor (before.advance middle changed) final) :
      SupervisorSegment supervisor before final

theorem supervisor_slice_segment {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity}
    {ticks : List Tick} {offset final : Nat} {before after : Context}
    (slice : SupervisorSlice mayTrace owner child ticks offset before final after) (start : Nat) (state : State) :
    SupervisorSegment (recordedSupervisor mayTrace owner child start ticks)
      ⟨start + offset, before, state⟩ ⟨start + final, after, state⟩ := by
  induction slice with
  | done offset context => exact .done _
  | next tick selected initial operation native traceMe rest ih =>
    apply SupervisorSegment.next
    · exact ⟨_, tick, rfl, selected, initial, rfl, rfl, operation, native, traceMe, rfl⟩
    · simpa only [Point.advance, Nat.add_assoc] using ih

theorem supervisor_segment_startup {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {metadataPlatform : MetadataFrame.PrimitiveContract}
    {metadataRuntime : MetadataOriginContract metadataPlatform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {native : NativeContract runtime mayTrace owner child}
    {metadata : MetadataContract metadataRuntime mayTrace owner child} {α : Type} {program : Startup α}
    {before middle final : Point} {trace : List (Request × Reply)} {target : Request}
    (segment : SupervisorSegment supervisor before middle)
    (rest : StartupExecution supervisor native metadata program middle trace target final) :
    StartupExecution supervisor native metadata program before trace target final := by
  induction segment with
  | done => exact rest
  | next operation next ih => exact .supervised operation (ih rest)

-- §AR-entry.acceptance: Actual indexed primitive runs consume the shared script's control prefix.
theorem execution_lift_prefix {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {metadataPlatform : MetadataFrame.PrimitiveContract}
    {metadataRuntime : MetadataOriginContract metadataPlatform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {native : NativeContract runtime mayTrace owner child}
    {metadata : MetadataContract metadataRuntime mayTrace owner child} {history : List Nat}
    {position : Nat} {before after : Context} {initial result : State}
    {actions : List Action} {trace : List (Request × Reply)} {controls : List TracerControl}
    (run : CallerPhysical.Execution supervisor native history position before initial actions trace controls after result)
    {α : Type} {program last : Script α} (path : Script.Prefix program trace last)
    {remaining : List (Request × Reply)} {target : Request} {final : Point}
    (rest : StartupExecution supervisor native metadata (Startup.admission last)
      ⟨position + actions.length, after, result⟩ remaining target final) :
    StartupExecution supervisor native metadata (Startup.admission program)
      ⟨position, before, initial⟩ (trace ++ remaining) target final := by
  induction run generalizing program last with
  | done position context state =>
    cases path
    simpa only [List.length_nil, Nat.add_zero, List.nil_append] using rest
  | supervisor source operation following ih =>
    apply StartupExecution.supervised operation
    apply ih path
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rest
  | native origin request reply operation following ih =>
    cases path with
    | step _ next _ tail =>
      change StartupExecution supervisor native metadata
        (.call request (fun answer => Startup.admission (next answer))) _ _ target final
      apply StartupExecution.returned request _ reply origin operation
      apply ih tail
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rest

theorem accepted_commands_prefix {α : Type} (commands : List Command)
    (next : Option Failure → Script α) :
    Script.Prefix ((runCommands Script.effect commands).bind next)
      (MetadataWitness.trace commands) (next none) := by
  induction commands with
  | nil => exact .refl _
  | cons command commands ih =>
    change Script.Prefix (.call command.request (fun answer =>
      (if command.expected.accepts answer then runCommands Script.effect commands
        else .pure (some (commandFailure command answer))).bind next))
      ((command.request, MetadataWitness.reply command.expected) :: MetadataWitness.trace commands) (next none)
    apply Script.Prefix.step
    simpa only [MetadataWitness.reply_accepted, ↓reduceIte] using ih

theorem accepted_initial_commands_path {α : Type} (commands remaining : List Command)
    (next : Option Failure → Script α) :
    Script.Prefix ((runCommands Script.effect (commands ++ remaining)).bind next)
      (MetadataWitness.trace commands) ((runCommands Script.effect remaining).bind next) := by
  induction commands with
  | nil => exact .refl _
  | cons command commands ih =>
    change Script.Prefix (.call command.request (fun answer =>
      (if command.expected.accepts answer then runCommands Script.effect (commands ++ remaining)
        else .pure (some (commandFailure command answer))).bind next))
      ((command.request, MetadataWitness.reply command.expected) :: MetadataWitness.trace commands) _
    apply Script.Prefix.step
    simpa only [MetadataWitness.reply_accepted, ↓reduceIte] using ih

theorem at_exec_script_path {α : Type} {program : Script α} {trace : List (Request × Reply)}
    {request : Request} (control : AtExec program trace request) :
    ∃ next, Script.Prefix program trace (.call request next) := by
  induction control with
  | ready request next exec => exact ⟨next, .refl _⟩
  | returned request next reply rest ih =>
    obtain ⟨final, path⟩ := ih
    exact ⟨final, .step request next reply path⟩

theorem at_exec_target_operation {α : Type} {program : Script α} {trace : List (Request × Reply)}
    {request : Request} (control : AtExec program trace request) : request.op = .exec := by
  induction control with
  | ready _ _ actual => exact actual
  | returned _ _ _ _ ih => exact ih

theorem execution_lift_at_exec {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {metadataPlatform : MetadataFrame.PrimitiveContract}
    {metadataRuntime : MetadataOriginContract metadataPlatform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {native : NativeContract runtime mayTrace owner child}
    {metadata : MetadataContract metadataRuntime mayTrace owner child} {history : List Nat}
    {position : Nat} {before after : Context} {initial result : State}
    {actions : List Action} {trace : List (Request × Reply)} {controls : List TracerControl}
    (run : CallerPhysical.Execution supervisor native history position before initial actions trace controls after result)
    {α : Type} {program : Script α} {target : Request} (control : AtExec program trace target) :
    StartupExecution supervisor native metadata (Startup.admission program)
      ⟨position, before, initial⟩ trace target ⟨position + actions.length, after, result⟩ := by
  obtain ⟨next, path⟩ := at_exec_script_path control
  have exec := at_exec_target_operation control
  simpa only [List.append_nil] using execution_lift_prefix run path
    (StartupExecution.ready target (fun reply => Startup.admission (next reply)) _ exec)

-- §AR-metadata.primitives: Each node records one selected open, read or close occurrence.
inductive MetadataCalls {platform : MetadataFrame.PrimitiveContract}
    {runtime : MetadataOriginContract platform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} (metadata : MetadataContract runtime mayTrace owner child) :
    Point → List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply) → Point → Prop
  | done (point : Point) : MetadataCalls metadata point [] point
  | next (request : LeanCageM3.Metadata.Request) (reply : LeanCageM3.Metadata.Reply) (origin : ReturnOrigin)
      {before final : Point} {middle : Context} {changed : State}
      {trace : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)}
      (operation : metadata.returned before.position before.context origin before.state request reply middle changed)
      (rest : MetadataCalls metadata (before.advance middle changed) trace final) :
      MetadataCalls metadata before ((request, reply) :: trace) final

theorem metadata_calls_from_runs {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity}
    (otherObjects : Nat → Nat → Option Nat) (otherFlags : Nat → Nat → Bool)
    (context : Context) (alive : context.childAlive = true) (start : Nat) (ticks : List Tick)
    {α : Type} {program : LeanCageM3.Metadata.Program α} {before after : State}
    {trace : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)} {value : α}
    (effects : LeanCageM3.Metadata.Runs MetadataWitness.platform.returned program before trace value after)
    (offset : Nat) (embedding : Embedded (metadataTicks child otherObjects otherFlags context before trace) offset ticks) :
    MetadataCalls (recordedMetadata (primitiveMetadata metadataRuntime mayTrace owner child) start ticks)
      ⟨start + offset, context, before⟩ trace ⟨start + (offset + trace.length), context, after⟩ := by
  induction effects generalizing offset with
  | pure value state => exact .done _
  | call request next reply operation rest ih =>
    have changed := metadata_effect_state operation
    apply MetadataCalls.next request reply .kernel
    · refine ⟨.frame _ context .kernel _ _ request reply alive (.kernel operation), offset,
        metadataTick child otherObjects otherFlags context _ request,
        rfl, embedded_head embedding, rfl, rfl, ?_,
        state_tick_table child otherObjects otherFlags context .native context _ .none,
        .kernel operation, ?_, rfl⟩
      · intro genuine safe; rfl
      · intro genuine safe actor fd bytes lost wrote; cases wrote
    · have following := ih (offset + 1) (by
        rw [changed]
        exact embedded_tail embedding)
      simpa only [Point.advance, List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using following

theorem metadata_calls_control {platform : MetadataFrame.PrimitiveContract}
    {runtime : MetadataOriginContract platform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {metadata : MetadataContract runtime mayTrace owner child}
    {supervisor : SupervisorContract mayTrace owner child} {σ α : Type}
    {effect : σ → LeanCageM3.Metadata.Request → LeanCageM3.Metadata.Reply → σ → Prop}
    {program : LeanCageM3.Metadata.Program α} {initial result : σ} {value : α}
    {trace : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)}
    (control : LeanCageM3.Metadata.Runs effect program initial trace value result)
    {before after : Point} (calls : MetadataCalls metadata before trace after) :
    MetadataExecution supervisor metadata program before trace value after := by
  induction control generalizing before with
  | pure value state => cases calls; exact .pure value _
  | call request next reply operation rest ih =>
    cases calls with
    | next _ _ origin actual following => exact .returned request next reply origin actual (ih following)

-- §AR-entry.acceptance: Primitive recordings feed the maintained metadata and worker programs.
theorem useful_startup_from_calls {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {metadataPlatform : MetadataFrame.PrimitiveContract}
    {metadataRuntime : MetadataOriginContract metadataPlatform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {native : NativeContract runtime mayTrace owner child}
    {metadata : MetadataContract metadataRuntime mayTrace owner child}
    {before markerDone inspected final : Point} {trace : List (Request × Reply)} {target : Request}
    {markerTrace statusTrace : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)}
    (markerControl : LeanCageM3.Metadata.Runs MetadataWitness.platform.returned
      (LeanCageM3.Metadata.bounded "/leancage-m3-disposable-vm" 64) MetadataWitness.initial markerTrace
      (.ok MetadataWitness.marker) MetadataWitness.initial)
    (statusControl : LeanCageM3.Metadata.Runs MetadataWitness.platform.returned
      (LeanCageM3.Metadata.bounded "/proc/self/status" 8192) MetadataWitness.initial statusTrace
      (.ok MetadataWitness.status) MetadataWitness.initial)
    (markerCalls : MetadataCalls metadata before markerTrace markerDone)
    (statusCalls : MetadataCalls metadata markerDone statusTrace inspected)
    (body : StartupExecution supervisor native metadata (Startup.admission (admission MetadataWitness.inputs))
      inspected trace target final) :
    StartupExecution supervisor native metadata (Worker.startup false MetadataWitness.args)
      before trace target final := by
  simp only [Worker.startup, Startup.read, bind, Startup.bind, pure]
  refine .inspected _ _ _ (.ok MetadataWitness.marker) (metadata_calls_control markerControl markerCalls) ?_
  refine .inspected _ _ _ (.ok MetadataWitness.status) (metadata_calls_control statusControl statusCalls) ?_
  simp only [LeanCageM3.Metadata.inspection, Except.mapError, MetadataWitness.status,
    MetadataWitness.fromUTF8_roundtrip, MetadataWitness.status_threads, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, MetadataWitness.parsed, Worker.enabled]
  change StartupExecution supervisor native metadata (Startup.admission (admission MetadataWitness.inputs))
    inspected trace target final
  exact body

-- §AR-entry.acceptance: One journal drives signals, stop, actual parent effects, then setup.
theorem useful_body_on_recorded_ticks
    (mayTrace : ProcessIdentity → Prop) (owner child : ProcessIdentity) (history : List Nat)
    (beforeObjects afterObjects : Nat → Nat → Option Nat) (beforeFlags afterFlags : Nat → Nat → Bool)
    (start signalOffset tailOffset : Nat) (ticks : List Tick) (afterContext : Context)
    (alive : afterContext.childAlive = true) (signals traced stopped result : State)
    (signalsEffect : KernelTrace (witnessPlatform exampleFilesystem) MetadataWitness.initial signalTrace signals)
    (traceEffect : WitnessReturns exampleFilesystem .kernel signals { op := .traceMe } (0, .empty) traced)
    (stopEffect : WitnessReturns exampleFilesystem .kernel traced { op := .stop } (0, .empty) stopped)
    (tailEffect : KernelTrace (witnessPlatform exampleFilesystem) stopped tailTrace result)
    (signalEmbedding : Embedded (kernelTicks exampleFilesystem child beforeObjects beforeFlags (born 1 none)
      MetadataWitness.initial signalTrace) signalOffset ticks)
    (traceSelected : TickAt ticks (signalOffset + signalTrace.length)
      (nativeTick child beforeObjects beforeFlags (born 1 none) .traceMe (tracedContext owner (born 1 none))
        signals { op := .traceMe } (0, .empty)))
    (stopSelected : TickAt ticks (signalOffset + signalTrace.length + 1)
      (nativeTick child beforeObjects beforeFlags (tracedContext owner (born 1 none)) .native
        (tracedContext owner (born 1 none)) traced { op := .stop } (0, .empty)))
    (parent : SupervisorSlice mayTrace owner child ticks (signalOffset + signalTrace.length + 2)
      (tracedContext owner (born 1 none)) tailOffset afterContext)
    (tailEmbedding : Embedded (kernelTicks exampleFilesystem child afterObjects afterFlags afterContext stopped tailTrace)
      tailOffset ticks) :
    let supervisor := recordedSupervisor mayTrace owner child start ticks
    let native := recordedNative (primitiveNative (runtime exampleFilesystem) mayTrace owner child) start ticks
    let metadata := recordedMetadata (primitiveMetadata metadataRuntime mayTrace owner child) start ticks
    StartupExecution supervisor native metadata (Startup.admission (admission MetadataWitness.inputs))
      ⟨start + signalOffset, born 1 none, MetadataWitness.initial⟩
      (MetadataWitness.trace (setup MetadataWitness.inputs)) (execRequest MetadataWitness.inputs)
      ⟨start + (tailOffset + tailTrace.length), afterContext, result⟩ := by
  let supervisor := recordedSupervisor mayTrace owner child start ticks
  let native := recordedNative (primitiveNative (runtime exampleFilesystem) mayTrace owner child) start ticks
  let metadata := recordedMetadata (primitiveMetadata metadataRuntime mayTrace owner child) start ticks
  change StartupExecution supervisor native metadata _ _ _ _ _
  have tailRun := kernel_frame_execution exampleFilesystem afterObjects afterFlags afterContext alive start ticks
    supervisor tailEffect tail_trace_ordinary tailOffset tailEmbedding history
  have tailStartup : StartupExecution supervisor native metadata
      (Startup.admission ((runCommands Script.effect tailCommands).bind (finishSetup Script.effect MetadataWitness.inputs)))
      ⟨start + tailOffset, afterContext, stopped⟩ tailTrace (execRequest MetadataWitness.inputs)
      ⟨start + (tailOffset + tailTrace.length), afterContext, result⟩ := by
    simpa only [List.length_map, Nat.add_assoc] using execution_lift_at_exec tailRun
      (MetadataWitness.commands_control MetadataWitness.inputs rfl tailCommands)
  have parentStartup := supervisor_segment_startup (supervisor_slice_segment parent start stopped) tailStartup
  have stopReturn := frame_returned (mayTrace := mayTrace) (owner := owner) (child := child)
    exampleFilesystem beforeObjects beforeFlags
    (tracedContext owner (born 1 none)) rfl start (signalOffset + signalTrace.length + 1) ticks stopEffect
    (by decide) stopSelected
  have stopStartup : StartupExecution supervisor native metadata
      (Startup.admission ((runCommands Script.effect (stopCommand :: tailCommands)).bind
        (finishSetup Script.effect MetadataWitness.inputs)))
      ⟨start + (signalOffset + signalTrace.length + 1), tracedContext owner (born 1 none), traced⟩
      (({ op := .stop }, (0, .empty)) :: tailTrace) (execRequest MetadataWitness.inputs)
      ⟨start + (tailOffset + tailTrace.length), afterContext, result⟩ := by
    apply StartupExecution.returned { op := .stop } _ (0, .empty) .kernel stopReturn
    have accepted : stopCommand.expected.accepts (0, .empty) = true := rfl
    simpa only [Script.bind, accepted, ↓reduceIte, Point.advance,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.reduceAdd] using parentStartup
  have traceReturn := trace_me_returned (mayTrace := mayTrace) (owner := owner) (child := child)
    exampleFilesystem beforeObjects beforeFlags (born 1 none)
    rfl rfl rfl start (signalOffset + signalTrace.length) ticks traceEffect traceSelected
  have traceStartup : StartupExecution supervisor native metadata
      (Startup.admission ((runCommands Script.effect (traceCommand :: stopCommand :: tailCommands)).bind
        (finishSetup Script.effect MetadataWitness.inputs)))
      ⟨start + (signalOffset + signalTrace.length), born 1 none, signals⟩
      (({ op := .traceMe }, (0, .empty)) :: ({ op := .stop }, (0, .empty)) :: tailTrace)
      (execRequest MetadataWitness.inputs) ⟨start + (tailOffset + tailTrace.length), afterContext, result⟩ := by
    apply StartupExecution.returned { op := .traceMe } _ (0, .empty) .kernel traceReturn
    have accepted : traceCommand.expected.accepts (0, .empty) = true := rfl
    simpa only [Script.bind, accepted, ↓reduceIte, Point.advance, Nat.add_assoc] using stopStartup
  have signalsRun := kernel_frame_execution exampleFilesystem beforeObjects beforeFlags (born 1 none) rfl
    start ticks supervisor signalsEffect signal_trace_ordinary signalOffset signalEmbedding history
  have signalsPath := accepted_initial_commands_path (signalSetup MetadataWitness.inputs)
    (traceCommand :: stopCommand :: tailCommands) (finishSetup Script.effect MetadataWitness.inputs)
  have fullStartup := execution_lift_prefix signalsRun signalsPath (by
    simpa only [List.length_map, Nat.add_assoc] using traceStartup)
  unfold admission execute
  simp only [MetadataWitness.inputs_valid, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind]
  rw [useful_trace_cut, useful_commands_cut]
  exact fullStartup

-- §AR-entry.acceptance: The same global native and metadata occurrences execute the real startup.
theorem useful_startup_on_recorded_ticks
    (mayTrace : ProcessIdentity → Prop) (owner child : ProcessIdentity) (history : List Nat)
    (beforeObjects afterObjects : Nat → Nat → Option Nat) (beforeFlags afterFlags : Nat → Nat → Bool)
    (start metadataOffset tailOffset : Nat) (ticks : List Tick) (afterContext : Context)
    (alive : afterContext.childAlive = true) (signals traced stopped result : State)
    (signalsEffect : KernelTrace (witnessPlatform exampleFilesystem) MetadataWitness.initial signalTrace signals)
    (traceEffect : WitnessReturns exampleFilesystem .kernel signals { op := .traceMe } (0, .empty) traced)
    (stopEffect : WitnessReturns exampleFilesystem .kernel traced { op := .stop } (0, .empty) stopped)
    (tailEffect : KernelTrace (witnessPlatform exampleFilesystem) stopped tailTrace result)
    (markerEmbedding : Embedded (metadataTicks child beforeObjects beforeFlags (born 1 none) MetadataWitness.initial
      (MetadataWitness.contentTrace "/leancage-m3-disposable-vm" 64 MetadataWitness.marker)) metadataOffset ticks)
    (statusEmbedding : Embedded (metadataTicks child beforeObjects beforeFlags (born 1 none) MetadataWitness.initial
      (MetadataWitness.contentTrace "/proc/self/status" 8192 MetadataWitness.status)) (metadataOffset + 4) ticks)
    (signalEmbedding : Embedded (kernelTicks exampleFilesystem child beforeObjects beforeFlags (born 1 none)
      MetadataWitness.initial signalTrace) (metadataOffset + 8) ticks)
    (traceSelected : TickAt ticks (metadataOffset + 8 + signalTrace.length)
      (nativeTick child beforeObjects beforeFlags (born 1 none) .traceMe (tracedContext owner (born 1 none))
        signals { op := .traceMe } (0, .empty)))
    (stopSelected : TickAt ticks (metadataOffset + 8 + signalTrace.length + 1)
      (nativeTick child beforeObjects beforeFlags (tracedContext owner (born 1 none)) .native
        (tracedContext owner (born 1 none)) traced { op := .stop } (0, .empty)))
    (parent : SupervisorSlice mayTrace owner child ticks (metadataOffset + 8 + signalTrace.length + 2)
      (tracedContext owner (born 1 none)) tailOffset afterContext)
    (tailEmbedding : Embedded (kernelTicks exampleFilesystem child afterObjects afterFlags afterContext stopped tailTrace)
      tailOffset ticks) :
    let supervisor := recordedSupervisor mayTrace owner child start ticks
    let native := recordedNative (primitiveNative (runtime exampleFilesystem) mayTrace owner child) start ticks
    let metadata := recordedMetadata (primitiveMetadata metadataRuntime mayTrace owner child) start ticks
    StartupExecution supervisor native metadata (Worker.startup false MetadataWitness.args)
      ⟨start + metadataOffset, born 1 none, MetadataWitness.initial⟩
      (MetadataWitness.trace (setup MetadataWitness.inputs)) (execRequest MetadataWitness.inputs)
      ⟨start + (tailOffset + tailTrace.length), afterContext, result⟩ := by
  let supervisor := recordedSupervisor mayTrace owner child start ticks
  let native := recordedNative (primitiveNative (runtime exampleFilesystem) mayTrace owner child) start ticks
  let metadata := recordedMetadata (primitiveMetadata metadataRuntime mayTrace owner child) start ticks
  have markerCalls := metadata_calls_from_runs (mayTrace := mayTrace) (owner := owner) (child := child)
    beforeObjects beforeFlags (born 1 none) rfl start ticks MetadataWitness.marker_content_run metadataOffset markerEmbedding
  have statusCalls := metadata_calls_from_runs (mayTrace := mayTrace) (owner := owner) (child := child)
    beforeObjects beforeFlags (born 1 none) rfl start ticks MetadataWitness.status_content_run (metadataOffset + 4) statusEmbedding
  have body := useful_body_on_recorded_ticks mayTrace owner child history beforeObjects afterObjects beforeFlags afterFlags
    start (metadataOffset + 8) tailOffset ticks afterContext alive signals traced stopped result
    signalsEffect traceEffect stopEffect tailEffect signalEmbedding traceSelected stopSelected parent tailEmbedding
  apply useful_startup_from_calls MetadataWitness.marker_content_run MetadataWitness.status_content_run
  · simpa only [MetadataWitness.contentTrace, List.length_cons, List.length_nil, Nat.reduceAdd] using markerCalls
  · simpa only [MetadataWitness.contentTrace, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_assoc] using statusCalls
  · exact body

namespace FDData

abbrev Slot := Option (Nat × Bool)

def descriptors : List Nat := [0, 1, 2, 3, 4, 5, 6, 60]

def Supported (handles : UInt32 → Option Handle) : Prop :=
  ∀ fd handle, handles fd = some handle → fd.toNat ∈ descriptors

theorem duplicate_supported {before : UInt32 → Option Handle} (supported : Supported before)
    (source target : UInt32) (flag : Bool) (targetMember : target.toNat ∈ descriptors) :
    Supported (duplicate before source target flag) := by
  intro fd handle present
  unfold duplicate at present
  split at present
  · rename_i same
    simpa only [same] using targetMember
  · exact supported fd handle present

theorem step_supported (request : Request) (before : UInt32 → Option Handle) (supported : Supported before)
    (target : request.op = .dup2 ∨ request.op = .dup3 → request.b.toUInt32.toNat ∈ descriptors) :
    Supported (handleStep request before) := by
  cases operation : request.op <;> simp only [handleStep, operation]
  all_goals try exact supported
  · split
    · exact supported
    · exact duplicate_supported supported _ _ _ (target (Or.inl operation))
  · exact duplicate_supported supported _ _ _ (target (Or.inr operation))
  · intro fd handle present
    dsimp only at present
    split at present
    · split at present
      · cases prior : before fd with
        | none => simp only [prior, Option.map_none] at present; contradiction
        | some previous => exact supported fd previous prior
      · contradiction
    · exact supported fd handle present

theorem kernel_state_supported (state : State) (request : Request) (reply : Reply) (supported : Supported state.handles)
    (target : request.op = .dup2 ∨ request.op = .dup3 → request.b.toUInt32.toNat ∈ descriptors) :
    Supported (kernelState exampleFilesystem state request reply).handles := by
  unfold kernelState
  split
  · rw [update_handles]
    exact step_supported request state.handles supported target
  · exact supported

theorem initial_supported : Supported MetadataWitness.initial.handles := by
  intro fd handle present
  by_cases zero : fd = 0
  · subst fd; decide
  by_cases two : fd = 2
  · subst fd; decide
  by_cases four : fd = 4
  · subst fd; decide
  by_cases five : fd = 5
  · subst fd; decide
  by_cases six : fd = 6
  · subst fd; decide
  by_cases sixty : fd = 60
  · subst fd; decide
  simp only [MetadataWitness.initial, zero, two, four, five, six, sixty, ↓reduceIte] at present
  contradiction

def sample (state : State) : List Slot :=
  descriptors.map (fun fd => (state.handles fd.toUInt32).map (fun handle => (handle.object, handle.cloexec)))

-- §AR-entry.acceptance: Pure export indexing has no proof-dependent generic array access.
def atD {α : Type} (fallback : α) : List α → Nat → α
  | [], _ => fallback
  | value :: _, 0 => value
  | _ :: rest, index + 1 => atD fallback rest index

def lookup (slots : List Slot) (fd : Nat) : Slot :=
  if fd = 0 then atD none slots 0
  else if fd = 1 then atD none slots 1
  else if fd = 2 then atD none slots 2
  else if fd = 3 then atD none slots 3
  else if fd = 4 then atD none slots 4
  else if fd = 5 then atD none slots 5
  else if fd = 6 then atD none slots 6
  else if fd = 60 then atD none slots 7
  else none

def objects (slots : List Slot) (fd : Nat) : Option Nat := (lookup slots fd).map Prod.fst
def flags (slots : List Slot) (fd : Nat) : Bool := ((lookup slots fd).map Prod.snd).getD false

theorem lookup_member (state : State) (fd : Nat) (member : fd ∈ descriptors) :
    lookup (sample state) fd = (state.handles fd.toUInt32).map (fun handle => (handle.object, handle.cloexec)) := by
  simp only [descriptors, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h <;> subst fd <;> rfl

theorem lookup_absent (slots : List Slot) (fd : Nat) (absent : fd ∉ descriptors) : lookup slots fd = none := by
  simp only [descriptors, List.mem_cons, List.not_mem_nil, or_false, not_or] at absent
  simp only [lookup, absent.1, absent.2.1, absent.2.2.1, absent.2.2.2.1, absent.2.2.2.2.1,
    absent.2.2.2.2.2.1, absent.2.2.2.2.2.2.1, absent.2.2.2.2.2.2.2, ↓reduceIte]

def stateSlot (state : State) (fd : Nat) : Slot :=
  if fd ≤ 2147483647 then (state.handles fd.toUInt32).map (fun handle => (handle.object, handle.cloexec)) else none

theorem sampled_lookup (state : State) (supported : Supported state.handles) (fd : Nat) :
    lookup (sample state) fd = stateSlot state fd := by
  by_cases member : fd ∈ descriptors
  · have bounded : fd ≤ 2147483647 := by
      simp only [descriptors, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with h | h | h | h | h | h | h | h <;> subst fd <;> decide
    rw [lookup_member state fd member]
    simp only [stateSlot, bounded, ↓reduceIte]
  · rw [lookup_absent _ _ member]
    unfold stateSlot
    split
    · rename_i bounded
      have narrow : fd.toUInt32.toNat = fd := by
        apply UInt32.toNat_ofNat_of_lt'
        change fd < 4294967296
        omega
      cases prior : state.handles fd.toUInt32 with
      | none => rfl
      | some handle =>
        have present := supported fd.toUInt32 handle prior
        rw [narrow] at present
        exact False.elim (member present)
    · rfl

theorem sampled_objects (state : State) (supported : Supported state.handles) : objects (sample state) = stateObjects state := by
  funext fd
  rw [objects, sampled_lookup state supported]
  unfold stateSlot stateObjects
  split
  · simp only [Option.map_map]
    rfl
  · rfl

theorem sampled_flags (state : State) (supported : Supported state.handles) : flags (sample state) = stateFlags state := by
  funext fd
  rw [flags, sampled_lookup state supported]
  unfold stateSlot stateFlags
  split
  · simp only [Option.map_map]
    rfl
  · rfl

structure Frame where
  code : Nat
  before : List Slot
  after : List Slot
  read : Option (Nat × List Nat)
  deriving DecidableEq, Repr

def socket (child : ProcessIdentity) (read : Option (Nat × List Nat)) : SocketObservation :=
  match read with
  | none => .none
  | some (fd, bytes) => .read child fd 1 bytes

def tick (family : PrimitiveFamily) (child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (before : Context) (action : Action) (after : Context) (frame : Frame) : Tick where
  before := before
  action := action
  after := after
  objects := fun actor fd => if actor = taskKey child then objects frame.before fd else otherObjects actor fd
  cloexec := fun actor fd => if actor = taskKey child then flags frame.before fd else otherFlags actor fd
  socket := socket child frame.read
  source := none
  primitive := some ⟨family, frame.code, true⟩

def ticks (family : PrimitiveFamily) (child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (context : Context) (frames : List Frame) : List Tick :=
  frames.map (tick family child otherObjects otherFlags context .native context)

def readData (request : Request) (reply : Reply) : Option (Nat × List Nat) :=
  if request.op = .readByte ∧ reply.1 = 1 then some (request.a.toNat, reply.2.data.toList.map UInt8.toNat) else none

def nativeFrames (state : State) : List (Request × Reply) → List Frame
  | [] => []
  | (request, reply) :: trace =>
      let next := kernelState exampleFilesystem state request reply
      ⟨request.op.code.toNat, sample state, sample next, readData request reply⟩ :: nativeFrames next trace

def metadataFrames (state : State) : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply) → List Frame
  | [] => []
  | (request, reply) :: trace =>
      let next := metadataState state request reply
      ⟨metadataCode request.op, sample state, sample next, none⟩ :: metadataFrames next trace

def computedState (state : State) (trace : List (Request × Reply)) : State :=
  trace.foldl (fun current pair => kernelState exampleFilesystem current pair.1 pair.2) state

def signalState : State := computedState MetadataWitness.initial signalTrace

theorem native_socket_data (child : ProcessIdentity) (request : Request) (reply : Reply) :
    nativeSocket child request reply = socket child (readData request reply) := by
  unfold nativeSocket readData
  split <;> rfl

theorem native_tick_sample (child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (before : Context) (action : Action) (after : Context)
    (state : State) (request : Request) (reply : Reply) (next : List Slot) (supported : Supported state.handles) :
    nativeTick child otherObjects otherFlags before action after state request reply =
      tick .native child otherObjects otherFlags before action after
        ⟨request.op.code.toNat, sample state, next, readData request reply⟩ := by
  unfold nativeTick stateTick tick
  rw [sampled_objects state supported, sampled_flags state supported, native_socket_data]

theorem metadata_tick_sample (child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (context : Context) (state : State)
    (request : LeanCageM3.Metadata.Request) (next : List Slot) (supported : Supported state.handles) :
    metadataTick child otherObjects otherFlags context state request =
      tick .metadata child otherObjects otherFlags context .native context ⟨metadataCode request.op, sample state, next, none⟩ := by
  unfold metadataTick stateTick tick
  rw [sampled_objects state supported, sampled_flags state supported]
  rfl

theorem native_ticks_sample (child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (context : Context) (state : State) (trace : List (Request × Reply))
    (supported : Supported state.handles)
    (targets : ∀ pair ∈ trace, pair.1.op = .dup2 ∨ pair.1.op = .dup3 → pair.1.b.toUInt32.toNat ∈ descriptors) :
    kernelTicks exampleFilesystem child otherObjects otherFlags context state trace =
      ticks .native child otherObjects otherFlags context (nativeFrames state trace) := by
  induction trace generalizing state with
  | nil => rfl
  | cons current trace ih =>
    simp only [kernelTicks, nativeFrames, ticks, List.map_cons]
    rw [native_tick_sample child otherObjects otherFlags context .native context state current.1 current.2 _ supported]
    rw [ih _ (kernel_state_supported state current.1 current.2 supported (targets current (by simp)))
      (by intro pair member; exact targets pair (by simp [member]))]
    rfl

theorem signal_targets_supported : ∀ pair ∈ signalTrace,
    pair.1.op = .dup2 ∨ pair.1.op = .dup3 → pair.1.b.toUInt32.toNat ∈ descriptors := by
  have checked : signalTrace.all (fun pair =>
      decide (pair.1.op = .dup2 ∨ pair.1.op = .dup3 → pair.1.b.toUInt32.toNat ∈ descriptors)) = true := by decide
  intro pair member
  exact of_decide_eq_true (List.all_eq_true.mp checked pair member)

theorem tail_targets_supported : ∀ pair ∈ tailTrace,
    pair.1.op = .dup2 ∨ pair.1.op = .dup3 → pair.1.b.toUInt32.toNat ∈ descriptors := by
  have checked : tailTrace.all (fun pair =>
      decide (pair.1.op = .dup2 ∨ pair.1.op = .dup3 → pair.1.b.toUInt32.toNat ∈ descriptors)) = true := by decide
  intro pair member
  exact of_decide_eq_true (List.all_eq_true.mp checked pair member)

theorem computed_state_supported (state : State) (trace : List (Request × Reply))
    (supported : Supported state.handles)
    (targets : ∀ pair ∈ trace, pair.1.op = .dup2 ∨ pair.1.op = .dup3 → pair.1.b.toUInt32.toNat ∈ descriptors) :
    Supported (computedState state trace).handles := by
  induction trace generalizing state with
  | nil => exact supported
  | cons current trace ih =>
    exact ih _ (kernel_state_supported state current.1 current.2 supported (targets current (by simp)))
      (by intro pair member; exact targets pair (by simp [member]))

theorem signal_state_supported : Supported signalState.handles :=
  computed_state_supported _ _ initial_supported signal_targets_supported

theorem metadata_state_supported (state : State) (request : LeanCageM3.Metadata.Request)
    (reply : LeanCageM3.Metadata.Reply) (supported : Supported state.handles) :
    Supported (metadataState state request reply).handles := by
  cases request with
  | mk operation descriptor amount path => cases operation with
  | «open» =>
    simp only [metadataState]
    split
    · intro fd handle present
      dsimp only [MetadataFrame.opened] at present
      split at present
      · rename_i same
        subst fd
        decide
      · exact supported fd handle present
    · exact supported
  | read => exact supported
  | close =>
    simp only [metadataState]
    intro fd handle present
    dsimp only [MetadataFrame.closed] at present
    split at present
    · contradiction
    · exact supported fd handle present

theorem metadata_ticks_sample (child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (context : Context) (state : State)
    (trace : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)) (supported : Supported state.handles) :
    metadataTicks child otherObjects otherFlags context state trace =
      ticks .metadata child otherObjects otherFlags context (metadataFrames state trace) := by
  induction trace generalizing state with
  | nil => rfl
  | cons current trace ih =>
    simp only [metadataTicks, metadataFrames, ticks, List.map_cons]
    rw [metadata_tick_sample child otherObjects otherFlags context state current.1 _ supported]
    rw [ih _ (metadata_state_supported state current.1 current.2 supported)]
    rfl

-- §AR-entry.acceptance: Closed useful descriptor data use only the actual eight supported slots.
def snapshots : List (List Slot) :=
  [[some (999, false), none, some (999, false), none, some (300, false), some (303, false), some (306, false), some (182, false)],
   [some (999, false), some (3000, true), some (999, false), none, some (300, false), some (303, false), some (306, false), some (182, false)],
   [some (300, false), none, some (999, false), none, some (300, false), some (303, false), some (306, false), some (182, false)],
   [some (300, false), some (303, false), some (999, false), none, some (300, false), some (303, false), some (306, false), some (182, false)],
   [some (300, false), some (303, false), some (306, false), none, some (300, false), some (303, false), some (306, false), some (182, false)],
   [some (300, false), some (303, false), some (306, false), some (182, true), some (300, false), some (303, false), some (306, false), some (182, false)],
   [some (300, false), some (303, false), some (306, false), some (182, true), none, none, none, none],
   [some (300, false), some (303, false), some (306, false), none, none, none, none, none]]

def pack (code before after : Nat) (read : Option (Nat × List Nat) := none) : Frame :=
  ⟨code, atD [] snapshots before, atD [] snapshots after, read⟩

def signalFrames : List Frame := pack 0 0 0 :: List.replicate 62 (pack 1 0 0) ++ [pack 0 0 0]
def traceFrames : List Frame := [pack 2 0 0, pack 3 0 0]
def inspectionFrames : List Frame := [pack 0 0 1, pack 1 1 1, pack 1 1 1, pack 2 1 0]
def tailFrames : List Frame :=
  [pack 27 0 0 (some (60, [165])), pack 4 0 2, pack 4 2 3, pack 4 3 4, pack 5 4 5, pack 6 5 6] ++
  ([7, 8, 9, 10, 11, 11] ++ List.replicate 41 11 ++ [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 11, 11, 11, 22]).map
    (fun code => pack code 6 6)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem signal_frames_exact : nativeFrames MetadataWitness.initial signalTrace = signalFrames := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem tail_frames_exact : nativeFrames signalState tailTrace = tailFrames := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem marker_frames_exact : metadataFrames MetadataWitness.initial
    (MetadataWitness.contentTrace "/leancage-m3-disposable-vm" 64 MetadataWitness.marker) = inspectionFrames := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem status_frames_exact : metadataFrames MetadataWitness.initial
    (MetadataWitness.contentTrace "/proc/self/status" 8192 MetadataWitness.status) = inspectionFrames := by decide

theorem signal_ticks_exact (child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (context : Context) :
    kernelTicks exampleFilesystem child otherObjects otherFlags context MetadataWitness.initial signalTrace =
      ticks .native child otherObjects otherFlags context signalFrames := by
  rw [native_ticks_sample _ _ _ _ _ _ initial_supported signal_targets_supported, signal_frames_exact]

theorem tail_ticks_exact (child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (context : Context) :
    kernelTicks exampleFilesystem child otherObjects otherFlags context signalState tailTrace =
      ticks .native child otherObjects otherFlags context tailFrames := by
  rw [native_ticks_sample _ _ _ _ _ _ signal_state_supported tail_targets_supported, tail_frames_exact]

theorem marker_ticks_exact (child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (context : Context) :
    metadataTicks child otherObjects otherFlags context MetadataWitness.initial
      (MetadataWitness.contentTrace "/leancage-m3-disposable-vm" 64 MetadataWitness.marker) =
      ticks .metadata child otherObjects otherFlags context inspectionFrames := by
  rw [metadata_ticks_sample _ _ _ _ _ _ initial_supported, marker_frames_exact]

theorem status_ticks_exact (child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (context : Context) :
    metadataTicks child otherObjects otherFlags context MetadataWitness.initial
      (MetadataWitness.contentTrace "/proc/self/status" 8192 MetadataWitness.status) =
      ticks .metadata child otherObjects otherFlags context inspectionFrames := by
  rw [metadata_ticks_sample _ _ _ _ _ _ initial_supported, status_frames_exact]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem signal_state_sample : sample signalState = atD [] snapshots 0 := by decide

theorem trace_tick_exact (child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (before after : Context) :
    nativeTick child otherObjects otherFlags before .traceMe after signalState { op := .traceMe } (0, .empty) =
      tick .native child otherObjects otherFlags before .traceMe after (pack 2 0 0) := by
  rw [native_tick_sample child otherObjects otherFlags before .traceMe after signalState
    { op := .traceMe } (0, .empty) (atD [] snapshots 0) signal_state_supported, signal_state_sample]
  rfl

theorem stop_tick_exact (child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (context : Context) :
    nativeTick child otherObjects otherFlags context .native context signalState { op := .stop } (0, .empty) =
      tick .native child otherObjects otherFlags context .native context (pack 3 0 0) := by
  rw [native_tick_sample child otherObjects otherFlags context .native context signalState
    { op := .stop } (0, .empty) (atD [] snapshots 0) signal_state_supported, signal_state_sample]
  rfl

end FDData

theorem kernel_trace_computed_state {before after : State} {trace : List (Request × Reply)}
    (effects : KernelTrace (witnessPlatform exampleFilesystem) before trace after) :
    after = FDData.computedState before trace := by
  induction effects with
  | nil => rfl
  | cons request reply operation rest ih =>
    cases operation
    exact ih

-- §AR-entry.acceptance: The actual effect witness fixes every stopped worker state.
theorem useful_computed_kernel_segments :
    KernelTrace (witnessPlatform exampleFilesystem) MetadataWitness.initial signalTrace FDData.signalState ∧
    WitnessReturns exampleFilesystem .kernel FDData.signalState { op := .traceMe } (0, .empty) FDData.signalState ∧
    WitnessReturns exampleFilesystem .kernel FDData.signalState { op := .stop } (0, .empty) FDData.signalState ∧
    KernelTrace (witnessPlatform exampleFilesystem) FDData.signalState tailTrace
      (after exampleFilesystem (setup MetadataWitness.inputs) MetadataWitness.initial) := by
  obtain ⟨signals, traced, stopped, result, leading, traceMe, stop, remaining, final, handles, filters⟩ := useful_kernel_segments
  have signalsExact := kernel_trace_computed_state leading
  change signals = FDData.signalState at signalsExact
  subst signals
  have tracedExact : traced = FDData.signalState := by cases traceMe; rfl
  subst traced
  have stoppedExact : stopped = FDData.signalState := by cases stop; rfl
  subst stopped
  subst result
  exact ⟨leading, traceMe, stop, remaining⟩

theorem signal_trace_length : signalTrace.length = 64 := by decide
theorem tail_trace_length : tailTrace.length = 68 := by decide

-- §AR-entry.acceptance: Pure slices are the same actual indexed primitive executions.
theorem useful_startup_on_pure_ticks
    (mayTrace : ProcessIdentity → Prop) (owner child : ProcessIdentity) (history : List Nat)
    (beforeObjects afterObjects : Nat → Nat → Option Nat) (beforeFlags afterFlags : Nat → Nat → Bool)
    (start metadataOffset tailOffset : Nat) (ticks : List Tick) (afterContext : Context)
    (alive : afterContext.childAlive = true)
    (markerEmbedding : Embedded (FDData.ticks .metadata child beforeObjects beforeFlags (born 1 none)
      FDData.inspectionFrames) metadataOffset ticks)
    (statusEmbedding : Embedded (FDData.ticks .metadata child beforeObjects beforeFlags (born 1 none)
      FDData.inspectionFrames) (metadataOffset + 4) ticks)
    (signalEmbedding : Embedded (FDData.ticks .native child beforeObjects beforeFlags (born 1 none)
      FDData.signalFrames) (metadataOffset + 8) ticks)
    (traceSelected : TickAt ticks (metadataOffset + 72)
      (FDData.tick .native child beforeObjects beforeFlags (born 1 none) .traceMe (tracedContext owner (born 1 none))
        (FDData.pack 2 0 0)))
    (stopSelected : TickAt ticks (metadataOffset + 73)
      (FDData.tick .native child beforeObjects beforeFlags (tracedContext owner (born 1 none)) .native
        (tracedContext owner (born 1 none)) (FDData.pack 3 0 0)))
    (parent : SupervisorSlice mayTrace owner child ticks (metadataOffset + 74)
      (tracedContext owner (born 1 none)) tailOffset afterContext)
    (tailEmbedding : Embedded (FDData.ticks .native child afterObjects afterFlags afterContext FDData.tailFrames)
      tailOffset ticks) :
    let supervisor := recordedSupervisor mayTrace owner child start ticks
    let native := recordedNative (primitiveNative (runtime exampleFilesystem) mayTrace owner child) start ticks
    let metadata := recordedMetadata (primitiveMetadata metadataRuntime mayTrace owner child) start ticks
    StartupExecution supervisor native metadata (Worker.startup false MetadataWitness.args)
      ⟨start + metadataOffset, born 1 none, MetadataWitness.initial⟩
      (MetadataWitness.trace (setup MetadataWitness.inputs)) (execRequest MetadataWitness.inputs)
      ⟨start + (tailOffset + 68), afterContext,
        after exampleFilesystem (setup MetadataWitness.inputs) MetadataWitness.initial⟩ := by
  obtain ⟨signalsEffect, traceEffect, stopEffect, tailEffect⟩ := useful_computed_kernel_segments
  have startup := useful_startup_on_recorded_ticks mayTrace owner child history
    beforeObjects afterObjects beforeFlags afterFlags start metadataOffset tailOffset ticks afterContext alive
    FDData.signalState FDData.signalState FDData.signalState
    (after exampleFilesystem (setup MetadataWitness.inputs) MetadataWitness.initial)
    signalsEffect traceEffect stopEffect tailEffect
    (by rwa [FDData.marker_ticks_exact]) (by rwa [FDData.status_ticks_exact])
    (by rwa [FDData.signal_ticks_exact])
    (by rw [FDData.trace_tick_exact]; simpa only [signal_trace_length, Nat.add_assoc, Nat.reduceAdd] using traceSelected)
    (by rw [FDData.stop_tick_exact]; simpa only [signal_trace_length, Nat.add_assoc, Nat.reduceAdd] using stopSelected)
    (by simpa only [signal_trace_length, Nat.add_assoc, Nat.reduceAdd] using parent)
    (by rwa [FDData.tail_ticks_exact])
  simpa only [tail_trace_length] using startup

-- §AR-entry.caller.origin: Metadata, signals and STOP precede the actual parent source slice.
def usefulWorkerPrefix (owner child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) : List Tick :=
  FDData.ticks .metadata child otherObjects otherFlags (born 1 none) FDData.inspectionFrames ++
  FDData.ticks .metadata child otherObjects otherFlags (born 1 none) FDData.inspectionFrames ++
  FDData.ticks .native child otherObjects otherFlags (born 1 none) FDData.signalFrames ++
  [FDData.tick .native child otherObjects otherFlags (born 1 none) .traceMe (tracedContext owner (born 1 none))
    (FDData.pack 2 0 0),
   FDData.tick .native child otherObjects otherFlags (tracedContext owner (born 1 none)) .native
    (tracedContext owner (born 1 none)) (FDData.pack 3 0 0)]

def usefulWorkerTail (child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (context : Context) : List Tick :=
  FDData.ticks .native child otherObjects otherFlags context FDData.tailFrames

theorem usefulWorkerPrefix_length (owner child : ProcessIdentity) (objects : Nat → Nat → Option Nat)
    (flags : Nat → Nat → Bool) : (usefulWorkerPrefix owner child objects flags).length = 74 := by
  simp only [usefulWorkerPrefix, FDData.ticks, List.length_append, List.length_map,
    List.length_cons, List.length_nil]
  decide

theorem usefulWorkerTail_length (child : ProcessIdentity) (objects : Nat → Nat → Option Nat)
    (flags : Nat → Nat → Bool) (context : Context) :
    (usefulWorkerTail child objects flags context).length = 68 := by
  simp only [usefulWorkerTail, FDData.ticks, List.length_map]
  decide

-- §AR-entry.acceptance: Both real source branches and the real worker share one journal.
theorem useful_startup_on_concatenated_ticks_with_suffix
    (mayTrace : ProcessIdentity → Prop) (owner child : ProcessIdentity) (history : List Nat)
    (beforeObjects afterObjects : Nat → Nat → Option Nat) (beforeFlags afterFlags : Nat → Nat → Bool)
    (start : Nat) (childTicks parentTicks suffixTicks : List Tick) (afterContext : Context)
    (alive : afterContext.childAlive = true)
    (parent : SupervisorSlice mayTrace owner child
      (childTicks ++ usefulWorkerPrefix owner child beforeObjects beforeFlags ++ parentTicks ++
        usefulWorkerTail child afterObjects afterFlags afterContext ++ suffixTicks)
      (childTicks.length + 74) (tracedContext owner (born 1 none))
      (childTicks.length + 74 + parentTicks.length) afterContext) :
    let ticks := childTicks ++ usefulWorkerPrefix owner child beforeObjects beforeFlags ++ parentTicks ++
      usefulWorkerTail child afterObjects afterFlags afterContext ++ suffixTicks
    let supervisor := recordedSupervisor mayTrace owner child start ticks
    let native := recordedNative (primitiveNative (runtime exampleFilesystem) mayTrace owner child) start ticks
    let metadata := recordedMetadata (primitiveMetadata metadataRuntime mayTrace owner child) start ticks
    StartupExecution supervisor native metadata (Worker.startup false MetadataWitness.args)
      ⟨start + childTicks.length, born 1 none, MetadataWitness.initial⟩
      (MetadataWitness.trace (setup MetadataWitness.inputs)) (execRequest MetadataWitness.inputs)
      ⟨start + (childTicks.length + 74 + parentTicks.length + 68), afterContext,
        after exampleFilesystem (setup MetadataWitness.inputs) MetadataWitness.initial⟩ := by
  let markers := FDData.ticks .metadata child beforeObjects beforeFlags (born 1 none) FDData.inspectionFrames
  let signals := FDData.ticks .native child beforeObjects beforeFlags (born 1 none) FDData.signalFrames
  have markerLength : markers.length = 4 := rfl
  have signalLength : signals.length = 64 := by
    simp only [signals, FDData.ticks, List.length_map]
    decide
  have embedding := embedded_append childTicks (usefulWorkerPrefix owner child beforeObjects beforeFlags)
    (parentTicks ++ usefulWorkerTail child afterObjects afterFlags afterContext ++ suffixTicks)
  change Embedded (markers ++ markers ++ signals ++ _) _ _ at embedding
  simp only [List.append_assoc] at embedding
  have markerEmbedding := embedded_prefix (first := markers) embedding
  have afterMarker := embedded_drop_left (first := markers) embedding
  have statusEmbedding := embedded_prefix (first := markers) afterMarker
  have afterStatus := embedded_drop_left (first := markers) afterMarker
  have signalEmbedding := embedded_prefix (first := signals) afterStatus
  have traceEmbedding := embedded_drop_left (first := signals) afterStatus
  have traceSelected := embedded_head traceEmbedding
  have stopSelected := embedded_head (embedded_tail traceEmbedding)
  have tailEmbedding := embedded_append
    (childTicks ++ usefulWorkerPrefix owner child beforeObjects beforeFlags ++ parentTicks)
    (usefulWorkerTail child afterObjects afterFlags afterContext) suffixTicks
  apply useful_startup_on_pure_ticks mayTrace owner child history beforeObjects afterObjects beforeFlags afterFlags
    start childTicks.length (childTicks.length + 74 + parentTicks.length) _ afterContext alive
  · simpa only [List.append_assoc] using markerEmbedding
  · simpa only [markerLength, List.append_assoc] using statusEmbedding
  · simpa only [markerLength, Nat.add_assoc, Nat.reduceAdd, List.append_assoc] using signalEmbedding
  · simpa only [markerLength, signalLength, Nat.add_assoc, Nat.reduceAdd, List.append_assoc] using traceSelected
  · simpa only [markerLength, signalLength, Nat.add_assoc, Nat.reduceAdd, List.append_assoc] using stopSelected
  · exact parent
  · simpa only [usefulWorkerTail, List.append_nil, List.length_append, usefulWorkerPrefix_length,
      List.append_assoc, Nat.add_assoc] using tailEmbedding


theorem useful_startup_on_concatenated_ticks
    (mayTrace : ProcessIdentity → Prop) (owner child : ProcessIdentity) (history : List Nat)
    (beforeObjects afterObjects : Nat → Nat → Option Nat) (beforeFlags afterFlags : Nat → Nat → Bool)
    (start : Nat) (childTicks parentTicks : List Tick) (afterContext : Context)
    (alive : afterContext.childAlive = true)
    (parent : SupervisorSlice mayTrace owner child
      (childTicks ++ usefulWorkerPrefix owner child beforeObjects beforeFlags ++ parentTicks ++
        usefulWorkerTail child afterObjects afterFlags afterContext)
      (childTicks.length + 74) (tracedContext owner (born 1 none))
      (childTicks.length + 74 + parentTicks.length) afterContext) :
    let ticks := childTicks ++ usefulWorkerPrefix owner child beforeObjects beforeFlags ++ parentTicks ++
      usefulWorkerTail child afterObjects afterFlags afterContext
    let supervisor := recordedSupervisor mayTrace owner child start ticks
    let native := recordedNative (primitiveNative (runtime exampleFilesystem) mayTrace owner child) start ticks
    let metadata := recordedMetadata (primitiveMetadata metadataRuntime mayTrace owner child) start ticks
    StartupExecution supervisor native metadata (Worker.startup false MetadataWitness.args)
      ⟨start + childTicks.length, born 1 none, MetadataWitness.initial⟩
      (MetadataWitness.trace (setup MetadataWitness.inputs)) (execRequest MetadataWitness.inputs)
      ⟨start + (childTicks.length + 74 + parentTicks.length + 68), afterContext,
        after exampleFilesystem (setup MetadataWitness.inputs) MetadataWitness.initial⟩ := by
  simpa only [List.append_nil] using
    useful_startup_on_concatenated_ticks_with_suffix mayTrace owner child history
      beforeObjects afterObjects beforeFlags afterFlags start childTicks parentTicks [] afterContext alive
      (by simpa only [List.append_nil] using parent)


namespace FDData
-- §FS-entry.image: The last operation drops the CLOEXEC failure descriptor.
def execFrame : Frame := pack 23 6 7
end FDData

def usefulFinalState : State := after exampleFilesystem (setup MetadataWitness.inputs) MetadataWitness.initial

theorem useful_final_supported : FDData.Supported usefulFinalState.handles := by
  have effects := useful_computed_kernel_segments.2.2.2
  have computed := kernel_trace_computed_state effects
  change usefulFinalState = _ at computed
  rw [computed]
  exact FDData.computed_state_supported FDData.signalState tailTrace
    FDData.signal_state_supported FDData.tail_targets_supported

theorem useful_exec_supported : FDData.Supported (execState usefulFinalState 1).handles := by
  intro fd handle present
  cases prior : usefulFinalState.handles fd with
  | none => simp only [execState, execHandles, prior, Option.filter_none] at present; contradiction
  | some previous => exact useful_final_supported fd previous prior

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem useful_exec_frame_exact :
    (⟨(execRequest MetadataWitness.inputs).op.code.toNat, FDData.sample usefulFinalState,
      FDData.sample (execState usefulFinalState 1), none⟩ : FDData.Frame) = FDData.execFrame := by decide

-- §AR-entry.caller.origin: This tick is the actual successful image replacement operation.
def imageTick (child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (context : Context) (state : State) (request : Request) : Tick :=
  { stateTick child otherObjects otherFlags context .native context state .none with
    primitive := some ⟨.native, request.op.code.toNat, true⟩ }

theorem useful_image_tick_exact (child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (context : Context) :
    imageTick child otherObjects otherFlags context usefulFinalState (execRequest MetadataWitness.inputs) =
      FDData.tick .native child otherObjects otherFlags context .native context FDData.execFrame := by
  change nativeTick child otherObjects otherFlags context .native context usefulFinalState
    (execRequest MetadataWitness.inputs) (0, .empty) = _
  rw [FDData.native_tick_sample child otherObjects otherFlags context .native context usefulFinalState
    (execRequest MetadataWitness.inputs) (0, .empty) (FDData.sample (execState usefulFinalState 1)) useful_final_supported]
  have frame := useful_exec_frame_exact
  change FDData.Frame.mk _ _ _ _ = _ at frame
  exact congrArg (FDData.tick .native child otherObjects otherFlags context .native context) frame

theorem useful_exec_descriptor_data :
    stateObjects usefulFinalState = FDData.objects FDData.execFrame.before ∧
    stateFlags usefulFinalState = FDData.flags FDData.execFrame.before ∧
    stateObjects (execState usefulFinalState 1) = FDData.objects FDData.execFrame.after ∧
    stateFlags (execState usefulFinalState 1) = FDData.flags FDData.execFrame.after := by
  have before := congrArg FDData.Frame.before useful_exec_frame_exact
  have after := congrArg FDData.Frame.after useful_exec_frame_exact
  exact ⟨(FDData.sampled_objects _ useful_final_supported).symm.trans (congrArg FDData.objects before),
    (FDData.sampled_flags _ useful_final_supported).symm.trans (congrArg FDData.flags before),
    (FDData.sampled_objects _ useful_exec_supported).symm.trans (congrArg FDData.objects after),
    (FDData.sampled_flags _ useful_exec_supported).symm.trans (congrArg FDData.flags after)⟩

theorem selected_tick_unique {ticks : List Tick} {start position selectedOffset : Nat} {selectedTick : Tick}
    (ordinal : position = start + selectedOffset) (selected : TickAt ticks selectedOffset selectedTick) :
    ∀ offset tick, position = start + offset → TickAt ticks offset tick → tick = selectedTick := by
  intro offset tick current found
  have sameOffset := Nat.add_left_cancel (ordinal.symm.trans current)
  subst offset
  exact Option.some.inj ((tickAt_getElem found).symm.trans (tickAt_getElem selected))

-- §FS-entry.image: The image primitive retains one selected task, request and pre-exec table.
def recordedImage (owner child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (start : Nat) (ticks : List Tick) :
    ImageContract MetadataWitness.execution owner child start ticks where
  replaced := fun position before state request task after image =>
    request.op = .exec ∧ task = child ∧ after = before ∧ before.childAlive = true ∧
    image = ⟨execState state 1, request.text, request.args, request.data⟩ ∧
    ∃ offset, position = start + offset ∧
      TickAt ticks offset (imageTick child otherObjects otherFlags before state request)
  effect := by intro _ _ _ _ _ _ _ operation; exact ⟨operation.1, operation.2.2.2.2.1⟩
  occurrence := by
    intro _ _ _ _ _ _ _ operation
    obtain ⟨offset, ordinal, selected⟩ := operation.2.2.2.2.2
    exact ⟨offset, _, ordinal, selected, rfl⟩
  identity := by intro _ _ _ _ _ _ _ operation; exact operation.2.1
  live := by intro _ _ _ _ _ _ _ operation; exact operation.2.2.2.1
  scope := by intro _ _ _ _ _ _ _ operation; rw [operation.2.2.1]; exact ⟨rfl, rfl⟩
  noSocketWrite := by
    intro position before state request task after image operation safe offset tick ordinal found actor fd bytes lost
    obtain ⟨selectedOffset, positionAt, selected⟩ := operation.2.2.2.2.2
    have same := selected_tick_unique positionAt selected offset tick ordinal found
    cases same
    intro wrote
    cases wrote

-- §AR-entry.acceptance: The useful successful exec consumes that same recorded operation.
theorem useful_recorded_image (owner child : ProcessIdentity) (otherObjects : Nat → Nat → Option Nat)
    (otherFlags : Nat → Nat → Bool) (start offset : Nat) (ticks : List Tick) (context : Context)
    (alive : context.childAlive = true)
    (selected : TickAt ticks offset
      (FDData.tick .native child otherObjects otherFlags context .native context FDData.execFrame)) :
    (recordedImage owner child otherObjects otherFlags start ticks).replaced (start + offset) context
      usefulFinalState (execRequest MetadataWitness.inputs) child context
      ⟨execState usefulFinalState 1, (execRequest MetadataWitness.inputs).text,
        (execRequest MetadataWitness.inputs).args, (execRequest MetadataWitness.inputs).data⟩ := by
  refine ⟨rfl, rfl, rfl, alive, rfl, offset, rfl, ?_⟩
  rwa [useful_image_tick_exact]


-- §AR-entry.acceptance: The same source ticks feed startup and successful image replacement.
theorem useful_source_recorded_entry
    (mayTrace : ProcessIdentity → Prop) (owner child : ProcessIdentity) (history : List Nat)
    (beforeObjects afterObjects : Nat → Nat → Option Nat) (beforeFlags afterFlags : Nat → Nat → Bool)
    (start : Nat) (childTicks parentTicks : List Tick) (afterContext : Context)
    (alive : afterContext.childAlive = true)
    (parent : SupervisorSlice mayTrace owner child
      (childTicks ++ usefulWorkerPrefix owner child beforeObjects beforeFlags ++ parentTicks ++
        usefulWorkerTail child afterObjects afterFlags afterContext ++
        [FDData.tick .native child afterObjects afterFlags afterContext .native afterContext FDData.execFrame])
      (childTicks.length + 74) (tracedContext owner (born 1 none))
      (childTicks.length + 74 + parentTicks.length) afterContext) :
    let ticks := childTicks ++ usefulWorkerPrefix owner child beforeObjects beforeFlags ++ parentTicks ++
      usefulWorkerTail child afterObjects afterFlags afterContext ++
      [FDData.tick .native child afterObjects afterFlags afterContext .native afterContext FDData.execFrame]
    let supervisor := recordedSupervisor mayTrace owner child start ticks
    let native := recordedNative (primitiveNative (runtime exampleFilesystem) mayTrace owner child) start ticks
    let metadata := recordedMetadata (primitiveMetadata metadataRuntime mayTrace owner child) start ticks
    let image : Image := ⟨execState usefulFinalState 1, (execRequest MetadataWitness.inputs).text,
      (execRequest MetadataWitness.inputs).args, (execRequest MetadataWitness.inputs).data⟩
    StartupExecution supervisor native metadata (Worker.startup false MetadataWitness.args)
      ⟨start + childTicks.length, born 1 none, MetadataWitness.initial⟩
      (MetadataWitness.trace (setup MetadataWitness.inputs)) (execRequest MetadataWitness.inputs)
      ⟨start + (childTicks.length + 74 + parentTicks.length + 68), afterContext, usefulFinalState⟩ ∧
    (recordedImage owner child afterObjects afterFlags start ticks).replaced
      (start + (childTicks.length + 74 + parentTicks.length + 68)) afterContext usefulFinalState
      (execRequest MetadataWitness.inputs) child afterContext image := by
  constructor
  · exact useful_startup_on_concatenated_ticks_with_suffix mayTrace owner child history
      beforeObjects afterObjects beforeFlags afterFlags start childTicks parentTicks
      [FDData.tick .native child afterObjects afterFlags afterContext .native afterContext FDData.execFrame]
      afterContext alive parent
  · apply useful_recorded_image owner child afterObjects afterFlags start
      (childTicks.length + 74 + parentTicks.length + 68) _ afterContext alive
    have selected := embedded_head (embedded_append
      (childTicks ++ usefulWorkerPrefix owner child beforeObjects beforeFlags ++ parentTicks ++
        usefulWorkerTail child afterObjects afterFlags afterContext)
      [FDData.tick .native child afterObjects afterFlags afterContext .native afterContext FDData.execFrame] [])
    simpa only [List.append_nil, List.length_append, usefulWorkerPrefix_length, usefulWorkerTail_length,
      List.append_assoc, Nat.add_assoc] using selected


-- §AR-application-verification.authority: The useful source preparation has concrete grants.
def usefulWorkspaceObjects (token : Nat) : LeanCageM3.Ref := ⟨token.toUInt64, 1⟩

def usefulWorkspace : LeanCageM3.Processes where
  run := 1
  uid := 100000
  root := usefulWorkspaceObjects 10
  namespaceId := 1
  filter := LeanCageM3.Filter.bytes.data.toList
  grants := [⟨usefulWorkspaceObjects 300, false⟩, ⟨usefulWorkspaceObjects 303, true⟩,
    ⟨usefulWorkspaceObjects 306, true⟩]
  tasks := fun _ => none

theorem useful_workspace_prepared :
    ∀ p, Worker.parse MetadataWitness.args = some p →
      PreparedWorkspace exampleFilesystem p MetadataWitness.initial usefulWorkspaceObjects usefulWorkspace := by
  intro p parsed
  have same := Option.some.inj (MetadataWitness.parsed.symm.trans parsed)
  subst p
  refine ⟨rfl, rfl, rfl, ?_, initial_prepared_sources⟩
  intro fd member handle present
  change fd ∈ ([4, 5, 6] : List UInt32) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with four | five | six
  · subst fd
    change some (⟨300, true, false, false⟩ : Handle) = some handle at present
    cases Option.some.inj present
    exact .head _
  · subst fd
    change some (⟨303, false, true, false⟩ : Handle) = some handle at present
    cases Option.some.inj present
    exact .tail _ (.head _)
  · subst fd
    change some (⟨306, false, true, false⟩ : Handle) = some handle at present
    cases Option.some.inj present
    exact .tail _ (.tail _ (.head _))

theorem useful_workspace_group : (fun (_ : Nat) => (1 : LeanCageM3.RunId)) 1 = usefulWorkspace.run := rfl
theorem useful_workspace_namespace : (1 : Nat).toUInt64 = usefulWorkspace.namespaceId := rfl

def usefulWorkspaceImage : Image :=
  ⟨execState usefulFinalState 1, (execRequest MetadataWitness.inputs).text,
    (execRequest MetadataWitness.inputs).args, (execRequest MetadataWitness.inputs).data⟩

theorem useful_workspace_image_restricted :
    ImageRestricted exampleFilesystem MetadataWitness.inputs MetadataWitness.initial usefulWorkspaceImage := by
  have effects := MetadataWitness.setup_effects exampleFilesystem MetadataWitness.inputs rfl MetadataWitness.initial rfl
  have replaced : MetadataWitness.execution.replaced .detached usefulFinalState
      (execRequest MetadataWitness.inputs) usefulWorkspaceImage := ⟨rfl, rfl⟩
  exact admission_image_state (witnessPlatform exampleFilesystem) MetadataWitness.execution .detached
    MetadataWitness.inputs rfl MetadataWitness.initial usefulFinalState usefulWorkspaceImage
    (by decide) MetadataWitness.useful_control effects (by trivial) replaced

theorem useful_workspace_image_stdio : ImageStdio MetadataWitness.inputs MetadataWitness.initial usefulWorkspaceImage :=
  image_has_supplied_stdio useful_workspace_image_restricted initial_prepared_sources

-- §AR-entry.acceptance: The same concrete image inhabits the maintained public task invariant.
theorem useful_workspace_task (context : CallerPhysical.Context)
    (placed : context.cgroup = some 1) (namespaceId : context.namespaceId = 1) :
    LeanCageM3.taskSafe usefulWorkspace
      (workspaceTask usefulWorkspaceObjects
        (physicalProcessContext 1 usefulWorkspace.run (fun _ => 1) context) usefulWorkspaceImage) := by
  apply image_establishes_workspace_task useful_workspace_image_restricted usefulWorkspaceObjects usefulWorkspace
  · exact useful_workspace_prepared MetadataWitness.inputs MetadataWitness.parsed
  · exact physical_context_prepared 1 (fun _ => 1) context usefulWorkspace 1 1 placed namespaceId rfl rfl


-- §AR-entry.acceptance: Both source branches and primitive slices share this single journal.
def usefulEntryTicks (owner child : ProcessIdentity)
    (beforeObjects afterObjects : Nat → Nat → Option Nat) (beforeFlags afterFlags : Nat → Nat → Bool)
    (childTicks parentTicks : List Tick) (afterContext : Context) : List Tick :=
  childTicks ++ usefulWorkerPrefix owner child beforeObjects beforeFlags ++ parentTicks ++
    usefulWorkerTail child afterObjects afterFlags afterContext ++
    [FDData.tick .native child afterObjects afterFlags afterContext .native afterContext FDData.execFrame]

-- §AR-entry.caller.receipt: Consume the same source package in the maintained public theorem.
theorem useful_public_workspace (lineageRuntime : CallerLineageContract)
    (mayTrace : ProcessIdentity → Prop) (owner child : ProcessIdentity) (history : List Nat)
    (beforeObjects afterObjects : Nat → Nat → Option Nat) (beforeFlags afterFlags : Nat → Nat → Bool)
    (childTicks parentTicks : List Tick) (afterContext : Context) (alive : afterContext.childAlive = true)
    (parent : SupervisorSlice mayTrace owner child
      (usefulEntryTicks owner child beforeObjects afterObjects beforeFlags afterFlags childTicks parentTicks afterContext)
      (childTicks.length + 74) (tracedContext owner (born 1 none))
      (childTicks.length + 74 + parentTicks.length) afterContext)
    (journal : Journal mayTrace owner child history (born 1 none)
      (usefulEntryTicks owner child beforeObjects afterObjects beforeFlags afterFlags childTicks parentTicks afterContext)
      afterContext)
    (source : CallerRequestsAllowed history)
    (writes : ∀ offset tick,
      TickAt (usefulEntryTicks owner child beforeObjects afterObjects beforeFlags afterFlags
        childTicks parentTicks afterContext) offset tick → WriteSourceOrExternal owner child tick)
    (values : ArgumentMeaning.nativeValues 100000 4 5 6 60 "run".toUTF8.data.toList
      "/m3-runs/100000/root".toUTF8.data.toList "normal".toUTF8.data.toList
      ["/bin/sh".toUTF8.data.toList] argumentBytes)
    (cgroupFiles : Nat → Option Nat)
    (caller : SourceScopeProducer owner child 0 (childTicks.length + 74 + parentTicks.length + 68)
      (usefulEntryTicks owner child beforeObjects afterObjects beforeFlags afterFlags childTicks parentTicks afterContext)
      1 60 182 cgroupFiles)
    {ancestorTask : ProcessIdentity} {ancestorInstalled installed : List ByteArray} {labels : List LineageLabel}
    (ancestor : CallerLineage lineageRuntime ancestorTask ancestorInstalled)
    (inherited : LineageEffects lineageRuntime ancestorTask ancestorInstalled labels child installed)
    (labelsChecked : CallerLabelsAllowed labels) :
    ∃ p, ParsedHandoff MetadataWitness.args p ∧
      NativeInputValues p 100000 4 5 6 60 "run".toUTF8.data.toList
        "/m3-runs/100000/root".toUTF8.data.toList "normal".toUTF8.data.toList ["/bin/sh".toUTF8.data.toList] ∧
      ImageRestricted exampleFilesystem p MetadataWitness.initial usefulWorkspaceImage ∧
      ImageStdio p MetadataWitness.initial usefulWorkspaceImage ∧
      afterContext.cgroup = some 1 ∧ afterContext.namespaceId = 1 ∧
      LeanCageM3.taskSafe usefulWorkspace
        (workspaceTask usefulWorkspaceObjects
          (physicalProcessContext 1 usefulWorkspace.run (fun _ => 1) afterContext) usefulWorkspaceImage) := by
  let ticks := usefulEntryTicks owner child beforeObjects afterObjects beforeFlags afterFlags
    childTicks parentTicks afterContext
  have joined := useful_source_recorded_entry mayTrace owner child history beforeObjects afterObjects
    beforeFlags afterFlags 0 childTicks parentTicks afterContext alive parent
  obtain ⟨run, replaced⟩ := joined
  have actualValues : ArgumentMeaning.nativeValues 100000 4 5 6 60 "run".toUTF8.data.toList
      "/m3-runs/100000/root".toUTF8.data.toList "normal".toUTF8.data.toList
      ["/bin/sh".toUTF8.data.toList] (MetadataWitness.args.map (·.toUTF8.data.toList)) := by
    rw [source_arguments_match]
    exact values
  have failure : ∀ p, Worker.parse MetadataWitness.args = some p →
      ∃ handle, MetadataWitness.initial.handles p.failure = some handle ∧ handle.object = 182 := by
    intro p parsed
    have same := Option.some.inj (MetadataWitness.parsed.symm.trans parsed)
    subst p
    exact ⟨⟨182, true, true, false⟩, rfl, rfl⟩
  have observed : StackObservation installed MetadataWitness.initial := by intro _; rfl
  obtain ⟨p, parsed, inputs, restricted, stdio, identity, scope, namespaceId, task⟩ :=
    production_source_workspace (witnessPlatform exampleFilesystem) (runtime exampleFilesystem) lineageRuntime
      MetadataWitness.platform metadataRuntime MetadataWitness.execution
      (recordedImage owner child afterObjects afterFlags 0 ticks) MetadataWitness.args usefulWorkspaceImage
      (by change MetadataWitness.initial.boundingCaps &&& 18446741874686296064 = 0; decide)
      100000 4 5 6 60 "run".toUTF8.data.toList "/m3-runs/100000/root".toUTF8.data.toList
      "normal".toUTF8.data.toList ["/bin/sh".toUTF8.data.toList] actualValues usefulWorkspaceObjects usefulWorkspace
      1 (fun _ => 1) 1 useful_workspace_prepared rfl rfl journal
      (recorded_supervisor_recording mayTrace owner child 0 ticks writes)
      (recorded_native_recording (primitiveNative (runtime exampleFilesystem) mayTrace owner child) 0 ticks)
      (recorded_metadata_recording (primitiveMetadata metadataRuntime mayTrace owner child) 0 ticks)
      ancestor inherited labelsChecked observed source run (by decide) 182 failure cgroupFiles
      (by simpa only [Nat.zero_add] using caller) replaced
  exact ⟨p, parsed, inputs, restricted, stdio, scope, namespaceId, task⟩


-- §FS-entry.provenance: This useful primitive model retains arbitrary unauthorized filter effects.
def usefulLineage (bootTask : ProcessIdentity) : CallerLineageContract where
  booted := fun task filters => task = bootTask ∧ filters = []
  step := fun kind request before after installed changed =>
    (kind = 0 ∨ after = before) ∧ (CallerLineageAllowed kind request → changed = installed)
  linuxBoot := by intro _ _ boot; exact boot.2
  primitiveFrame := by intro _ _ _ _ _ _ operation allowed; exact operation.2 allowed
  primitiveIdentity := by intro _ _ _ _ _ _ operation; exact operation.1

theorem lineage_effects_append {runtime : CallerLineageContract} {before middle after : ProcessIdentity}
    {initial changed final : List ByteArray} {first last : List LineageLabel}
    (leading : LineageEffects runtime before initial first middle changed)
    (remaining : LineageEffects runtime middle changed last after final) :
    LineageEffects runtime before initial (first ++ last) after final := by
  induction leading with
  | done => exact remaining
  | next label operation rest ih => exact .next label operation (ih remaining)

theorem lineage_frames (bootTask task : ProcessIdentity) (installed : List ByteArray) (labels : List LineageLabel) :
    LineageEffects (usefulLineage bootTask) task installed labels task installed := by
  induction labels with
  | nil => exact .done _ _
  | cons label labels ih => exact .next label ⟨Or.inr rfl, fun _ => rfl⟩ ih

theorem lineage_labels_append {first last : List LineageLabel}
    (leading : CallerLabelsAllowed first) (remaining : CallerLabelsAllowed last) :
    CallerLabelsAllowed (first ++ last) := by
  induction first with
  | nil => exact remaining
  | cons label labels ih => exact ⟨leading.1, ih leading.2⟩

-- §AR-entry.caller.origin: Follow actual common source, selected fork, child source and runtime.
def usefulSourceLabels (common child : List LineageLabel) : List LineageLabel :=
  common ++ (⟨0, 0⟩ :: (child ++ [⟨4, 0⟩]))

-- §AR-entry.acceptance: The ancestor boots once; child lineage crosses the actual fork.
theorem useful_source_lineage (owner child : ProcessIdentity) (commonLabels childLabels : List LineageLabel)
    (commonChecked : CallerLabelsAllowed commonLabels) (childChecked : CallerLabelsAllowed childLabels) :
    CallerLineage (usefulLineage owner) owner [] ∧
    LineageEffects (usefulLineage owner) owner [] (usefulSourceLabels commonLabels childLabels) child [] ∧
    CallerLabelsAllowed (usefulSourceLabels commonLabels childLabels) := by
  refine ⟨.boot ⟨rfl, rfl⟩, ?_, ?_⟩
  · have fork : (usefulLineage owner).step 0 0 owner child [] [] := ⟨Or.inl rfl, fun _ => rfl⟩
    have start : (usefulLineage owner).step 4 0 child child [] [] := ⟨Or.inr rfl, fun _ => rfl⟩
    have childEffects := lineage_effects_append (lineage_frames owner child [] childLabels)
      (LineageEffects.next ⟨4, 0⟩ start (LineageEffects.done child []))
    exact lineage_effects_append (lineage_frames owner owner [] commonLabels)
      (LineageEffects.next ⟨0, 0⟩ fork childEffects)
  · apply lineage_labels_append commonChecked
    refine ⟨Or.inl rfl, ?_⟩
    apply lineage_labels_append childChecked
    exact ⟨by simp [CallerLineageAllowed], True.intro⟩


-- §AR-entry.caller.receipt: The source ancestry and one recorded launch feed the public guarantee.
-- §AR-entry.caller.values: The exact source-bound argumentBytes have these unique values.
theorem useful_native_values :
    ArgumentMeaning.nativeValues 100000 4 5 6 60 "run".toUTF8.data.toList
      "/m3-runs/100000/root".toUTF8.data.toList "normal".toUTF8.data.toList
      ["/bin/sh".toUTF8.data.toList] argumentBytes := by
  intro uid input output errors failure mode root fault argv values
  obtain ⟨uidText, inputText, outputText, errorsText, failureText, original,
    uidValue, inputValue, outputValue, errorsValue, failureValue⟩ := values
  simp only [argumentBytes, List.cons.injEq] at original
  rcases original with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  change some 100000 = some uid at uidValue
  change some 4 = some input at inputValue
  change some 5 = some output at outputValue
  change some 6 = some errors at errorsValue
  change some 60 = some failure at failureValue
  refine ⟨(Option.some.inj uidValue).symm, (Option.some.inj inputValue).symm,
    (Option.some.inj outputValue).symm, (Option.some.inj errorsValue).symm,
    (Option.some.inj failureValue).symm, ?_, ?_, ?_, ?_⟩
  all_goals decide



theorem useful_public_source_workspace
    (mayTrace : ProcessIdentity → Prop) (owner child : ProcessIdentity) (history : List Nat)
    (beforeObjects afterObjects : Nat → Nat → Option Nat) (beforeFlags afterFlags : Nat → Nat → Bool)
    (childTicks parentTicks : List Tick) (afterContext : Context) (alive : afterContext.childAlive = true)
    (parent : SupervisorSlice mayTrace owner child
      (usefulEntryTicks owner child beforeObjects afterObjects beforeFlags afterFlags childTicks parentTicks afterContext)
      (childTicks.length + 74) (tracedContext owner (born 1 none))
      (childTicks.length + 74 + parentTicks.length) afterContext)
    (journal : Journal mayTrace owner child history (born 1 none)
      (usefulEntryTicks owner child beforeObjects afterObjects beforeFlags afterFlags childTicks parentTicks afterContext)
      afterContext)
    (source : CallerRequestsAllowed history)
    (writes : ∀ offset tick,
      TickAt (usefulEntryTicks owner child beforeObjects afterObjects beforeFlags afterFlags
        childTicks parentTicks afterContext) offset tick → WriteSourceOrExternal owner child tick)
    (cgroupFiles : Nat → Option Nat)
    (caller : SourceScopeProducer owner child 0 (childTicks.length + 74 + parentTicks.length + 68)
      (usefulEntryTicks owner child beforeObjects afterObjects beforeFlags afterFlags childTicks parentTicks afterContext)
      1 60 182 cgroupFiles)
    (commonLabels childLabels : List LineageLabel)
    (commonChecked : CallerLabelsAllowed commonLabels) (childChecked : CallerLabelsAllowed childLabels) :
    ∃ p, ParsedHandoff MetadataWitness.args p ∧
      NativeInputValues p 100000 4 5 6 60 "run".toUTF8.data.toList
        "/m3-runs/100000/root".toUTF8.data.toList "normal".toUTF8.data.toList ["/bin/sh".toUTF8.data.toList] ∧
      ImageRestricted exampleFilesystem p MetadataWitness.initial usefulWorkspaceImage ∧
      ImageStdio p MetadataWitness.initial usefulWorkspaceImage ∧
      afterContext.cgroup = some 1 ∧ afterContext.namespaceId = 1 ∧
      LeanCageM3.taskSafe usefulWorkspace
        (workspaceTask usefulWorkspaceObjects
          (physicalProcessContext 1 usefulWorkspace.run (fun _ => 1) afterContext) usefulWorkspaceImage) := by
  obtain ⟨ancestor, inherited, checked⟩ := useful_source_lineage owner child commonLabels childLabels commonChecked childChecked
  exact useful_public_workspace (usefulLineage owner) mayTrace owner child history
    beforeObjects afterObjects beforeFlags afterFlags childTicks parentTicks afterContext alive parent journal source
    writes useful_native_values cgroupFiles caller ancestor inherited checked


end CallerWitness

end LeanCage.Entry
