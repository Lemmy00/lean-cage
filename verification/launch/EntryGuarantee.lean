import ProcessProvenance
import CallerProvenance
import MetadataOrigins
import StartupExecution
import EntryGuarantee.ScopeReceipt
import LeanCageM3.ProcessProofs

namespace LeanCage.Entry

-- §AR-entry.caller: Preparation relates physical object tokens to the existing workspace model.
def workspaceHandle (objects : Nat → LeanCageM3.Ref) (handle : Handle) : LeanCageM3.Handle :=
  ⟨objects handle.object, handle.writable⟩

def workspaceCredentials (state : State) : LeanCageM2.Credentials :=
  { realUid := state.uid.real, effectiveUid := state.uid.effective,
    savedUid := state.uid.saved, fsUid := state.uid.filesystem,
    realGid := state.gid.real, effectiveGid := state.gid.effective,
    savedGid := state.gid.saved, fsGid := state.gid.filesystem,
    groups := state.groups, effectiveCaps := state.effectiveCaps,
    permittedCaps := state.permittedCaps, inheritableCaps := state.inheritableCaps,
    ambientCaps := state.ambientCaps, boundingCaps := state.boundingCaps }

-- §FS-linux-product.proofs.entry: Scope metadata is separate from credential/descriptor state.
structure ProcessContext where
  generation : UInt64
  owner : LeanCageM3.RunId
  scope : LeanCageM3.RunId
  namespaceId : UInt64

def workspaceTask (objects : Nat → LeanCageM3.Ref) (context : ProcessContext)
    (image : Image) : LeanCageM3.Task :=
  { generation := context.generation, owner := context.owner, scope := context.scope,
    credentials := workspaceCredentials image.state, root := objects image.state.root,
    namespaceId := context.namespaceId,
    handles := ([0, 1, 2] : List UInt32).filterMap
      (fun fd => (image.state.handles fd).map (workspaceHandle objects)),
    nnp := image.state.noNewPrivs,
    filter := (image.state.filters.headD .empty).data.toList }

-- §FS-entry.inputs: Prepared source slots are present and have their actual access modes.
def SourceBindings (p : Inputs) (initial : State) (input output errors failure : Handle) : Prop :=
  initial.handles p.input = some input ∧ initial.handles p.output = some output ∧
    initial.handles p.errors = some errors ∧ initial.handles p.failure = some failure

def SourceClasses (input output errors failure : Handle) : Prop :=
  input.readable = true ∧ input.writable = false ∧
    output.readable = false ∧ output.writable = true ∧
    errors.readable = false ∧ errors.writable = true ∧
    failure.readable = true ∧ failure.writable = true

def PreparedSources (p : Inputs) (initial : State) : Prop :=
  ∃ input output errors failure, SourceBindings p initial input output errors failure ∧
    SourceClasses input output errors failure

namespace PhysicalHandoff

-- §FS-entry.release: Both socket endpoints are duplex; ordinary objects use prepared modes.
def objectAccess (ordinary : Nat → Bool) (object : Nat) : Bool :=
  if object % 3 = 0 then ordinary (object / 3) else true

theorem child_endpoint_access (ordinary : Nat → Bool) (channel : Nat) :
    objectAccess ordinary (objectCode 2 channel) = true := by
  simp [objectAccess, objectCode, Nat.add_mod]

-- §FS-entry.inputs: Aliased ordinary objects may have distinct descriptor access modes.
def descriptorAccess (objects : Nat → Option Nat) (ordinary : Nat → Bool) (fd : Nat) : Bool :=
  match objects fd with
  | none => ordinary fd
  | some object => objectAccess (fun _ => ordinary fd) object

theorem descriptor_endpoint_access {objects : Nat → Option Nat} (ordinary : Nat → Bool)
    {fd channel : Nat} (present : objects fd = some (objectCode 2 channel)) :
    descriptorAccess objects ordinary fd = true := by
  simp only [descriptorAccess, present, child_endpoint_access]

theorem descriptor_ordinary_access {objects : Nat → Option Nat} (ordinary : Nat → Bool)
    {fd identity : Nat} (present : objects fd = some (objectCode 0 identity)) :
    descriptorAccess objects ordinary fd = ordinary fd := by
  simp [descriptorAccess, present, objectAccess, objectCode]

theorem loaded_child_endpoint {objects : Nat → Option Nat}
    {cloexec ordinaryRead ordinaryWrite : Nat → Bool} {state : State}
    {fd : UInt32} {channel : Nat} {flag : Bool}
    (loaded : loadedHandles objects cloexec (descriptorAccess objects ordinaryRead)
      (descriptorAccess objects ordinaryWrite) state)
    (physical : binding objects cloexec fd.toNat (objectCode 2 channel) flag) :
    state.handles fd = some ⟨objectCode 2 channel, true, true, flag⟩ := by
  have result := loaded_binding loaded physical
  rw [descriptor_endpoint_access ordinaryRead physical.1,
    descriptor_endpoint_access ordinaryWrite physical.1] at result
  exact result

theorem loaded_ordinary {objects : Nat → Option Nat}
    {cloexec ordinaryRead ordinaryWrite : Nat → Bool} {state : State}
    {fd : UInt32} {identity : Nat} {flag : Bool}
    (loaded : loadedHandles objects cloexec (descriptorAccess objects ordinaryRead)
      (descriptorAccess objects ordinaryWrite) state)
    (physical : binding objects cloexec fd.toNat (objectCode 0 identity) flag) :
    state.handles fd = some
      ⟨objectCode 0 identity, ordinaryRead fd.toNat, ordinaryWrite fd.toNat, flag⟩ := by
  have result := loaded_binding loaded physical
  rw [descriptor_ordinary_access ordinaryRead physical.1,
    descriptor_ordinary_access ordinaryWrite physical.1] at result
  exact result

-- §FS-entry.inputs: The caller proves presence; preparation supplies ordinary access modes.
theorem loaded_prepared_sources {objects : Nat → Option Nat}
    {cloexec ordinaryRead ordinaryWrite : Nat → Bool} {state : State} (p : Inputs)
    (input output errors channel : Nat) (inputFlag outputFlag errorsFlag failureFlag : Bool)
    (loaded : loadedHandles objects cloexec (descriptorAccess objects ordinaryRead)
      (descriptorAccess objects ordinaryWrite) state)
    (inputBinding : binding objects cloexec p.input.toNat (objectCode 0 input) inputFlag)
    (outputBinding : binding objects cloexec p.output.toNat (objectCode 0 output) outputFlag)
    (errorsBinding : binding objects cloexec p.errors.toNat (objectCode 0 errors) errorsFlag)
    (failureBinding : binding objects cloexec p.failure.toNat (objectCode 2 channel) failureFlag)
    (inputRead : ordinaryRead p.input.toNat = true) (inputWrite : ordinaryWrite p.input.toNat = false)
    (outputRead : ordinaryRead p.output.toNat = false) (outputWrite : ordinaryWrite p.output.toNat = true)
    (errorsRead : ordinaryRead p.errors.toNat = false) (errorsWrite : ordinaryWrite p.errors.toNat = true) :
    PreparedSources p state := by
  have first := loaded_ordinary loaded inputBinding
  have second := loaded_ordinary loaded outputBinding
  have third := loaded_ordinary loaded errorsBinding
  have fourth := loaded_child_endpoint loaded failureBinding
  rw [inputRead, inputWrite] at first
  rw [outputRead, outputWrite] at second
  rw [errorsRead, errorsWrite] at third
  exact ⟨_, _, _, _, ⟨first, second, third, fourth⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

end PhysicalHandoff

-- §FS-entry.image: Successful entry retains the supplied objects, with all three slots present.
def ImageStdio (p : Inputs) (initial : State) (image : Image) : Prop :=
  ∃ input output errors failure, SourceBindings p initial input output errors failure ∧
    SourceClasses input output errors failure ∧
    image.state.handles 0 = some { input with cloexec := false } ∧
    image.state.handles 1 = some { output with cloexec := false } ∧
    image.state.handles 2 = some { errors with cloexec := false } ∧
    image.state.handles 3 = none

-- §AR-application-verification.authority: Preparation supplies these named inputs.
def PreparedWorkspace (fs : Filesystem) (p : Inputs) (initial : State)
    (objects : Nat → LeanCageM3.Ref) (expected : LeanCageM3.Processes) : Prop :=
  p.uid = expected.uid ∧
  objects (fs.rootObject initial.root initial.cwd p.root) = expected.root ∧
  expected.filter = LeanCageM3.Filter.bytes.data.toList ∧
  (∀ fd ∈ [p.input, p.output, p.errors], ∀ handle,
    initial.handles fd = some handle → workspaceHandle objects handle ∈ expected.grants) ∧
  PreparedSources p initial

def PreparedContext (context : ProcessContext) (expected : LeanCageM3.Processes) : Prop :=
  context.owner = expected.run ∧ context.scope = expected.run ∧
    context.namespaceId = expected.namespaceId

-- §AR-application-verification.authority: Preparation names the physical cgroup's run.
def physicalProcessContext (generation run : UInt64) (groups : Nat → LeanCageM3.RunId)
    (context : CallerPhysical.Context) : ProcessContext :=
  ⟨generation, run, (context.cgroup.map groups).getD 0, context.namespaceId.toUInt64⟩

theorem physical_context_prepared (generation : UInt64) (groups : Nat → LeanCageM3.RunId)
    (context : CallerPhysical.Context) (expected : LeanCageM3.Processes) (group namespaceId : Nat)
    (placed : context.cgroup = some group) (space : context.namespaceId = namespaceId)
    (groupMeaning : groups group = expected.run)
    (namespaceMeaning : namespaceId.toUInt64 = expected.namespaceId) :
    PreparedContext (physicalProcessContext generation expected.run groups context) expected := by
  exact ⟨rfl, by simp [physicalProcessContext, placed, groupMeaning],
    by simpa only [physicalProcessContext, space] using namespaceMeaning⟩

theorem image_has_supplied_stdio {fs : Filesystem} {p : Inputs} {initial : State} {image : Image}
    (entry : ImageRestricted fs p initial image) (sources : PreparedSources p initial) :
    ImageStdio p initial image := by
  obtain ⟨input, output, errors, failure, bindings, classes⟩ := sources
  have handles := entry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨input, output, errors, failure, bindings, classes, ?_, ?_, ?_, ?_⟩
  · simpa [bindings.1] using handles 0
  · simpa [bindings.2.1] using handles 1
  · simpa [bindings.2.2.1] using handles 2
  · simpa using handles 3

theorem image_workspace_credentials {fs : Filesystem} {p : Inputs} {initial : State}
    {image : Image} (entry : ImageRestricted fs p initial image) :
    workspaceCredentials image.state = LeanCageM3.workspaceCredentials p.uid := by
  rcases entry with ⟨_, _, _, uid, gid, groups, effective, permitted, inheritable,
    bounding, ambient, _⟩
  simp [workspaceCredentials, LeanCageM3.workspaceCredentials, uid, gid, IDs.leased,
    groups, effective, permitted, inheritable, bounding, ambient]

theorem image_workspace_handles {fs : Filesystem} {p : Inputs} {initial : State}
    {image : Image} (entry : ImageRestricted fs p initial image)
    (objects : Nat → LeanCageM3.Ref) (grants : List LeanCageM3.Handle)
    (prepared : ∀ fd ∈ [p.input, p.output, p.errors], ∀ handle,
      initial.handles fd = some handle → workspaceHandle objects handle ∈ grants) :
    ∀ fd handle, image.state.handles fd = some handle → workspaceHandle objects handle ∈ grants := by
  rcases entry with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, handles⟩
  intro fd handle present
  rw [handles fd] at present
  split at present
  · cases source : initial.handles p.input with
    | none => simp [source] at present
    | some original =>
      simp only [source, Option.map_some, Option.some.injEq] at present
      cases present
      exact prepared p.input (by simp) original source
  · split at present
    · cases source : initial.handles p.output with
      | none => simp [source] at present
      | some original =>
        simp only [source, Option.map_some, Option.some.injEq] at present
        cases present
        exact prepared p.output (by simp) original source
    · split at present
      · cases source : initial.handles p.errors with
        | none => simp [source] at present
        | some original =>
          simp only [source, Option.map_some, Option.some.injEq] at present
          cases present
          exact prepared p.errors (by simp) original source
      · contradiction

-- §AR-application-verification.admission: Physical entry supplies task safety.
theorem image_establishes_workspace_task {fs : Filesystem} {p : Inputs} {initial : State}
    {image : Image} (entry : ImageRestricted fs p initial image)
    (objects : Nat → LeanCageM3.Ref) (expected : LeanCageM3.Processes)
    (context : ProcessContext) (prepared : PreparedWorkspace fs p initial objects expected)
    (scope : PreparedContext context expected) :
    LeanCageM3.taskSafe expected (workspaceTask objects context image) := by
  have credentials := image_workspace_credentials entry
  have allowed := image_workspace_handles entry objects expected.grants prepared.2.2.2.1
  rcases entry with ⟨_, _, _, _, _, _, _, _, _, _, _, _, nnp, filter, _, _, root, _⟩
  refine ⟨scope.1, scope.2.1, ?_, ?_, scope.2.2, nnp, ?_, ?_⟩
  · change workspaceCredentials image.state = _
    rw [credentials, prepared.1]
  · change objects image.state.root = expected.root
    rw [root]
    exact prepared.2.1
  · change (image.state.filters.headD .empty).data.toList = expected.filter
    rw [filter, prepared.2.2.1]
    rfl
  · intro handle present
    change handle ∈ ([0, 1, 2] : List UInt32).filterMap
      (fun fd => (image.state.handles fd).map (workspaceHandle objects)) at present
    obtain ⟨fd, _, mapped⟩ := List.mem_filterMap.mp present
    cases source : image.state.handles fd with
    | none => simp [source] at mapped
    | some original =>
      simp only [source, Option.map_some, Option.some.injEq] at mapped
      subst handle
      exact allowed fd original source

-- §AR-entry.acceptance: This consumer uses actual worker control, origins and successful exec.
-- Native caller provenance and prepared-object producers must discharge the named interfaces.
theorem production_workspace_entry {fs : Filesystem} (platform : PrimitiveContract fs)
    (runtime : OriginContract platform) (execution : ExecContract) (execControl : TracerControl)
    (args : List String) (initial current : State) (image : Image)
    (kernelWidth : initial.boundingCaps &&& 18446741874686296064 = 0)
    (objects : Nat → LeanCageM3.Ref) (expected : LeanCageM3.Processes) (context : ProcessContext)
    (prepared : ∀ p, Worker.parse args = some p → PreparedWorkspace fs p initial objects expected)
    (scope : PreparedContext context expected)
    {trace : List (Request × Reply)} {request : Request} {controls : List TracerControl}
    (control : Startup.AtExec (Worker.startup false args) trace request)
    (clean : initial.filters = [])
    (tracer : ∀ selected ∈ controls, selected.nonSubstituting)
    (effects : TracedReturns runtime initial trace controls current)
    (safeExec : execControl.nonSubstituting)
    (replaced : execution.replaced execControl current request image) :
    ∃ p, ParsedHandoff args p ∧ ImageRestricted fs p initial image ∧ ImageStdio p initial image ∧
      LeanCageM3.taskSafe expected (workspaceTask objects context image) := by
  obtain ⟨p, parsed, production, admission⟩ := startup_at_exec false args control
  have entry := admission_image_state platform execution execControl p (Worker.production_mode p production)
    initial current image kernelWidth admission
    (production_kernel_from_clean platform runtime args initial current control clean tracer effects) safeExec replaced
  exact ⟨p, worker_parse_exact args p parsed, entry,
    image_has_supplied_stdio entry (prepared p parsed).2.2.2.2,
    image_establishes_workspace_task entry objects expected context (prepared p parsed) scope⟩

-- §AR-entry.caller.values: The native certificate names the original values and text bytes.
def NativeInputValues (p : Inputs) (uid input output errors failure : Nat)
    (mode root fault : List UInt8) (argv : List (List UInt8)) : Prop :=
  p.uid.toNat = uid ∧ p.input.toNat = input ∧ p.output.toNat = output ∧
    p.errors.toNat = errors ∧ p.failure.toNat = failure ∧
    p.root.toUTF8.data.toList = root ∧ p.fault.toUTF8.data.toList = fault ∧
    p.argv.toList.map (·.toUTF8.data.toList) = argv ∧
    p.preflight = (mode == "check".toUTF8.data.toList)

theorem native_parser_input_values (args : List String) (p : Inputs)
    (uid input output errors failure : Nat) (mode root fault : List UInt8)
    (argv : List (List UInt8))
    (native : ArgumentMeaning.nativeValues uid input output errors failure mode root fault argv
      (args.map (·.toUTF8.data.toList)))
    (parsed : Worker.parse args = some p) :
    NativeInputValues p uid input output errors failure mode root fault argv := by
  obtain ⟨selectedMode, supported, preflight, u, i, o, e, f, selected, r, t, a⟩ :=
    worker_native_values args p uid input output errors failure mode root fault argv native parsed
  refine ⟨u, i, o, e, f, r, t, a, ?_⟩
  rw [← selected, preflight]
  rcases supported with rfl | rfl <;> rfl

-- §FS-entry.check: Workload entry identifies the original run bytes, rather than check bytes.
theorem workload_native_run_mode (args : List String)
    (uid input output errors failure : Nat) (mode root fault : List UInt8)
    (argv : List (List UInt8))
    (native : ArgumentMeaning.nativeValues uid input output errors failure mode root fault argv
      (args.map (·.toUTF8.data.toList)))
    {trace : List (Request × Reply)} {target : Request}
    (control : Startup.AtExec (Worker.startup false args) trace target) :
    mode = ([114, 117, 110] : List UInt8) := by
  obtain ⟨p, parsed, _, actual⟩ := startup_at_exec false args control
  have noCheck := (admission_at_exec p actual).2.2.2
  obtain ⟨selectedMode, supported, preflight, _, _, _, _, _, selected, _, _, _⟩ :=
    worker_native_values args p uid input output errors failure mode root fault argv native parsed
  rcases supported with rfl | rfl
  · exact selected.symm
  · simp only [beq_self_eq_true] at preflight
    rw [noCheck] at preflight
    contradiction

-- §AR-application-verification.admission: The task consumer retains actual C handoff values.
theorem production_workspace_entry_from_native {fs : Filesystem} (platform : PrimitiveContract fs)
    (runtime : OriginContract platform) (execution : ExecContract) (execControl : TracerControl)
    (args : List String) (initial current : State) (image : Image)
    (kernelWidth : initial.boundingCaps &&& 18446741874686296064 = 0)
    (objects : Nat → LeanCageM3.Ref) (expected : LeanCageM3.Processes) (context : ProcessContext)
    (prepared : ∀ p, Worker.parse args = some p → PreparedWorkspace fs p initial objects expected)
    (scope : PreparedContext context expected)
    (uid input output errors failure : Nat) (mode root fault : List UInt8) (argv : List (List UInt8))
    (native : ArgumentMeaning.nativeValues uid input output errors failure mode root fault argv
      (args.map (·.toUTF8.data.toList)))
    {trace : List (Request × Reply)} {request : Request} {controls : List TracerControl}
    (control : Startup.AtExec (Worker.startup false args) trace request)
    (clean : initial.filters = [])
    (tracer : ∀ selected ∈ controls, selected.nonSubstituting)
    (effects : TracedReturns runtime initial trace controls current)
    (safeExec : execControl.nonSubstituting)
    (replaced : execution.replaced execControl current request image) :
    ∃ p, ParsedHandoff args p ∧
      NativeInputValues p uid input output errors failure mode root fault argv ∧
      ImageRestricted fs p initial image ∧ ImageStdio p initial image ∧
      LeanCageM3.taskSafe expected (workspaceTask objects context image) := by
  obtain ⟨p, parsed, production, admission⟩ := startup_at_exec false args control
  have entry := admission_image_state platform execution execControl p (Worker.production_mode p production)
    initial current image kernelWidth admission
    (production_kernel_from_clean platform runtime args initial current control clean tracer effects) safeExec replaced
  exact ⟨p, worker_parse_exact args p parsed,
    native_parser_input_values args p uid input output errors failure mode root fault argv native parsed,
    entry, image_has_supplied_stdio entry (prepared p parsed).2.2.2.2,
    image_establishes_workspace_task entry objects expected context (prepared p parsed) scope⟩

-- §AR-entry.acceptance: Actual source values and caller execution supply entry provenance.
theorem production_workspace_admission {fs : Filesystem} (platform : PrimitiveContract fs)
    (runtime : OriginContract platform) (lineageRuntime : CallerLineageContract) (execution : ExecContract) (execControl : TracerControl)
    (args : List String) (initial current : State) (image : Image)
    (kernelWidth : initial.boundingCaps &&& 18446741874686296064 = 0)
    (objects : Nat → LeanCageM3.Ref) (expected : LeanCageM3.Processes) (context : ProcessContext)
    (prepared : ∀ p, Worker.parse args = some p → PreparedWorkspace fs p initial objects expected)
    (scope : PreparedContext context expected)
    (uid input output errors failure : Nat) (mode root fault : List UInt8) (argv : List (List UInt8))
    (native : ArgumentMeaning.nativeValues uid input output errors failure mode root fault argv
      (args.map (·.toUTF8.data.toList)))
    (owner child : ProcessIdentity) (history : List Nat)
    {trace : List (Request × Reply)} {request : Request} {controls : List TracerControl}
    (control : Startup.AtExec (Worker.startup false args) trace request)
    (source : CallerRequestsAllowed history)
    (lineage : CallerLineage lineageRuntime child initial.filters)
    (effects : CallerReturns runtime owner child history initial trace controls current)
    (execSnapshot : CallerControlUse owner child history execControl)
    (replaced : execution.replaced execControl current request image) :
    ∃ p, ParsedHandoff args p ∧ NativeInputValues p uid input output errors failure mode root fault argv ∧
      ImageRestricted fs p initial image ∧ ImageStdio p initial image ∧
      LeanCageM3.taskSafe expected (workspaceTask objects context image) := by
  have safeExec := caller_control_non_substituting source execSnapshot
  obtain ⟨p, parsed, production, admission⟩ := startup_at_exec false args control
  have kernel := production_kernel_from_caller platform runtime lineageRuntime args initial current
    owner child history control source lineage effects
  have entry := admission_image_state platform execution execControl p (Worker.production_mode p production)
    initial current image kernelWidth admission kernel safeExec replaced
  exact ⟨p, worker_parse_exact args p parsed,
    native_parser_input_values args p uid input output errors failure mode root fault argv native parsed,
    entry, image_has_supplied_stdio entry (prepared p parsed).2.2.2.2,
    image_establishes_workspace_task entry objects expected context (prepared p parsed) scope⟩

-- §AR-entry.acceptance: Start at actual worker exec, including its owned metadata reads.
theorem production_workspace_startup {fs : Filesystem} (platform : PrimitiveContract fs)
    (runtime : OriginContract platform) (lineageRuntime : CallerLineageContract)
    (metadata : MetadataFrame.PrimitiveContract) (metadataRuntime : MetadataOriginContract metadata)
    (execution : ExecContract)
    (execControl : TracerControl) (args : List String) (initial current : State) (image : Image)
    (kernelWidth : initial.boundingCaps &&& 18446741874686296064 = 0)
    (objects : Nat → LeanCageM3.Ref) (expected : LeanCageM3.Processes) (context : ProcessContext)
    (prepared : ∀ p, Worker.parse args = some p → PreparedWorkspace fs p initial objects expected)
    (scope : PreparedContext context expected)
    (uid input output errors failure : Nat) (mode root fault : List UInt8) (argv : List (List UInt8))
    (native : ArgumentMeaning.nativeValues uid input output errors failure mode root fault argv
      (args.map (·.toUTF8.data.toList)))
    (owner child : ProcessIdentity) (history : List Nat)
    {trace : List (Request × Reply)} {request : Request}
    (run : Startup.AtExecState (CallerMetadata metadataRuntime owner child history)
      (CallerNative runtime owner child history) (Worker.startup false args) initial trace request current)
    (source : CallerRequestsAllowed history)
    (lineage : CallerLineage lineageRuntime child initial.filters)
    (execSnapshot : CallerControlUse owner child history execControl)
    (replaced : execution.replaced execControl current request image) :
    ∃ p, ParsedHandoff args p ∧ NativeInputValues p uid input output errors failure mode root fault argv ∧
      ImageRestricted fs p initial image ∧ ImageStdio p initial image ∧
      LeanCageM3.taskSafe expected (workspaceTask objects context image) := by
  have actual := metadata_phase_from_caller (worker_metadata_phase false args) run source
    (caller_lineage_clean lineage)
  obtain ⟨controls, effects⟩ := startup_state_caller_returns actual
  exact production_workspace_admission platform runtime lineageRuntime execution execControl
    args initial current image kernelWidth objects expected context prepared scope
    uid input output errors failure mode root fault argv native owner child history
    (startup_state_control run) source lineage effects execSnapshot replaced

-- §AR-entry.acceptance: Caller observations are produced by the same ordered execution.
theorem production_recorded_image {fs : Filesystem} (platform : PrimitiveContract fs)
    (runtime : OriginContract platform) (lineageRuntime : CallerLineageContract)
    (metadataPlatform : MetadataFrame.PrimitiveContract)
    (metadataRuntime : MetadataOriginContract metadataPlatform) (execution : ExecContract)
    {mayTrace : ProcessIdentity → Prop} {owner child task : ProcessIdentity}
    {supervisor : CallerPhysical.SupervisorContract mayTrace owner child}
    {nativeRuntime : CallerPhysical.NativeContract runtime mayTrace owner child}
    {metadata : CallerPhysical.MetadataContract metadataRuntime mayTrace owner child}
    {history : List Nat} {start namespaceId : Nat} {cgroup : Option Nat}
    {ticks : List CallerPhysical.Tick} {last imageContext : CallerPhysical.Context}
    {before final : CallerPhysical.Point} {trace : List (Request × Reply)} {request : Request}
    (imageRuntime : CallerPhysical.ImageContract execution owner child start ticks)
    (args : List String) (image : Image)
    (kernelWidth : before.state.boundingCaps &&& 18446741874686296064 = 0)
    (uid input output errors failure : Nat) (mode root fault : List UInt8) (argv : List (List UInt8))
    (values : ArgumentMeaning.nativeValues uid input output errors failure mode root fault argv
      (args.map (·.toUTF8.data.toList)))
    (prepared : ∀ p, Worker.parse args = some p → PreparedSources p before.state)
    (journal : CallerPhysical.Journal mayTrace owner child history
      (CallerPhysical.born namespaceId cgroup) ticks last)
    (supervisorRecording : CallerPhysical.SupervisorRecording supervisor start ticks)
    (nativeRecording : CallerPhysical.NativeRecording nativeRuntime start ticks)
    (metadataRecording : CallerPhysical.MetadataRecording metadataRuntime owner child metadata.returned start ticks)
    {ancestorTask : ProcessIdentity} {ancestorInstalled installed : List ByteArray}
    {labels : List LineageLabel}
    (ancestor : CallerLineage lineageRuntime ancestorTask ancestorInstalled)
    (inherited : CallerPhysical.LineageEffects lineageRuntime ancestorTask ancestorInstalled labels child installed)
    (labelsChecked : CallerLabelsAllowed labels)
    (observed : CallerPhysical.StackObservation installed before.state)
    (source : CallerRequestsAllowed history)
    (run : CallerPhysical.StartupExecution supervisor nativeRuntime metadata
      (Worker.startup false args) before trace request final)
    (replaced : imageRuntime.replaced final.position final.context final.state request task imageContext image) :
    ∃ p, Worker.parse args = some p ∧ ParsedHandoff args p ∧
      NativeInputValues p uid input output errors failure mode root fault argv ∧
      ImageRestricted fs p before.state image ∧ ImageStdio p before.state image ∧ task = child ∧
      imageContext.namespaceId = final.context.namespaceId ∧ imageContext.cgroup = final.context.cgroup := by
  have lineage := CallerPhysical.source_observed_startup_lineage ancestor inherited labelsChecked observed
  have actual := CallerPhysical.startup_execution_erase journal supervisorRecording nativeRecording metadataRecording run
  have kernel := production_kernel_from_actual_startup platform runtime lineageRuntime
    metadataPlatform metadataRuntime args before.state final.state owner child history actual source lineage
  have snapshot := CallerPhysical.journal_snapshot journal
    (imageRuntime.occurrence _ _ _ _ _ _ _ replaced)
  have safe := caller_control_non_substituting source snapshot
  obtain ⟨p, parsed, production, control⟩ := startup_at_exec false args (startup_state_control actual)
  have imageState := admission_image_state platform execution (CallerPhysical.control owner child final.context)
    p (Worker.production_mode p production) before.state final.state image kernelWidth control kernel safe
    (imageRuntime.effect _ _ _ _ _ _ _ replaced)
  exact ⟨p, parsed, worker_parse_exact args p parsed,
    native_parser_input_values args p uid input output errors failure mode root fault argv values parsed,
    imageState, image_has_supplied_stdio imageState (prepared p parsed),
    imageRuntime.identity _ _ _ _ _ _ _ replaced,
    imageRuntime.scope _ _ _ _ _ _ _ replaced⟩

-- §AR-application-verification.admission: The maintained task invariant consumes actual entry.
theorem production_recorded_workspace {fs : Filesystem} (platform : PrimitiveContract fs)
    (runtime : OriginContract platform) (lineageRuntime : CallerLineageContract)
    (metadataPlatform : MetadataFrame.PrimitiveContract)
    (metadataRuntime : MetadataOriginContract metadataPlatform) (execution : ExecContract)
    {mayTrace : ProcessIdentity → Prop} {owner child task : ProcessIdentity}
    {supervisor : CallerPhysical.SupervisorContract mayTrace owner child}
    {nativeRuntime : CallerPhysical.NativeContract runtime mayTrace owner child}
    {metadata : CallerPhysical.MetadataContract metadataRuntime mayTrace owner child}
    {history : List Nat} {start namespaceId : Nat} {cgroup : Option Nat}
    {ticks : List CallerPhysical.Tick} {last imageContext : CallerPhysical.Context}
    {before final : CallerPhysical.Point} {trace : List (Request × Reply)} {request : Request}
    (imageRuntime : CallerPhysical.ImageContract execution owner child start ticks)
    (args : List String) (image : Image)
    (kernelWidth : before.state.boundingCaps &&& 18446741874686296064 = 0)
    (uid input output errors failure : Nat) (mode root fault : List UInt8) (argv : List (List UInt8))
    (values : ArgumentMeaning.nativeValues uid input output errors failure mode root fault argv
      (args.map (·.toUTF8.data.toList)))
    (objects : Nat → LeanCageM3.Ref) (expected : LeanCageM3.Processes)
    (generation : UInt64) (groups : Nat → LeanCageM3.RunId) (group : Nat)
    (prepared : ∀ p, Worker.parse args = some p → PreparedWorkspace fs p before.state objects expected)
    (groupMeaning : groups group = expected.run)
    (namespaceMeaning : namespaceId.toUInt64 = expected.namespaceId)
    (journal : CallerPhysical.Journal mayTrace owner child history
      (CallerPhysical.born namespaceId cgroup) ticks last)
    (supervisorRecording : CallerPhysical.SupervisorRecording supervisor start ticks)
    (nativeRecording : CallerPhysical.NativeRecording nativeRuntime start ticks)
    (metadataRecording : CallerPhysical.MetadataRecording metadataRuntime owner child metadata.returned start ticks)
    {ancestorTask : ProcessIdentity} {ancestorInstalled installed : List ByteArray}
    {labels : List LineageLabel}
    (ancestor : CallerLineage lineageRuntime ancestorTask ancestorInstalled)
    (inherited : CallerPhysical.LineageEffects lineageRuntime ancestorTask ancestorInstalled labels child installed)
    (labelsChecked : CallerLabelsAllowed labels)
    (observed : CallerPhysical.StackObservation installed before.state)
    (source : CallerRequestsAllowed history)
    (run : CallerPhysical.StartupExecution supervisor nativeRuntime metadata
      (Worker.startup false args) before trace request final)
    {closeOffset : Nat} {closed : CallerPhysical.Tick}
    (closeOccurrence : CallerPhysical.TickAt ticks closeOffset closed)
    (assigned : closed.after.cgroup = some group)
    (ordered : start + closeOffset < final.position)
    {ownedOffset : Nat} {ownedTick : CallerPhysical.Tick}
    (ownedOccurrence : CallerPhysical.TickAt ticks ownedOffset ownedTick)
    (ownedTracer : ownedTick.before.tracer = some owner) (beforeClose : ownedOffset ≤ closeOffset)
    (cgroupFiles : Nat → Option Nat)
    (placements : ∀ offset tick, start + closeOffset + 1 ≤ start + offset →
      start + offset < final.position → CallerPhysical.TickAt ticks offset tick →
        CallerPhysical.PlacementRecording cgroupFiles tick)
    (sourceTables : ∀ offset tick, start + closeOffset + 1 ≤ start + offset →
      start + offset < final.position → CallerPhysical.TickAt ticks offset tick →
        ∀ reference, tick.source = some reference → CallerPhysical.WriteOutsideCgroup cgroupFiles tick)
    (otherTables : ∀ offset tick, start + closeOffset + 1 ≤ start + offset →
      start + offset < final.position → CallerPhysical.TickAt ticks offset tick →
        ∀ actor, actor ≠ owner → actor ≠ child → CallerPhysical.CgroupAbsent cgroupFiles tick actor)
    (replaced : imageRuntime.replaced final.position final.context final.state request task imageContext image) :
    ∃ p, ParsedHandoff args p ∧ NativeInputValues p uid input output errors failure mode root fault argv ∧
      ImageRestricted fs p before.state image ∧ ImageStdio p before.state image ∧ task = child ∧
      imageContext.cgroup = some group ∧ imageContext.namespaceId = namespaceId ∧
      LeanCageM3.taskSafe expected (workspaceTask objects
        (physicalProcessContext generation expected.run groups imageContext) image) := by
  obtain ⟨p, parser, parsed, inputs, entry, stdio, identity, _, _⟩ :=
    production_recorded_image platform runtime lineageRuntime metadataPlatform metadataRuntime execution
      imageRuntime args image kernelWidth uid input output errors failure mode root fault argv values
      (fun p selected => (prepared p selected).2.2.2.2) journal supervisorRecording nativeRecording
      metadataRecording ancestor inherited labelsChecked observed source run replaced
  have lineage := CallerPhysical.source_observed_startup_lineage ancestor inherited labelsChecked observed
  have beforeOwned := CallerPhysical.startup_precedes_owned_observation args journal supervisorRecording
    nativeRecording metadataRecording source (caller_lineage_clean lineage) run ownedOccurrence ownedTracer
  have workerStarted : before.position ≤ start + closeOffset + 1 := by omega
  have stable := CallerPhysical.startup_no_cgroup_placement args journal supervisorRecording
    nativeRecording metadataRecording run source (caller_lineage_clean lineage) cgroupFiles workerStarted
    placements sourceTables otherTables
  have scope := CallerPhysical.recorded_image_observed_scope imageRuntime journal
    closeOccurrence assigned ordered stable replaced
  have context := physical_context_prepared generation groups imageContext expected group namespaceId
    scope.1 scope.2 groupMeaning namespaceMeaning
  exact ⟨p, parsed, inputs, entry, stdio, identity, scope.1, scope.2,
    image_establishes_workspace_task entry objects expected
      (physicalProcessContext generation expected.run groups imageContext) (prepared p parser) context⟩

-- §AR-entry.caller.receipt: Pass the actual release read to the proved source producer.
theorem production_source_workspace {fs : Filesystem} (platform : PrimitiveContract fs)
    (runtime : OriginContract platform) (lineageRuntime : CallerLineageContract)
    (metadataPlatform : MetadataFrame.PrimitiveContract)
    (metadataRuntime : MetadataOriginContract metadataPlatform) (execution : ExecContract)
    {mayTrace : ProcessIdentity → Prop} {owner child task : ProcessIdentity}
    {supervisor : CallerPhysical.SupervisorContract mayTrace owner child}
    {nativeRuntime : CallerPhysical.NativeContract runtime mayTrace owner child}
    {metadata : CallerPhysical.MetadataContract metadataRuntime mayTrace owner child}
    {history : List Nat} {start namespaceId : Nat} {cgroup : Option Nat}
    {ticks : List CallerPhysical.Tick} {last imageContext : CallerPhysical.Context}
    {before final : CallerPhysical.Point} {trace : List (Request × Reply)} {request : Request}
    (imageRuntime : CallerPhysical.ImageContract execution owner child start ticks)
    (args : List String) (image : Image)
    (kernelWidth : before.state.boundingCaps &&& 18446741874686296064 = 0)
    (uid input output errors failure : Nat) (mode root fault : List UInt8) (argv : List (List UInt8))
    (values : ArgumentMeaning.nativeValues uid input output errors failure mode root fault argv
      (args.map (·.toUTF8.data.toList)))
    (objects : Nat → LeanCageM3.Ref) (expected : LeanCageM3.Processes)
    (generation : UInt64) (groups : Nat → LeanCageM3.RunId) (group : Nat)
    (prepared : ∀ p, Worker.parse args = some p → PreparedWorkspace fs p before.state objects expected)
    (groupMeaning : groups group = expected.run)
    (namespaceMeaning : namespaceId.toUInt64 = expected.namespaceId)
    (journal : CallerPhysical.Journal mayTrace owner child history
      (CallerPhysical.born namespaceId cgroup) ticks last)
    (supervisorRecording : CallerPhysical.SupervisorRecording supervisor start ticks)
    (nativeRecording : CallerPhysical.NativeRecording nativeRuntime start ticks)
    (metadataRecording : CallerPhysical.MetadataRecording metadataRuntime owner child metadata.returned start ticks)
    {ancestorTask : ProcessIdentity} {ancestorInstalled installed : List ByteArray}
    {labels : List LineageLabel}
    (ancestor : CallerLineage lineageRuntime ancestorTask ancestorInstalled)
    (inherited : CallerPhysical.LineageEffects lineageRuntime ancestorTask ancestorInstalled labels child installed)
    (labelsChecked : CallerLabelsAllowed labels)
    (observed : CallerPhysical.StackObservation installed before.state)
    (source : CallerRequestsAllowed history)
    (run : CallerPhysical.StartupExecution supervisor nativeRuntime metadata
      (Worker.startup false args) before trace request final)
    (failureFits : failure ≤ 2147483647) (endpoint : Nat)
    (failureObject : ∀ p, Worker.parse args = some p →
      ∃ handle, before.state.handles p.failure = some handle ∧ handle.object = endpoint)
    (cgroupFiles : Nat → Option Nat)
    (caller : SourceScopeProducer owner child start final.position ticks group failure endpoint cgroupFiles)
    (replaced : imageRuntime.replaced final.position final.context final.state request task imageContext image) :
    ∃ p, ParsedHandoff args p ∧ NativeInputValues p uid input output errors failure mode root fault argv ∧
      ImageRestricted fs p before.state image ∧ ImageStdio p before.state image ∧ task = child ∧
      imageContext.cgroup = some group ∧ imageContext.namespaceId = namespaceId ∧
      LeanCageM3.taskSafe expected (workspaceTask objects
        (physicalProcessContext generation expected.run groups imageContext) image) := by
  have lineage := CallerPhysical.source_observed_startup_lineage ancestor inherited labelsChecked observed
  obtain ⟨p, parser, normal, ordinal, selected, state, next, changed, leading, trailing, actions, controls,
    traceCut, operation, suffix, handles, readBeforeExec, trailingWrites⟩ :=
    CallerPhysical.startup_execution_release args journal supervisorRecording nativeRecording metadataRecording
      source (caller_lineage_clean lineage) run
  have inputs := native_parser_input_values args p uid input output errors failure mode root fault argv values parser
  have failureValue : p.failure.toNat = failure := inputs.2.2.2.2.1
  have descriptorFits : (releaseCommand p).request.a.toNat ≤ 2147483647 := by
    simpa [releaseCommand, cmd, failureValue] using failureFits
  have safe := caller_control_non_substituting source
    (CallerPhysical.native_recorded_snapshot journal nativeRecording operation).2
  obtain ⟨readOffset, readTick, readPosition, readAt, readBefore, readAfter, table, socket⟩ :=
    CallerPhysical.native_recorded_read nativeRecording operation safe rfl rfl descriptorFits
  have readSocket : readTick.socket = .read child failure 1 [165] := by
    simpa [releaseCommand, cmd, failureValue] using socket
  obtain ⟨handle, failurePresent, failureEndpoint⟩ := failureObject p parser
  have atRead : state.handles p.failure = some handle := by rw [handles]; exact failurePresent
  have width : p.failure.toNat ≤ 2147483647 := by simpa [failureValue] using failureFits
  obtain ⟨objectsAt, flagsAt⟩ := table p.failure width
  have bound : CallerPhysical.TickBinding readTick (CallerPhysical.taskKey child) failure endpoint handle.cloexec := by
    constructor
    · simpa [atRead, failureValue, failureEndpoint] using objectsAt
    · simpa [atRead, failureValue] using flagsAt
  obtain ⟨scope, placements, sourceTables, otherTables⟩ := caller readOffset readTick handle.cloexec readAt readSocket bound
  have ordered : start + scope.closeOffset < final.position := by
    have a := scope.closeBeforeResume
    have b := scope.resumeBeforeSend
    have c := scope.sendBeforeRead
    omega
  exact production_recorded_workspace platform runtime lineageRuntime metadataPlatform metadataRuntime execution
    imageRuntime args image kernelWidth uid input output errors failure mode root fault argv values objects expected
    generation groups group prepared groupMeaning namespaceMeaning journal supervisorRecording nativeRecording
    metadataRecording ancestor inherited labelsChecked observed source run scope.closeAt scope.assigned ordered
    scope.optionsAt scope.tracer scope.optionsBeforeClose cgroupFiles placements sourceTables otherTables replaced

end LeanCage.Entry
