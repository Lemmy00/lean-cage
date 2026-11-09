import WorkerConnection
import CallerState

namespace LeanCage.Entry

-- §FS-entry.image: These are Linux exec updates, separate from application setup.
def execHandles (handles : UInt32 → Option Handle) : UInt32 → Option Handle :=
  fun fd => (handles fd).filter (fun handle => !handle.cloexec)

def execIDs (ids : IDs) : IDs :=
  { ids with saved := ids.effective, filesystem := ids.effective }

def execState (before : State) (dumpable : UInt64) : State :=
  { before with
    handles := execHandles before.handles
    uid := execIDs before.uid
    gid := execIDs before.gid
    effectiveCaps := 0
    permittedCaps := 0
    inheritableCaps := 0
    ambientCaps := 0
    securebits := before.securebits &&& 18446744073709551583
    dumpable }

-- §FS-entry.image: Conditions for the restricted ordinary-exec primitive law.
-- They concern the input of one exec; they do not establish any setup operation.
def execPrerequisites (before : State) : Prop :=
  before.noNewPrivs = true ∧ before.effectiveCaps = 0 ∧ before.permittedCaps = 0 ∧
  before.inheritableCaps = 0 ∧ before.boundingCaps = 0 ∧ before.ambientCaps = 0 ∧
  before.securebits = 15 ∧ before.defaults ||| 262400 = 18446744073709551615

structure Image where
  state : State
  executable : String
  argv : Array String
  environment : ByteArray

-- §AR-entry.effects: Successful replacement is a distinct non-returning primitive outcome.
-- The kernel may select dumpability; this law cannot manufacture a successful replacement.
structure ExecContract where
  replaced : TracerControl → State → Request → Image → Prop
  inheritance : ∀ control before request image,
    replaced control before request image → control.nonSubstituting →
    request.op = .exec → execPrerequisites before →
    image.state = execState before image.state.dumpable ∧
    image.executable = request.text ∧ image.argv = request.args ∧
    image.environment = request.data

-- §FS-entry.image: A successful workload starts without the private setup-failure pipe.
def ImageRestricted (fs : Filesystem) (p : Inputs) (initial : State) (image : Image) : Prop :=
  image.executable = p.argv[0]! ∧ image.argv = p.argv ∧ image.environment = environmentBytes ∧
  image.state.uid = IDs.leased p.uid ∧ image.state.gid = IDs.leased p.uid ∧
  image.state.groups = [] ∧ image.state.effectiveCaps = 0 ∧ image.state.permittedCaps = 0 ∧
  image.state.inheritableCaps = 0 ∧ image.state.boundingCaps = 0 ∧ image.state.ambientCaps = 0 ∧
  image.state.securebits = 15 ∧ image.state.noNewPrivs = true ∧
  image.state.filters = [LeanCageM3.Filter.bytes] ∧
  image.state.defaults ||| 262400 = 18446744073709551615 ∧ image.state.signalMask = 0 ∧
  image.state.root = fs.rootObject initial.root initial.cwd p.root ∧
  image.state.cwd = fs.workingObject (fs.rootObject initial.root initial.cwd p.root)
    initial.cwd "/workspace" ∧ image.state.umask = 63 ∧
  (∀ fd : UInt32, image.state.handles fd =
    if fd = 0 then (initial.handles p.input).map (fun h => { h with cloexec := false })
    else if fd = 1 then (initial.handles p.output).map (fun h => { h with cloexec := false })
    else if fd = 2 then (initial.handles p.errors).map (fun h => { h with cloexec := false })
    else none)

theorem exec_ids_leased (uid : UInt32) : execIDs (IDs.leased uid) = IDs.leased uid := rfl

theorem exec_handles_survive (handle : Option Handle) :
    (handle.map (fun h => { h with cloexec := false })).filter (fun h => !h.cloexec) =
      handle.map (fun h => { h with cloexec := false }) := by
  cases handle <;> rfl

theorem exec_handles_close (handle : Option Handle) :
    (handle.map (fun h => { h with cloexec := true })).filter (fun h => !h.cloexec) = none := by
  cases handle <;> rfl

-- §FS-entry.image: Setup values discharge the input conditions of the exec primitive.
theorem restricted_exec_prerequisites {fs : Filesystem} {p : Inputs} {initial current : State}
    (restricted : Restricted fs p initial current) : execPrerequisites current := by
  rcases restricted with ⟨_, _, _, effective, permitted, inheritable, bounding,
    ambient, securebits, _, nnp, _, defaults, _⟩
  exact ⟨nnp, effective, permitted, inheritable, bounding, ambient, securebits, defaults⟩

theorem restricted_exec_state {fs : Filesystem} {p : Inputs} {initial current : State}
    (restricted : Restricted fs p initial current) (dumpable : UInt64) :
    ImageRestricted fs p initial
      ⟨execState current dumpable, p.argv[0]!, p.argv, environmentBytes⟩ := by
  rcases restricted with ⟨uid, gid, groups, effective, permitted, inheritable, bounding,
    ambient, securebits, _, nnp, filters, defaults, signals, root, cwd, permissions, handles⟩
  refine ⟨rfl, rfl, rfl, ?_, ?_, groups, rfl, rfl, rfl, bounding, rfl, ?_, nnp,
    filters, defaults, signals, root, cwd, permissions, ?_⟩
  · change execIDs current.uid = _
    rw [uid, exec_ids_leased]
  · change execIDs current.gid = _
    rw [gid, exec_ids_leased]
  · change current.securebits &&& 18446744073709551583 = 15
    rw [securebits]
    decide
  · intro fd
    change execHandles current.handles fd = _
    simp only [execHandles, handles]
    split
    · exact exec_handles_survive _
    · split
      · exact exec_handles_survive _
      · split
        · exact exec_handles_survive _
        · split
          · exact exec_handles_close _
          · rfl

-- §FS-entry.image: The full body guarantee includes successful replacement and exact arguments.
theorem admission_image_state {fs : Filesystem} (platform : PrimitiveContract fs)
    (execution : ExecContract) (execControl : TracerControl) (p : Inputs) (normal : p.fault = "normal")
    (initial current : State) (image : Image)
    (kernelWidth : initial.boundingCaps &&& 18446741874686296064 = 0)
    {trace : List (Request × Reply)} {request : Request}
    (control : AtExec (admission p) trace request)
    (effects : KernelTrace platform initial trace current)
    (safeExec : execControl.nonSubstituting)
    (replaced : execution.replaced execControl current request image) :
    ImageRestricted fs p initial image := by
  obtain ⟨restricted, op, text, args, environment⟩ :=
    admission_value_state platform p normal initial current kernelWidth control effects
  obtain ⟨state, path, argv, env⟩ :=
    execution.inheritance execControl current request image replaced safeExec op
      (restricted_exec_prerequisites restricted)
  have established := restricted_exec_state restricted image.state.dumpable
  rcases image with ⟨imageState, imagePath, imageArgv, imageEnv⟩
  dsimp only at state path argv env
  rw [text] at path
  rw [args] at argv
  rw [environment] at env
  cases path
  cases argv
  cases env
  change ImageRestricted fs p initial
    ⟨execState current imageState.dumpable, _, _, _⟩ at established
  rw [← state] at established
  exact established

-- §FS-entry.check: Even a primitive capable of replacement cannot be reached by preflight.
theorem preflight_no_image {p : Inputs} (check : p.preflight = true)
    {trace : List (Request × Reply)} {request : Request} :
    ¬AtExec (admission p) trace request :=
  only_excludes_exec (preflight_no_exec p check)

end LeanCage.Entry
