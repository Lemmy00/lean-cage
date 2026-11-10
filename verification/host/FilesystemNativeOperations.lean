import FilesystemActors

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: Native identities name process lifetimes, including one caller
-- across several independent requests.
abbrev NativeToken := Nat

structure NativeReferences where
  handles : UInt64 → Option Handle
  closeOnExec : UInt64 → Bool
  workingDirectory : ObjectId

def NativeReferences.project (references : NativeReferences) (shared : World) : World :=
  { shared with
    handles := references.handles
    closeOnExec := references.closeOnExec
    workingDirectory := references.workingDirectory }

def NativeReferences.engineSlot (fd : UInt64) : Bool := fd == 0 || fd == 1 || fd == 3

def NativeReferences.rawProjection (references : NativeReferences) : NativeReferences :=
  { handles := fun fd => if engineSlot fd then references.handles fd else none
    closeOnExec := fun fd => if engineSlot fd then references.closeOnExec fd else false
    workingDirectory := references.workingDirectory }

def NativeReferences.supportProjection (references : NativeReferences) : NativeReferences :=
  { handles := fun fd => if engineSlot fd then none else references.handles fd
    closeOnExec := fun fd => if engineSlot fd then false else references.closeOnExec fd
    workingDirectory := references.workingDirectory }

-- §AR-host-boundary.primitives: The raw view does not erase stderr or SDK aliases from the
-- actual exec table. Both projections are snapshots at this one transfer point.
theorem native_reference_partition (references : NativeReferences) (fd : UInt64) :
    ((references.rawProjection.handles fd).orElse
      (fun _ => references.supportProjection.handles fd)) = references.handles fd := by
  unfold NativeReferences.rawProjection NativeReferences.supportProjection
  cases selected : NativeReferences.engineSlot fd <;> simp [selected]

-- §AR-host-boundary.primitives: These are single raw operations, never callback summaries.
inductive NativeVfsOperation where
  | adapted (request : Request)
  | linkAt (sourceDirectory : UInt64) (source : ByteArray)
      (targetDirectory : UInt64) (target : ByteArray) (flags : UInt64)
  | symlinkAt (contents : ByteArray) (directory : UInt64) (name : ByteArray)
  | renameAt (sourceDirectory : UInt64) (source : ByteArray)
      (targetDirectory : UInt64) (target : ByteArray) (flags : UInt64)
  | chdir (path : ByteArray)
  | fchdir (fd : UInt64)
  | fchmod (fd mode : UInt64)
  | fchown (fd owner group : UInt64)
  | truncate (fd extent : UInt64)
  | seek (fd offset whence : UInt64)
  | pwrite (fd : UInt64) (bytes : ByteArray) (extent offset : UInt64)
  | setInodeFlags (fd flags : UInt64)
  | setEncryptionPolicy (fd : UInt64) (policy : ByteArray)
  | setAttribute (fd : UInt64) (name value : ByteArray) (flags : UInt64)
  | removeAttribute (fd : UInt64) (name : ByteArray)
  | fchmodAt (directory : UInt64) (path : ByteArray) (mode flags : UInt64)
  | fchownAt (directory : UInt64) (path : ByteArray) (owner group flags : UInt64)

inductive NativeFileAction where
  | close (fd : UInt64)
  | duplicate (source target : UInt64)
  | closeFrom (minimum : UInt64)
  | open (fd : UInt64) (path : ByteArray) (flags mode : UInt64)
  | chdir (path : ByteArray)
  | fchdir (fd : UInt64)

structure NativeSpawnAttributes where
  flags : UInt64
  processGroup : UInt64
  signalMask : List Nat
  signalDefault : List Nat
  schedulingPolicy : UInt64
  schedulingPriority : UInt64

-- §AR-host-boundary.primitives: Spawn copies actual initialized actions and raw argument bytes.
structure NativeSpawn where
  path : ByteArray
  arguments : List ByteArray
  environment : List ByteArray
  actions : List NativeFileAction
  attributes : NativeSpawnAttributes

structure NativeExec where
  path : ByteArray
  arguments : List ByteArray
  environment : List ByteArray

structure NativePollEntry where
  descriptor : UInt64
  events : UInt64

-- §AR-host-boundary.primitives: Integer words retain the actual ABI bit patterns. A send owns
-- its requested initialized span; receive bytes belong to the operation's observed product.
inductive NativeOperation where
  | vfs (operation : NativeVfsOperation)
  | socketPair (domain socketType protocol : UInt64)
  | fcntl (fd command argument : UInt64)
  | duplicate (source target flags : UInt64)
  | send (fd : UInt64) (bytes : ByteArray) (extent flags : UInt64)
  | receive (fd extent flags : UInt64)
  | shutdown (fd how : UInt64)
  | poll (entries : List NativePollEntry) (timeout : UInt64)
  | clock (clockId : UInt64)
  | signal (pid signal : UInt64)
  | waitPid (pid options : UInt64)
  | spawn (arguments : NativeSpawn)
  | exec (arguments : NativeExec)

-- §FS-host-boundary.ownership: Kernel effects are recorded even when the reply is lost or
-- reports an error. Creation and image replacement are different products.
inductive NativeProduct where
  | none
  | socketPair (first second : UInt64)
  | sent (bytes : ByteArray)
  | received (bytes : ByteArray)
  | created (child : NativeToken)
  | executed (image : ObjectId)
  | reaped (child : NativeToken) (status : UInt64)

structure NativeBirth where
  parent : NativeToken
  arguments : NativeSpawn
  pid : Nat

structure NativeExecution where
  image : ObjectId
  arguments : NativeExec
  references : NativeReferences

structure NativeHandoff where
  token : NativeToken
  execution : NativeExecution

-- §FS-host-boundary.ownership: Native births are separate from source-owned Lean child births.
structure NativeProcesses where
  allocated : NativeToken → Bool
  births : NativeToken → Option NativeBirth
  executions : NativeToken → Option NativeExecution
  references : NativeToken → Option NativeReferences
  nativeOwned : NativeToken → Bool := fun _ => true
  handoffs : ActorId → Option NativeHandoff := fun _ => none
  retiring : NativeToken → Option RetirementResources := fun _ => none

def NativeReferences.resources (references : NativeReferences) : RetirementResources :=
  ⟨references.handles, references.closeOnExec, some references.workingDirectory, references.workingDirectory⟩

-- §FS-host-boundary.ownership: Retirement ends native source execution immediately, while
-- retaining each actual surviving FD/CWD until its later observed kernel release.
def NativeProcesses.retire (processes : NativeProcesses) (token : NativeToken)
    (resources : RetirementResources) : NativeProcesses :=
  { processes with
    references := fun query => if query = token then none else processes.references query
    nativeOwned := fun query => if query = token then false else processes.nativeOwned query
    retiring := fun query => if query = token then some resources else processes.retiring query }

def NativeProcesses.transfer (processes : NativeProcesses) (actor : ActorId)
    (execution : NativeExecution) : NativeProcesses :=
  { processes with
    references := fun query => if query = actor then none else processes.references query
    nativeOwned := fun query => if query = actor then false else processes.nativeOwned query
    handoffs := fun query => if query = actor then some ⟨actor, execution⟩ else processes.handoffs query }

-- §AR-host-boundary.primitives: An adapted call uses the same single-operation kernel law;
-- other native operations retain their own actual libc/kernel relation.
structure NativePrimitive (kernel : Contract) where
  observed : NativeToken → Credentials → NativeProcesses → World → NativeOperation →
    Option Reply → NativeProduct → NativeProcesses → World → Prop
  pathTarget : NativeToken → Credentials → NativeProcesses → World → NativeOperation →
    Option Reply → NativeProduct → NativeProcesses → World → ObjectId → Prop
  interpreted : ∀ token caller processes next before after request reply product,
    observed token caller processes before (.vfs (.adapted request)) reply product next after →
    kernel.step before request reply after
  allocation_monotone : ∀ token caller processes next before after operation reply product child,
    observed token caller processes before operation reply product next after →
    processes.allocated child = true → next.allocated child = true
  birth_frame : ∀ token caller processes next before after operation reply product child birth,
    observed token caller processes before operation reply product next after →
    processes.births child = some birth → next.births child = some birth
  fresh_source : ∀ token caller processes next before after operation reply product child,
    observed token caller processes before operation reply product next after →
    processes.allocated child = false → next.allocated child = true →
    ∃ arguments birth, operation = .spawn arguments ∧ product = .created child ∧
      next.births child = some birth ∧ birth.parent = token ∧ birth.arguments = arguments
  created : ∀ token caller processes next before after operation reply child,
    observed token caller processes before operation reply (.created child) next after →
    processes.allocated child = false ∧ next.allocated child = true
  execution_origin : ∀ token caller processes next before after operation reply product query execution,
    observed token caller processes before operation reply product next after →
    next.executions query = some execution →
    processes.executions query = some execution ∨ (query = token ∧ product = .executed execution.image)
  other_references : ∀ token caller processes next before after operation reply product query,
    observed token caller processes before operation reply product next after →
    query ≠ token → processes.allocated query = true →
    next.references query = processes.references query ∨ next.references query = none
  native_ownership : ∀ token caller processes next before after operation reply product,
    observed token caller processes before operation reply product next after →
    next.nativeOwned = processes.nativeOwned
  transfers : ∀ token caller processes next before after operation reply product,
    observed token caller processes before operation reply product next after →
    next.handoffs = processes.handoffs
  exec_source : ∀ token caller processes next before after operation reply product image,
    observed token caller processes before operation reply product next after →
    product = .executed image →
    ∃ arguments execution, operation = .exec arguments ∧
      next.executions token = some execution ∧ execution.image = image ∧
      execution.arguments = arguments ∧ next.references token = some execution.references

-- §AR-host-boundary.primitives: This row projects the parent native process's own table and CWD.
structure NativeCallAt {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (primitive : NativePrimitive kernel)
    (tick : ActorTick runtime) (before after : NativeProcesses) where
  token : NativeToken
  caller : Credentials
  beforeReferences : NativeReferences
  afterReferences : NativeReferences
  active : before.allocated token = true
  owned : before.nativeOwned token = true
  inputTable : before.references token = some beforeReferences
  outputTable : after.references token = some afterReferences
  operation : NativeOperation
  reply : Option Reply
  product : NativeProduct
  action : tick.action = .foreign caller
  native : primitive.observed token caller before
    (beforeReferences.project tick.before.shared) operation reply product after
    (afterReferences.project tick.after.shared)

-- §AR-host-boundary.primitives: A pathname setter has its own resolved target on this exact
-- operation row. The directory operand is a lookup base, not the metadata target.
inductive NativePathSetter : NativeOperation → Prop where
  | chmod (directory : UInt64) (path : ByteArray) (mode flags : UInt64) :
      NativePathSetter (.vfs (.fchmodAt directory path mode flags))
  | chown (directory : UInt64) (path : ByteArray) (owner group flags : UInt64) :
      NativePathSetter (.vfs (.fchownAt directory path owner group flags))

def NativeCallPathTarget {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {primitive : NativePrimitive kernel}
    {tick : ActorTick runtime} {before after : NativeProcesses}
    (call : NativeCallAt primitive tick before after) (object : ObjectId) : Prop :=
  NativePathSetter call.operation ∧ primitive.pathTarget call.token call.caller before
    (call.beforeReferences.project tick.before.shared) call.operation call.reply call.product after
    (call.afterReferences.project tick.after.shared) object

-- §FS-host-boundary.caller: Launch consumes the same still-current exec snapshot, transfers raw
-- custody, and retains the complementary inherited SDK snapshot without claiming future frames.
structure NativeHandoffAt {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (tick : ActorTick runtime) (before : NativeProcesses) where
  actor : ActorId
  execution : NativeExecution
  active : before.allocated actor = true
  owned : before.nativeOwned actor = true
  recorded : before.executions actor = some execution
  current : before.references actor = some execution.references
  action : tick.action = .launch actor execution.references.rawProjection.handles
    execution.references.rawProjection.closeOnExec execution.references.workingDirectory

-- §AR-host-boundary.primitives: This binds one actual native process teardown observation
-- outside the frozen normal-call ABI. Birth/exec history stays immutable and partial refs stay.
structure NativeRetirementAt {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (tick : ActorTick runtime) (before after : NativeProcesses) where
  token : NativeToken
  observation : EngineRetirement
  beforeResources : RetirementResources
  afterResources : RetirementResources
  active : before.allocated token = true
  input : (∃ references, before.nativeOwned token = true ∧ before.references token = some references ∧
      beforeResources = references.resources) ∨ before.retiring token = some beforeResources
  action : tick.action = .nativeRetire token observation beforeResources afterResources
  next : after = before.retire token afterResources

theorem native_adapted_kernel_step {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {primitive : NativePrimitive kernel}
    {tick : ActorTick runtime} {before after : NativeProcesses}
    (call : NativeCallAt primitive tick before after) {request : Request}
    (operation : call.operation = .vfs (.adapted request)) :
    kernel.step (call.beforeReferences.project tick.before.shared) request call.reply
      (call.afterReferences.project tick.after.shared) := by
  have observed := call.native
  rw [operation] at observed
  exact primitive.interpreted _ _ _ _ _ _ _ _ _ observed

end LeanCage.Host.Kernel
