import LeanCageEntry.Script

namespace LeanCage.Entry

-- §FS-entry.inputs: These identities describe open objects, independently of slot numbers.
structure Handle where
  object : Nat
  readable : Bool
  writable : Bool
  cloexec : Bool
  deriving DecidableEq, Repr

structure IDs where
  real : UInt32
  effective : UInt32
  saved : UInt32
  filesystem : UInt32
  deriving DecidableEq, Repr

def IDs.leased (uid : UInt32) : IDs := ⟨uid, uid, uid, uid⟩

-- §AR-entry.effects: -1 preserves an ID slot; the filesystem ID follows the effective ID.
def IDs.reassign (old : IDs) (real effective saved : UInt32) : IDs :=
  let keep (previous requested : UInt32) := if requested = 4294967295 then previous else requested
  if (real == 4294967295 || real == old.real) &&
      (effective == 4294967295 || (effective == old.effective && effective == old.filesystem)) &&
      (saved == 4294967295 || saved == old.saved) then old
  else
    let effective := keep old.effective effective
    ⟨keep old.real real, effective, keep old.saved saved, effective⟩

theorem IDs.reassign_all (old : IDs) (uid : UInt32) (specified : uid ≠ 4294967295) :
    old.reassign uid uid uid = IDs.leased uid := by
  simp only [reassign, beq_eq_false_iff_ne.mpr specified, Bool.false_or]
  split
  · rename_i same
    simp only [Bool.and_eq_true, beq_iff_eq] at same
    cases old
    rcases same with ⟨⟨rfl, rfl, rfl⟩, rfl⟩
    rfl
  · simp [leased]

-- §FS-entry.inputs: Successful path resolution supplies object identities, not pathname labels.
structure Filesystem where
  rootObject : Nat → Nat → String → Nat
  workingObject : Nat → Nat → String → Nat

-- §FS-linux-product.proofs.entry: Setup changes actual value-carrying authority state.
structure State where
  handles : UInt32 → Option Handle
  uid : IDs
  gid : IDs
  groups : List UInt32
  effectiveCaps : UInt64
  permittedCaps : UInt64
  inheritableCaps : UInt64
  boundingCaps : UInt64
  ambientCaps : UInt64
  securebits : UInt64
  dumpable : UInt64
  noNewPrivs : Bool
  filters : List ByteArray
  defaults : UInt64
  signalMask : UInt64
  root : Nat
  cwd : Nat
  umask : UInt64

def duplicate (fds : UInt32 → Option Handle) (source target : UInt32) (cloexec : Bool) :
    UInt32 → Option Handle :=
  fun fd => if fd = target then (fds source).map (fun h => { h with cloexec }) else fds fd

-- §AR-entry.effects: Single-operation state updates, not an assumed successful sandbox.
def update (fs : Filesystem) (request : Request) (state : State) : State :=
  match request.op with
  | .signalMask => { state with signalMask := request.a &&& 18446744073709289215 }
  | .signalDefault => { state with defaults := state.defaults ||| (1 <<< (request.a - 1)) }
  | .dup2 => { state with
      handles := if request.a.toUInt32 = request.b.toUInt32 then state.handles else
        duplicate state.handles request.a.toUInt32 request.b.toUInt32 false }
  | .dup3 => { state with
      handles := duplicate state.handles request.a.toUInt32 request.b.toUInt32 (request.c &&& 524288 != 0) }
  | .closeRange => { state with handles := (fun fd =>
      if request.a.toUInt32 ≤ fd && fd ≤ request.b.toUInt32 then
        (if request.c &&& 4 != 0 then (state.handles fd).map (fun h => { h with cloexec := true })
         else none)
      else state.handles fd) }
  | .chroot => { state with root := fs.rootObject state.root state.cwd request.text }
  | .chdir => { state with cwd := fs.workingObject state.root state.cwd request.text }
  | .umask => { state with umask := request.a &&& 511 }
  | .setgroups => { state with groups := [] }
  | .setresgid => { state with
      gid := state.gid.reassign request.a.toUInt32 request.b.toUInt32 request.c.toUInt32 }
  | .setresuid => { state with
      uid := state.uid.reassign request.a.toUInt32 request.b.toUInt32 request.c.toUInt32 }
  | .capset => { state with
      effectiveCaps := 0, permittedCaps := 0, inheritableCaps := 0, ambientCaps := 0 }
  | .prctl =>
    if request.a == 28 then { state with securebits := request.b }
    else if request.a == 24 then { state with boundingCaps := state.boundingCaps &&& ~~~(1 <<< request.b) }
    else if request.a == 47 && request.b == 4 then { state with ambientCaps := 0 }
    else if request.a == 4 then { state with dumpable := request.b }
    else if request.a == 38 then { state with noNewPrivs := request.b == 1 }
    else state
  | .filter => { state with filters := state.filters ++ [request.data] }
  | _ => state

def after (fs : Filesystem) (commands : List Command) (initial : State) : State :=
  commands.foldl (fun state command => update fs command.request state) initial

-- §AR-entry.effects: Credential operations may also change dumpability and capability sets.
-- The proof must allow those changes until later concrete operations establish their final values.
def collateral (request : Request) (before observed : State) : State :=
  match request.op with
  | .setresuid => { before with
      dumpable := observed.dumpable
      effectiveCaps := observed.effectiveCaps
      permittedCaps := observed.permittedCaps
      inheritableCaps := observed.inheritableCaps
      ambientCaps := observed.ambientCaps }
  | .setresgid | .capset => { before with dumpable := observed.dumpable }
  | _ => before

def advance (fs : Filesystem) (request : Request) (before observed : State) : State :=
  update fs request (collateral request before observed)

def afterObserved (fs : Filesystem) : List Command → State → (Nat → State) → State
  | [], state, _ => state
  | command :: rest, state, observed =>
    afterObserved fs rest (advance fs command.request state (observed 0)) (fun n => observed (n + 1))

-- §FS-entry.control: Independent value predicate at the workload syscall, before image replacement.
def Restricted (fs : Filesystem) (p : Inputs) (initial current : State) : Prop :=
  current.uid = IDs.leased p.uid ∧ current.gid = IDs.leased p.uid ∧ current.groups = [] ∧
  current.effectiveCaps = 0 ∧ current.permittedCaps = 0 ∧ current.inheritableCaps = 0 ∧
  current.boundingCaps = 0 ∧ current.ambientCaps = 0 ∧ current.securebits = 15 ∧
  current.dumpable = 0 ∧ current.noNewPrivs = true ∧ current.filters = [LeanCageM3.Filter.bytes] ∧
  current.defaults ||| 262400 = 18446744073709551615 ∧ current.signalMask = 0 ∧
  current.root = fs.rootObject initial.root initial.cwd p.root ∧
  current.cwd = fs.workingObject (fs.rootObject initial.root initial.cwd p.root) initial.cwd "/workspace" ∧
  current.umask = 63 ∧
  (∀ fd : UInt32, current.handles fd =
    if fd = 0 then (initial.handles p.input).map (fun h => { h with cloexec := false })
    else if fd = 1 then (initial.handles p.output).map (fun h => { h with cloexec := false })
    else if fd = 2 then (initial.handles p.errors).map (fun h => { h with cloexec := false })
    else if fd = 3 then (initial.handles p.failure).map (fun h => { h with cloexec := true })
    else none)

end LeanCage.Entry
