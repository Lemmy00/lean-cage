import LeanCage.Linux.Launch

namespace LeanCageM2

-- §FS-lifecycle.model: Operation IDs are the versioned executable helper protocol.
inductive Operation where
  | bootstrap | namespaces | handles | credentials | validate | nnp | filter | exec
  deriving DecidableEq, Repr

def plan : List Operation :=
  [.bootstrap, .namespaces, .handles, .credentials, .validate, .nnp, .filter, .exec]

def Operation.wire : Operation → String
  | .bootstrap => "1" | .namespaces => "2" | .handles => "3" | .credentials => "4"
  | .validate => "5" | .nnp => "6" | .filter => "7" | .exec => "8"

def wirePlan : String := String.join (plan.map Operation.wire)

-- §AR-lifecycle.design: The executable emits a plan only after actual M1 decoding succeeds.
def preparePlan (abi : LeanCage.Linux.Filter.Abi) (bytes : ByteArray) :
    Except LeanCage.Linux.Filter.DecodeError (List Operation) :=
  match LeanCage.Linux.Filter.decode abi bytes with
  | .error error => .error error
  | .ok _ => .ok plan

-- §FS-lifecycle.setup: Linux IDs are 32-bit; capability sets cover the 64-bit v3 ABI.
structure Credentials where
  realUid : UInt32 := 0
  effectiveUid : UInt32 := 0
  savedUid : UInt32 := 0
  fsUid : UInt32 := 0
  realGid : UInt32 := 0
  effectiveGid : UInt32 := 0
  savedGid : UInt32 := 0
  fsGid : UInt32 := 0
  groups : List UInt32 := []
  effectiveCaps : UInt64 := 0
  permittedCaps : UInt64 := 0
  inheritableCaps : UInt64 := 0
  ambientCaps : UInt64 := 0
  boundingCaps : UInt64 := 0
  deriving DecidableEq, Repr

def restrictedCredentials : Credentials :=
  { realUid := 65534, effectiveUid := 65534, savedUid := 65534, fsUid := 65534,
    realGid := 65534, effectiveGid := 65534, savedGid := 65534, fsGid := 65534 }

-- §FS-lifecycle.resources: Historical startup state; guests may later install their own handlers.
structure StartupSignals where
  blocked : UInt64
  customHandlers : UInt64
  threads : UInt32
  deriving DecidableEq, Repr

def cleanStartup : StartupSignals := ⟨0, 0, 1⟩

-- §FS-lifecycle.resources: Birth identities are logical tokens, not recyclable machine PIDs.
structure Member where
  identity : Nat
  scope : UInt64
  credentials : Credentials
  nnp : Bool
  filtered : Bool
  deriving DecidableEq, Repr

def Member.Secure (member : Member) : Prop :=
  member.scope = 1 ∧ member.credentials = restrictedCredentials ∧ member.nnp = true ∧ member.filtered = true

inductive Phase where
  | setup (pending : Operation) | running | failed | done
  deriving DecidableEq, Repr

inductive Entry where
  | no | yes | unknown
  deriving DecidableEq, Repr

-- §FS-lifecycle.supervision: Unknown knowledge is independent of actual historical entry.
structure State where
  phase : Phase := .setup .bootstrap
  completed : List Operation := []
  imageSealed : Bool := false
  privateInputs : Bool := false
  signalsReset : Bool := false
  namespaced : Bool := false
  handlesClosed : Bool := false
  credentialsDropped : Bool := false
  credentials : Option Credentials := none
  startupSignals : Option StartupSignals := none
  decoded : Bool := false
  nnp : Bool := false
  filtered : Bool := false
  entered : Bool := false
  knowledge : Entry := .no
  cancelRequested : Bool := false
  extinct : Bool := false
  members : List Member := []
  issued : List Nat := []
  owned : List UInt64 := []
  released : List UInt64 := []
  deriving DecidableEq, Repr

def initial : State := {}

-- §FS-lifecycle.cancellation: Requests remain possible until cancellation actually takes effect.
def request (s : State) : Option Operation :=
  match s.phase with
  | .setup op => some op
  | _ => none

-- §FS-lifecycle.model: Each successful effect establishes its own receipt; failures do not.
def nextOperation : Operation → Option Operation
  | .bootstrap => some .namespaces | .namespaces => some .handles
  | .handles => some .credentials | .credentials => some .validate
  | .validate => some .nnp | .nnp => some .filter | .filter => some .exec | .exec => none

def setupPrefix : Operation → List Operation
  | .bootstrap => [] | .namespaces => [.bootstrap]
  | .handles => [.bootstrap, .namespaces]
  | .credentials => [.bootstrap, .namespaces, .handles]
  | .validate => [.bootstrap, .namespaces, .handles, .credentials]
  | .nnp => [.bootstrap, .namespaces, .handles, .credentials, .validate]
  | .filter => [.bootstrap, .namespaces, .handles, .credentials, .validate, .nnp]
  | .exec => [.bootstrap, .namespaces, .handles, .credentials, .validate, .nnp, .filter]

def ready (s : State) : Bool :=
  s.imageSealed && s.privateInputs && s.signalsReset &&
    s.namespaced && s.handlesClosed && s.credentialsDropped && s.decoded && s.nnp && s.filtered &&
    decide (s.credentials = some restrictedCredentials) && decide (s.startupSignals = some cleanStartup)

def establish (s : State) (op : Operation) : State :=
  let t := { s with
    completed := s.completed ++ [op]
    phase := ((nextOperation op).map Phase.setup).getD .running }
  match op with
  | .bootstrap => { t with
      imageSealed := true
      privateInputs := true
      signalsReset := true
      startupSignals := some cleanStartup
      owned := [10, 11, 12] }
  | .namespaces => { t with namespaced := true }
  | .handles => { t with handlesClosed := true }
  | .credentials => { t with
      credentialsDropped := true
      credentials := some restrictedCredentials }
  | .validate => { t with decoded := true }
  | .nnp => { t with nnp := true }
  | .filter => { t with filtered := true }
  | .exec => { t with
      entered := true
      knowledge := .yes
      members := [⟨2, 1, s.credentials.getD {}, s.nnp, s.filtered⟩]
      issued := [2] }

-- §FS-lifecycle.model: Hostile actions include fork/exec/session escape and outside signals.
inductive Event where
  | ok (operation : Operation)
  | setupError (operation : Operation) (errno : LeanCage.Launch.Errno)
  | interrupted (operation : Operation)
  | contractViolation (operation : Operation)
  | fork (parent : Member) (freshIdentity : Nat)
  | reexec (member : Member)
  | exit (member : Member)
  | escapeAttempt (member : Member)
  | signalOutside (member : Member)
  | cancelRequest
  | reportLost
  | namespaceDeath
  | release (handle : UInt64)
  deriving DecidableEq, Repr

-- §FS-lifecycle.model: The executable controller checks the real decoder at validation.
def step (abi : LeanCage.Linux.Filter.Abi) (bytes : ByteArray)
    (s : State) (event : Event) : Option State :=
  match event with
  | .ok op =>
    if s.phase != .setup op then none
    else if op == .validate && !(LeanCage.Linux.Filter.decode abi bytes).isOk then none
    else if op == .exec && !ready s then none
    else some (establish s op)
  | .setupError op _ | .interrupted op | .contractViolation op =>
    if s.phase == .setup op then some { s with phase := .failed } else none
  | .fork parent fresh =>
    if s.phase == .running && parent ∈ s.members &&
        !s.issued.contains fresh then
      some { s with
        members := { parent with identity := fresh } :: s.members
        issued := fresh :: s.issued }
    else none
  | .reexec member | .escapeAttempt member | .signalOutside member =>
    if s.phase == .running && member ∈ s.members then some s else none
  | .exit member =>
    if s.phase == .running && member ∈ s.members then
      some { s with members := s.members.filter fun p => p.identity != member.identity }
    else none
  | .cancelRequest =>
    if s.phase == .done then none else some { s with cancelRequested := true }
  | .reportLost => some { s with knowledge := .unknown }
  | .namespaceDeath => some { s with phase := .done, extinct := true, members := [] }
  | .release handle =>
    if handle ∈ s.owned ∧ s.phase = .done then
      some { s with owned := s.owned.filter (· != handle), released := handle :: s.released }
    else none

-- §FS-lifecycle.model: Reachability includes arbitrary ordering of all admitted observations.
inductive Reaches (abi : LeanCage.Linux.Filter.Abi) (bytes : ByteArray) : State → Prop where
  | initial : Reaches abi bytes initial
  | next {s t : State} {event : Event} :
    Reaches abi bytes s → step abi bytes s event = some t → Reaches abi bytes t

def replay (abi : LeanCage.Linux.Filter.Abi) (bytes : ByteArray) :
    State → List Event → Option State
  | s, [] => some s
  | s, e :: es => (step abi bytes s e).bind fun t => replay abi bytes t es

-- §FS-lifecycle.model: This invariant is independent of the transition function.
def Safe (s : State) : Prop :=
  (s.entered = true → ready s = true) ∧
  (∀ member ∈ s.members, member.Secure) ∧
  (s.extinct = true → s.phase = .done ∧ s.members = [])

def Ordered (s : State) : Prop :=
  (∀ op, s.phase = .setup op → s.completed = setupPrefix op) ∧
  (s.entered = true → s.completed = plan)

-- §FS-lifecycle.model: Actual decoder acceptance is separate from namespace/credential effects.
def Decoded (abi : LeanCage.Linux.Filter.Abi) (bytes : ByteArray) (s : State) : Prop :=
  s.decoded = true → (LeanCage.Linux.Filter.decode abi bytes).isOk = true

-- §FS-lifecycle.model: Project exactly the successful portable M1 segment, versioning exec ABI.
def m1Events : Operation → LeanCage.Launch.Trace
  | .validate => [.validationAccepted] | .nnp => [.noNewPrivilegesSet]
  | .filter => [.filterInstalled] | .exec => [.execAttempted, .execSucceeded] | _ => []

end LeanCageM2
