import FilesystemNativeEffects
import FilesystemNativeChannelRows

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

abbrev Bytes := List UInt8

inductive Side where
  | caller | engine
  deriving DecidableEq, Repr

def Side.peer : Side → Side
  | .caller => .engine
  | .engine => .caller

structure Pair where
  caller : ObjectId
  engine : ObjectId
  separate : caller ≠ engine

def Pair.endpoint (pair : Pair) : Side → ObjectId
  | .caller => pair.caller
  | .engine => pair.engine

-- §AR-host-boundary.primitives: Queues are a positional physical observation,
-- separate from the filesystem world whose fields do not contain socket data.
structure State where
  incoming : Side → Bytes
  writeClosed : Side → Bool

def State.empty : State := ⟨fun _ => [], fun _ => false⟩

def State.setIncoming (state : State) (side : Side) (bytes : Bytes) : State :=
  { state with incoming := fun query => if query = side then bytes else state.incoming query }

def State.enqueue (state : State) (sender : Side) (bytes : Bytes) : State :=
  state.setIncoming sender.peer (state.incoming sender.peer ++ bytes)

def State.closeWrite (state : State) (side : Side) : State :=
  { state with writeClosed := fun query => if query = side then true else state.writeClosed query }

-- §FS-host-boundary.ownership: Committed bytes are distinct from optional SDK
-- observations. Discard and half-close remain explicit physical effects.
inductive Action where
  | born
  | write (sender : Side) (bytes : Bytes)
  | read (receiver : Side) (bytes : Bytes)
  | discard (receiver : Side) (bytes : Bytes)
  | closeWrite (sender : Side)
  | eof (receiver : Side)
  | quiet

inductive Step : Option State → Action → Option State → Prop where
  | born : Step none .born (some .empty)
  | write (state : State) (sender : Side) (bytes : Bytes)
      (writable : state.writeClosed sender = false) :
      Step (some state) (.write sender bytes) (some (state.enqueue sender bytes))
  | read (state : State) (receiver : Side) (bytes rest : Bytes)
      (contents : state.incoming receiver = bytes ++ rest) :
      Step (some state) (.read receiver bytes) (some (state.setIncoming receiver rest))
  | discard (state : State) (receiver : Side) (bytes rest : Bytes)
      (contents : state.incoming receiver = bytes ++ rest) :
      Step (some state) (.discard receiver bytes) (some (state.setIncoming receiver rest))
  | closeWrite (state : State) (sender : Side) :
      Step (some state) (.closeWrite sender) (some (state.closeWrite sender))
  | eof (state : State) (receiver : Side) (empty : state.incoming receiver = [])
      (closed : state.writeClosed receiver.peer = true) :
      Step (some state) (.eof receiver) (some state)
  | quiet (state : Option State) : Step state .quiet state

def written (receiver : Side) : Action → Bytes
  | .write sender bytes => if sender.peer = receiver then bytes else []
  | _ => []

def received (receiver : Side) : Action → Bytes
  | .read actual bytes => if actual = receiver then bytes else []
  | _ => []

def preservesUnread (receiver : Side) : Action → Prop
  | .discard actual _ => actual ≠ receiver
  | _ => True

inductive Run : State → List Action → State → Prop where
  | nil (state : State) : Run state [] state
  | cons {before middle after : State} {action : Action} {actions : List Action}
      (head : Step (some before) action (some middle)) (tail : Run middle actions after) :
      Run before (action :: actions) after

inductive Steps : Option State → List Action → Option State → Prop where
  | nil (state : Option State) : Steps state [] state
  | cons {before middle after : Option State} {action : Action} {actions : List Action}
      (head : Step before action middle) (tail : Steps middle actions after) :
      Steps before (action :: actions) after

theorem step_live {before : State} {action : Action} {after : Option State}
    (step : Step (some before) action after) : ∃ final, after = some final := by
  cases step <;> exact ⟨_, rfl⟩

theorem steps_live {before : State} {actions : List Action} {after : Option State}
    (steps : Steps (some before) actions after) : ∃ final, after = some final ∧ Run before actions final := by
  generalize original : some before = initial at steps
  induction steps generalizing before with
  | nil state =>
    cases original
    exact ⟨before, rfl, .nil _⟩
  | cons head tail ih =>
    cases original
    obtain ⟨middle, rfl⟩ := step_live head
    obtain ⟨final, actual, run⟩ := ih rfl
    exact ⟨final, actual, .cons head run⟩

theorem step_balance {before after : State} {action : Action} (receiver : Side)
    (step : Step (some before) action (some after)) (retained : preservesUnread receiver action) :
    before.incoming receiver ++ written receiver action =
      received receiver action ++ after.incoming receiver := by
  cases step with
  | write state sender bytes writable =>
    cases receiver <;> cases sender <;>
      simp [written, received, State.enqueue, State.setIncoming, Side.peer]
  | read state actual bytes rest contents =>
    cases receiver <;> cases actual <;>
      simp_all [written, received, State.setIncoming]
  | discard state actual bytes rest contents =>
    cases receiver <;> cases actual <;>
      simp_all [preservesUnread, written, received, State.setIncoming]
  | closeWrite state sender => simp [written, received, State.closeWrite]
  | eof state actual empty closed => simp [written, received]
  | quiet state => simp [written, received]

-- §FS-host-boundary.caller: Every delivered prefix consists of committed bytes
-- in order; a later missing reply or engine exit cannot rewrite that prefix.
theorem run_balance {before after : State} {actions : List Action} (receiver : Side)
    (run : Run before actions after) (retained : ∀ action ∈ actions, preservesUnread receiver action) :
    before.incoming receiver ++ actions.flatMap (written receiver) =
      actions.flatMap (received receiver) ++ after.incoming receiver := by
  induction run with
  | nil state => simp
  | @cons before middle after action actions head tail ih =>
    have first := step_balance receiver head (retained action (by simp))
    have rest := ih (by intro selected member; exact retained selected (by simp [member]))
    simpa only [List.flatMap_cons, List.append_assoc] using
      (calc
        (before.incoming receiver ++ written receiver action) ++ actions.flatMap (written receiver) =
            (received receiver action ++ middle.incoming receiver) ++ actions.flatMap (written receiver) := by rw [first]
        _ = received receiver action ++ (actions.flatMap (received receiver) ++ after.incoming receiver) := by
          rw [List.append_assoc, rest]
        _ = (received receiver action ++ actions.flatMap (received receiver)) ++ after.incoming receiver := by
          simp only [List.append_assoc])

theorem run_received_prefix {after : State} {actions : List Action} (receiver : Side)
    (run : Run .empty actions after) (retained : ∀ action ∈ actions, preservesUnread receiver action) :
    ∃ pending, actions.flatMap (written receiver) = actions.flatMap (received receiver) ++ pending := by
  exact ⟨after.incoming receiver, by simpa only [State.empty, List.nil_append] using run_balance receiver run retained⟩

-- §FS-host-boundary.ownership: EOF records only a drained, write-closed peer.
-- It does not assert process exit, a status observation, or successful reaping.
theorem eof_observation {before after : State} {receiver : Side}
    (step : Step (some before) (.eof receiver) (some after)) :
    before.incoming receiver = [] ∧ before.writeClosed receiver.peer = true ∧ after = before := by
  cases step with
  | eof state actual empty closed => exact ⟨empty, closed, rfl⟩

-- §AR-host-boundary.interfaces.gateway: Engine ordinals come from the actual
-- lifetime actor's raw source history; native fields come from its source key.
inductive CallKey where
  | engine (actor ordinal : Nat)
  | native (process invocation actions attributes entry : Nat)
  deriving DecidableEq

def nativeKey (source : NativeCode.SourceKey) (entry : Nat) : CallKey :=
  .native source.process source.entryPosition source.actionsLifetime source.attributesLifetime entry

structure WriteDescription where
  sender : Side
  descriptor : UInt64
  object : ObjectId
  description : DescriptionId
  bytes : Bytes

inductive Observation where
  | pending
  | returned (reply : Reply)
  | lost

structure WriteProgress where
  input : WriteDescription
  committed : Nat
  bounded : committed ≤ input.bytes.length
  observation : Observation

def WriteProgress.canCommit (progress : WriteProgress) : Prop :=
  match progress.observation with
  | .returned _ => False
  | .pending | .lost => True

abbrev Ledger := CallKey → Option WriteProgress

def Ledger.set (ledger : Ledger) (key : CallKey) (progress : WriteProgress) : Ledger :=
  fun query => if query = key then some progress else ledger query

structure PhysicalState where
  stream : Option State
  ledger : Ledger

def segment (bytes : Bytes) (first last : Nat) : Bytes := (bytes.drop first).take (last - first)

inductive ProgressEvent where
  | begin (key : CallKey) (input : WriteDescription)
  | commit (key : CallKey) (extent : Nat)
  | returned (key : CallKey) (reply : Reply)
  | lost (key : CallKey)
  | channel (action : Action)

-- §AR-host-boundary.primitives: The physical observer witnesses actual kernel
-- progress. A send may expose several prefixes while its SDK call is pending.
inductive ProgressStep : PhysicalState → ProgressEvent → List Action → PhysicalState → Prop where
  | begin (state : PhysicalState) (key : CallKey) (input : WriteDescription)
      (fresh : state.ledger key = none) :
      ProgressStep state (.begin key input) []
        { state with ledger := state.ledger.set key ⟨input, 0, Nat.zero_le _, .pending⟩ }
  | commit (state : PhysicalState) (key : CallKey) (current : WriteProgress)
      (stream : State) (extent : Nat)
      (selected : state.ledger key = some current) (live : state.stream = some stream)
      (unreturned : current.canCommit)
      (increase : current.committed < extent) (bound : extent ≤ current.input.bytes.length)
      (writable : stream.writeClosed current.input.sender = false) :
      ProgressStep state (.commit key extent) [.write current.input.sender (segment current.input.bytes current.committed extent)]
        { stream := some (stream.enqueue current.input.sender (segment current.input.bytes current.committed extent))
          ledger := state.ledger.set key { current with committed := extent, bounded := bound } }
  | returned (state : PhysicalState) (key : CallKey) (current : WriteProgress) (reply : Reply)
      (selected : state.ledger key = some current)
      (unobserved : current.observation = .pending)
      (count : nativeError reply = false → current.committed = reply.1.toNat) :
      ProgressStep state (.returned key reply) []
        { state with ledger := state.ledger.set key { current with observation := .returned reply } }
  | lost (state : PhysicalState) (key : CallKey) (current : WriteProgress)
      (selected : state.ledger key = some current) (unobserved : current.observation = .pending) :
      ProgressStep state (.lost key) []
        { state with ledger := state.ledger.set key { current with observation := .lost } }
  | channel (state : PhysicalState) (action : Action) (after : Option State)
      (step : Step state.stream action after) (notWrite : ∀ sender bytes, action ≠ .write sender bytes) :
      ProgressStep state (.channel action) [action] { state with stream := after }

theorem progress_stream {before after : PhysicalState} {event : ProgressEvent} {actions : List Action}
    (progress : ProgressStep before event actions after) : Steps before.stream actions after.stream := by
  cases progress with
  | begin => exact .nil _
  | commit key current stream extent selected live unreturned increase bound writable =>
    rw [live]
    exact .cons (.write _ _ _ writable) (.nil _)
  | returned => exact .nil _
  | lost => exact .nil _
  | channel action after step notWrite => exact .cons step (.nil _)

-- §FS-host-boundary.ownership: Observing a reply or losing it never enqueues
-- the same already committed bytes again and never erases queued observations.
theorem observed_stream_unchanged (state : PhysicalState) (key : CallKey) (current : WriteProgress)
    (reply : Reply) :
    ({ state with ledger := state.ledger.set key { current with observation := .returned reply } } : PhysicalState).stream =
      state.stream ∧
    ({ state with ledger := state.ledger.set key { current with observation := .lost } } : PhysicalState).stream =
      state.stream := ⟨rfl, rfl⟩

theorem committed_extent {before after : PhysicalState} {event : ProgressEvent} {actions : List Action}
    (progress : ProgressStep before event actions after) (key : CallKey) (current : WriteProgress)
    (selected : before.ledger key = some current) :
    ∃ final, after.ledger key = some final ∧ final.input = current.input ∧ current.committed ≤ final.committed := by
  cases progress with
  | begin added input fresh =>
    have different : key ≠ added := by intro same; subst added; rw [fresh] at selected; cases selected
    exact ⟨current, by simp only [Ledger.set, ite_eq_right different]; exact selected, rfl, Nat.le_refl _⟩
  | commit added previous stream extent stored live unreturned increase bound writable =>
    by_cases same : key = added
    · subst added
      have identity := Option.some.inj (stored.symm.trans selected)
      subst previous
      exact ⟨{ current with committed := extent, bounded := bound }, by simp [Ledger.set], rfl, Nat.le_of_lt increase⟩
    · exact ⟨current, by simp only [Ledger.set, ite_eq_right same]; exact selected, rfl, Nat.le_refl _⟩
  | returned added previous reply stored unobserved count =>
    by_cases same : key = added
    · subst added
      have identity := Option.some.inj (stored.symm.trans selected)
      subst previous
      exact ⟨{ current with observation := .returned reply }, by simp [Ledger.set], rfl, Nat.le_refl _⟩
    · exact ⟨current, by simp only [Ledger.set, ite_eq_right same]; exact selected, rfl, Nat.le_refl _⟩
  | lost added previous stored unobserved =>
    by_cases same : key = added
    · subst added
      have identity := Option.some.inj (stored.symm.trans selected)
      subst previous
      exact ⟨{ current with observation := .lost }, by simp [Ledger.set], rfl, Nat.le_refl _⟩
    · exact ⟨current, by simp only [Ledger.set, ite_eq_right same]; exact selected, rfl, Nat.le_refl _⟩
  | channel => exact ⟨current, selected, rfl, Nat.le_refl _⟩

end LeanCage.Host.PrivateStreams
