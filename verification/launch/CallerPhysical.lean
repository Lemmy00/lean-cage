import CallerProvenance

namespace LeanCage.Entry.CallerPhysical

-- §AR-entry.caller.origin: Every field is a physical projection of the same task incarnation.
structure Context where
  tracer : Option ProcessIdentity
  options : Nat
  issued : List Nat
  parentAlive : Bool
  childAlive : Bool
  namespaceId : Nat
  cgroup : Option Nat

-- §FS-entry.provenance: Keep unauthorized attempts and arbitrary privileged debugger requests.
inductive Action where
  | idle
  | native
  | traceMe
  | request (actor : ProcessIdentity) (request : Nat) (options : Nat)
  | placement (group : Nat)
  | parentDeath
  | childDeath

-- §FS-entry.provenance: This pure view retains foreign control and unsafe native rewriting.
def ContextSafe (owner : ProcessIdentity) (context : Context) : Prop :=
  context.tracer = none ∨ (context.tracer = some owner ∧
    CallerRequestsAllowed context.issued ∧ TracerOptionsAllowed context.options)

-- §AR-entry.caller.origin: The permission predicate includes trusted ancestor application tasks.
-- Source obligations below apply to each actor that can actually alter this child.
inductive Step (mayTrace : ProcessIdentity → Prop) (owner child : ProcessIdentity) :
    Context → Action → Context → Prop
  | idle (context : Context) : Step mayTrace owner child context .idle context
  | nativeFrame (before after : Context)
      (tracer : after.tracer = before.tracer) (options : after.options = before.options)
      (issued : after.issued = before.issued) (parent : after.parentAlive = before.parentAlive)
      (alive : after.childAlive = before.childAlive) (space : after.namespaceId = before.namespaceId)
      (group : after.cgroup = before.cgroup) :
      Step mayTrace owner child before .native after
  | nativeUnsafe (before after : Context) (unprotected : ¬ContextSafe owner before) :
      Step mayTrace owner child before .native after
  | traceMe (before : Context) (untraced : before.tracer = none)
      (parent : before.parentAlive = true) (alive : before.childAlive = true) :
      Step mayTrace owner child before .traceMe
        { before with tracer := some owner, options := 0, issued := [] }
  | options (before : Context) (actor : ProcessIdentity) (value : Nat)
      (traced : before.tracer = some actor) (alive : before.childAlive = true) :
      Step mayTrace owner child before (.request actor 16896 value)
        { before with options := value, issued := before.issued ++ [16896] }
  | observe (before : Context) (actor : ProcessIdentity) (request : Nat) (value : Nat)
      (traced : before.tracer = some actor) (alive : before.childAlive = true)
      (opcode : request = 7 ∨ request = 16898) :
      Step mayTrace owner child before (.request actor request value)
        { before with issued := before.issued ++ [request] }
  | attach (before : Context) (actor : ProcessIdentity) (request : Nat) (value : Nat)
      (permission : mayTrace actor) (untraced : before.tracer = none)
      (alive : before.childAlive = true) (opcode : request = 16 ∨ request = 16902) :
      Step mayTrace owner child before (.request actor request value)
        { before with tracer := some actor, options := value, issued := [request] }
  | other (before after : Context) (actor : ProcessIdentity) (request : Nat) (value : Nat)
      (permission : mayTrace actor ∨ before.tracer = some actor)
      (opcode : ¬NonSubstitutingRequest request) :
      Step mayTrace owner child before (.request actor request value) after
  | denied (before : Context) (actor : ProcessIdentity) (request : Nat) (value : Nat)
      (permission : ¬mayTrace actor) (untraced : before.tracer ≠ some actor) :
      Step mayTrace owner child before (.request actor request value) before
  | failed (before : Context) (actor : ProcessIdentity) (request : Nat) (value : Nat) :
      Step mayTrace owner child before (.request actor request value) before
  | placement (before : Context) (group : Nat) :
      Step mayTrace owner child before (.placement group) { before with cgroup := some group }
  | parentKilled (before : Context) :
      Step mayTrace owner child before .parentDeath
        { before with parentAlive := false, childAlive := false }
  | parentDetached (before : Context) :
      Step mayTrace owner child before .parentDeath
        { before with parentAlive := false, tracer := none, options := 0, issued := [] }
  | childKilled (before : Context) :
      Step mayTrace owner child before .childDeath { before with childAlive := false }

-- §AR-entry.caller.origin: A source certificate says which operation this actor really issued.
-- The native certificate is proved over its current C execution. Ancestor certificates
-- are the named owned-VM preparation input; authority alone does not establish this predicate.
def SourceUse (mayTrace : ProcessIdentity → Prop) (history : List Nat)
    (before : Context) (action : Action) : Prop :=
  Action.rec (motive := fun _ => Prop) True True True
    (fun actor request options =>
      (mayTrace actor ∨ before.tracer = some actor) →
        SourceRequestMember request history ∧ SourceSupervisor request options)
    (fun _ => True) True True action

theorem source_use_request {mayTrace : ProcessIdentity → Prop} {history : List Nat}
    {before : Context} {actor : ProcessIdentity} {request : Nat} {options : Nat}
    (source : SourceSupervisorUse history request options) :
    SourceUse mayTrace history before (.request actor request options) := by
  intro _
  exact source

def Good (owner : ProcessIdentity) (history : List Nat) (context : Context) : Prop :=
  context.tracer = none ∨
    (context.tracer = some owner ∧ (∀ request ∈ context.issued, request ∈ history) ∧
      TracerOptionsAllowed context.options ∧ CallerRequestsAllowed context.issued)

theorem good_context_safe {owner : ProcessIdentity} {history : List Nat} {context : Context}
    (good : Good owner history context) : ContextSafe owner context := by
  rcases good with detached | ⟨owned, _, options, checked⟩
  · exact Or.inl detached
  · exact Or.inr ⟨owned, checked, options⟩

private theorem requests_allowed_append {first rest : List Nat}
    (before : CallerRequestsAllowed first) (after : CallerRequestsAllowed rest) :
    CallerRequestsAllowed (first ++ rest) := by
  induction first with
  | nil => exact after
  | cons request first ih => exact ⟨before.1, ih before.2⟩

def control (owner child : ProcessIdentity) (context : Context) : TracerControl :=
  match context.tracer with
  | none => .detached
  | some actor => if actor = owner then .exclusive owner child context.issued context.options.toUInt64 else .foreign

-- §FS-entry.provenance: Source payloads close the unsafe SETOPTIONS case of the broad relation.
theorem step_good {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity}
    {history : List Nat} {before after : Context} {action : Action}
    (prior : Good owner history before) (source : SourceUse mayTrace history before action)
    (operation : Step mayTrace owner child before action after) : Good owner history after := by
  cases operation with
  | idle => exact prior
  | nativeFrame after tracer options issued parent alive space group =>
    rcases prior with detached | ⟨owned, priorIssued, priorOptions, priorChecked⟩
    · exact Or.inl (tracer.trans detached)
    · exact Or.inr ⟨tracer.trans owned, by simpa only [issued] using priorIssued,
        by simpa only [options] using priorOptions,
        by simpa only [issued] using priorChecked⟩
  | nativeUnsafe after unprotected => exact False.elim (unprotected (good_context_safe prior))
  | traceMe untraced parent alive =>
    exact Or.inr ⟨rfl, by simp, Or.inl rfl, True.intro⟩
  | options actor value traced alive =>
    have facts := source (Or.inr traced)
    rcases prior with detached | ⟨owned, issued, options, checked⟩
    · rw [detached] at traced; contradiction
    · have actorOwner : actor = owner := Option.some.inj (traced.symm.trans owned)
      subst actor
      refine Or.inr ⟨owned, ?_, Or.inr ?_, requests_allowed_append checked ⟨facts.2.1, True.intro⟩⟩
      · intro request member
        rcases List.mem_append.mp member with old | last
        · exact issued request old
        · have selected : request = 16896 := by simpa using last
          subst request; exact source_request_member facts.1
      · exact facts.2.2 rfl
  | observe actor request value traced alive opcode =>
    have facts := source (Or.inr traced)
    rcases prior with detached | ⟨owned, issued, options, checked⟩
    · rw [detached] at traced; contradiction
    · refine Or.inr ⟨owned, ?_, options, requests_allowed_append checked ⟨facts.2.1, True.intro⟩⟩
      intro selected member
      rcases List.mem_append.mp member with old | last
      · exact issued selected old
      · have same : selected = request := by simpa using last
        subst selected; exact source_request_member facts.1
  | attach actor request value permission untraced alive opcode =>
    have allowed := (source (Or.inl permission)).2.1
    rcases opcode with rfl | rfl <;> simp [NonSubstitutingRequest] at allowed
  | other after actor request value permission opcode =>
    exact False.elim (opcode (source permission).2.1)
  | denied actor request value permission untraced => exact prior
  | failed actor request value => exact prior
  | placement group => exact prior
  | parentKilled => exact prior
  | parentDetached => exact Or.inl rfl
  | childKilled => exact prior

theorem good_control {owner child : ProcessIdentity} {history : List Nat} {context : Context}
    (good : Good owner history context) :
    CallerControlUse owner child history (control owner child context) := by
  rcases good with detached | ⟨owned, issued, options, checked⟩
  · simp only [control, detached]
    exact .detached
  · simp only [control, owned, ↓reduceIte]
    have narrow : context.options.toUInt64.toNat = context.options := by
      apply UInt64.toNat_ofNat_of_lt'
      change context.options < 18446744073709551616
      rcases options with zero | installed <;> omega
    exact .owned context.issued issued context.options.toUInt64 (by simpa only [narrow] using options)

theorem context_safe_non_substituting {owner child : ProcessIdentity} {context : Context}
    (safe : ContextSafe owner context) : (control owner child context).nonSubstituting := by
  rcases safe with detached | ⟨owned, checked, options⟩
  · simp only [control, detached, TracerControl.nonSubstituting]
  · simp only [control, owned, ↓reduceIte, TracerControl.nonSubstituting]
    have narrow : context.options.toUInt64.toNat = context.options := by
      apply UInt64.toNat_ofNat_of_lt'
      change context.options < 18446744073709551616
      rcases options with zero | installed <;> omega
    exact ⟨fun request member => caller_request_allowed checked member,
      by simpa only [narrow] using options⟩

theorem good_non_substituting {owner child : ProcessIdentity} {history : List Nat} {context : Context}
    (good : Good owner history context) : (control owner child context).nonSubstituting :=
  context_safe_non_substituting (good_context_safe good)

-- §FS-entry.provenance: The same full prefix produces the context used by the next native call.
inductive Runs (mayTrace : ProcessIdentity → Prop) (owner child : ProcessIdentity)
    (history : List Nat) : Context → List Action → Context → Prop
  | nil (context : Context) : Runs mayTrace owner child history context [] context
  | cons {before middle after : Context} {action : Action} {actions : List Action}
      (source : SourceUse mayTrace history before action)
      (operation : Step mayTrace owner child before action middle)
      (rest : Runs mayTrace owner child history middle actions after) :
      Runs mayTrace owner child history before (action :: actions) after

theorem runs_good {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity}
    {history : List Nat} {before after : Context} {actions : List Action}
    (good : Good owner history before)
    (run : Runs mayTrace owner child history before actions after) : Good owner history after := by
  induction run with
  | nil => exact good
  | cons source operation rest ih => exact ih (step_good good source operation)

-- §AR-entry.caller.origin: Fork/runtime copying supplies actual identities and the untraced slot.
def born (namespaceId : Nat) (cgroup : Option Nat) : Context :=
  ⟨none, 0, [], true, true, namespaceId, cgroup⟩


theorem fork_prefix_control {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity}
    {history : List Nat} {namespaceId : Nat} {cgroup : Option Nat} {after : Context}
    {actions : List Action}
    (run : Runs mayTrace owner child history (born namespaceId cgroup) actions after) :
    CallerControlUse owner child history (control owner child after) :=
  good_control (runs_good (Or.inl rfl) run)

-- §FS-entry.image: Supervision changes namespace/cgroup only at an explicit placement event.
theorem step_scope {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity}
    {history : List Nat} {before after : Context} {action : Action}
    (operation : Step mayTrace owner child before action after)
    (source : SourceUse mayTrace history before action)
    (notPlacement : ∀ group, action ≠ .placement group) (notNative : action ≠ .native) :
    after.namespaceId = before.namespaceId ∧ after.cgroup = before.cgroup := by
  cases operation with
  | nativeFrame => exact False.elim (notNative rfl)
  | nativeUnsafe => exact False.elim (notNative rfl)
  | placement group => exact False.elim (notPlacement group rfl)
  | other after actor request value permission opcode =>
    exact False.elim (opcode (source permission).2.1)
  | attach actor request value permission untraced alive opcode => exact ⟨rfl, rfl⟩
  | _ => exact ⟨rfl, rfl⟩


-- §AR-entry.effects: These conditions concern the arguments of one debugger operation.
def FrameAllowed (mayTrace : ProcessIdentity → Prop) (before : Context) : Action → Prop
  | .request actor request options =>
      (NonSubstitutingRequest request ∧ (request = 16896 → TracerOptionsAllowed options)) ∨
        (¬mayTrace actor ∧ before.tracer ≠ some actor)
  | _ => True

theorem source_frame_allowed {mayTrace : ProcessIdentity → Prop} {history : List Nat}
    {before : Context} {action : Action} (source : SourceUse mayTrace history before action) :
    FrameAllowed mayTrace before action := by
  cases action with
  | request actor request options =>
    by_cases authority : mayTrace actor ∨ before.tracer = some actor
    · have facts := (source authority).2
      exact Or.inl ⟨facts.1, fun selected => Or.inr (facts.2 selected)⟩
    · exact Or.inr ⟨fun permission => authority (Or.inl permission),
        fun owned => authority (Or.inr owned)⟩
  | _ => trivial

-- §AR-entry.effects: This is one genuine parent/kernel operation and its child projection.
-- It cannot choose the next source action or establish the whole caller's provenance.
structure SupervisorContract (mayTrace : ProcessIdentity → Prop) (owner child : ProcessIdentity) where
  returned : Nat → Context → State → Action → Context → State → Prop
  projection : ∀ position before state action after result,
    returned position before state action after result → Step mayTrace owner child before action after
  separate : ∀ position before state action after result,
    returned position before state action after result → action ≠ .native
  noTraceMe : ∀ position before state action after result,
    returned position before state action after result → action ≠ .traceMe
  frame : ∀ position before state action after result,
    returned position before state action after result → FrameAllowed mayTrace before action → result = state

-- §AR-entry.effects: A native call and its actual kernel context are sampled together.
structure NativeContract {fs : Filesystem} {platform : PrimitiveContract fs}
    (runtime : OriginContract platform) (mayTrace : ProcessIdentity → Prop)
    (owner child : ProcessIdentity) where
  returned : Nat → Context → ReturnOrigin → State → Request → Reply → Context → State → Prop
  live : ∀ position before origin state request reply after result,
    returned position before origin state request reply after result → before.childAlive = true
  effect : ∀ position before origin state request reply after result,
    returned position before origin state request reply after result →
    runtime.returns (control owner child before) origin state request reply result
  projection : ∀ position before origin state request reply after result,
    returned position before origin state request reply after result →
    ((request.op ≠ .traceMe ∨ origin ≠ .kernel ∨ reply.1 ≠ 0 ∨ ¬ContextSafe owner before) ∧
      Step mayTrace owner child before .native after) ∨
      ((request.op = .traceMe ∧ origin = .kernel ∧ reply.1 = 0 ∧
        Step mayTrace owner child before .traceMe after) ∨
        (∃ group, (request.op = .write ∨ origin = .intercepted ∨
          ¬(control owner child before).nonSubstituting) ∧
          Step mayTrace owner child before (.placement group) after))
  scope : ∀ position before origin state request reply after result,
    returned position before origin state request reply after result →
    (control owner child before).nonSubstituting → origin = .kernel → request.op ≠ .write →
    after.namespaceId = before.namespaceId ∧ after.cgroup = before.cgroup

-- §FS-entry.provenance: One journal interleaves the actual parent and child operations.
inductive Execution {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} (supervisor : SupervisorContract mayTrace owner child)
    (native : NativeContract runtime mayTrace owner child) (history : List Nat) :
    Nat → Context → State → List Action → List (Request × Reply) → List TracerControl → Context → State → Prop
  | done (position : Nat) (context : Context) (state : State) :
      Execution supervisor native history position context state [] [] [] context state
  | supervisor {position : Nat} {before middle after : Context} {state changed result : State}
      {journal : List Action} {trace : List (Request × Reply)} {controls : List TracerControl} {action : Action}
      (source : SourceUse mayTrace history before action)
      (operation : supervisor.returned position before state action middle changed)
      (rest : Execution supervisor native history (position + 1) middle changed journal trace controls after result) :
      Execution supervisor native history position before state (action :: journal) trace controls after result
  | native {position : Nat} {before middle after : Context} {state changed result : State}
      {journal : List Action} {trace : List (Request × Reply)} {controls : List TracerControl}
      (origin : ReturnOrigin) (request : Request) (reply : Reply)
      (operation : native.returned position before origin state request reply middle changed)
      (rest : Execution supervisor native history (position + 1) middle changed journal trace controls after result) :
      Execution supervisor native history position before state (.native :: journal) ((request, reply) :: trace)
        (control owner child before :: controls) after result

theorem native_good {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {native : NativeContract runtime mayTrace owner child}
    {history : List Nat} {position : Nat} {before after : Context} {origin : ReturnOrigin}
    {state result : State} {request : Request} {reply : Reply}
    (good : Good owner history before)
    (operation : native.returned position before origin state request reply after result) : Good owner history after := by
  rcases native.projection _ _ _ _ _ _ _ _ operation with ⟨_, frame⟩ | ⟨_, _, _, traceMe⟩ | ⟨group, _, placement⟩
  · exact step_good (action := .native) good trivial frame
  · exact step_good (action := .traceMe) good trivial traceMe
  · exact step_good (history := history) (action := .placement group) good trivial placement

-- §AR-entry.acceptance: The actual journal produces every body snapshot and the exec-time snapshot.
theorem execution_returns {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {native : NativeContract runtime mayTrace owner child} {history : List Nat}
    {position : Nat} {before after : Context} {initial final : State}
    {journal : List Action} {trace : List (Request × Reply)} {controls : List TracerControl}
    (good : Good owner history before)
    (run : Execution supervisor native history position before initial journal trace controls after final) :
    CallerReturns runtime owner child history initial trace controls final ∧
      CallerControlUse owner child history (control owner child after) := by
  induction run with
  | done position context state => exact ⟨.nil state, good_control good⟩
  | supervisor source operation rest ih =>
    have same := supervisor.frame _ _ _ _ _ _ operation (source_frame_allowed source)
    subst_vars
    exact ih (step_good good source (supervisor.projection _ _ _ _ _ _ operation))
  | native origin request reply operation rest ih =>
    have result := ih (native_good good operation)
    exact ⟨.cons _ origin request reply (native.effect _ _ _ _ _ _ _ _ operation)
      (good_control good) result.1, result.2⟩

theorem fork_execution_returns {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {native : NativeContract runtime mayTrace owner child} {history : List Nat}
    {position namespaceId : Nat} {cgroup : Option Nat} {after : Context} {initial final : State}
    {journal : List Action} {trace : List (Request × Reply)} {controls : List TracerControl}
    (run : Execution supervisor native history position (born namespaceId cgroup) initial journal trace controls after final) :
    CallerReturns runtime owner child history initial trace controls final ∧
      CallerControlUse owner child history (control owner child after) :=
  execution_returns (Or.inl rfl) run


-- §FS-entry.image: This suffix starts at the actual grant context, after cgroup placement.
theorem execution_scope {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {native : NativeContract runtime mayTrace owner child} {history : List Nat}
    {position : Nat} {before after : Context} {initial final : State}
    {journal : List Action} {trace : List (Request × Reply)} {controls : List TracerControl}
    (run : Execution supervisor native history position before initial journal trace controls after final)
    (noPlacement : ∀ action ∈ journal, ∀ group, action ≠ .placement group)
    (noWrite : ∀ pair ∈ trace, pair.1.op ≠ .write)
    (genuine : ∀ position before origin state request reply after result,
      native.returned position before origin state request reply after result →
      (control owner child before).nonSubstituting ∧ origin = .kernel) :
    after.namespaceId = before.namespaceId ∧ after.cgroup = before.cgroup := by
  induction run with
  | done => exact ⟨rfl, rfl⟩
  | supervisor source operation rest ih =>
    have first := step_scope (supervisor.projection _ _ _ _ _ _ operation) source
      (noPlacement _ (by simp)) (supervisor.separate _ _ _ _ _ _ operation)
    have later := ih (by intro action member; exact noPlacement action (by simp [member])) noWrite
    exact ⟨later.1.trans first.1, later.2.trans first.2⟩
  | native origin request reply operation rest ih =>
    have observed := genuine _ _ _ _ _ _ _ _ operation
    have first := native.scope _ _ _ _ _ _ _ _ operation observed.1 observed.2
      (noWrite (request, reply) (by simp))
    have later := ih (by intro action member; exact noPlacement action (by simp [member]))
      (by intro pair member; exact noWrite pair (by simp [member]))
    exact ⟨later.1.trans first.1, later.2.trans first.2⟩

-- §FS-entry.release: A selected read retains its real global operation ordinal in this journal.
theorem execution_native_member {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {native : NativeContract runtime mayTrace owner child} {history : List Nat}
    {position : Nat} {before after : Context} {initial final : State}
    {journal : List Action} {trace : List (Request × Reply)} {controls : List TracerControl}
    {request : Request} {reply : Reply}
    (good : Good owner history before)
    (run : Execution supervisor native history position before initial journal trace controls after final)
    (member : (request, reply) ∈ trace) :
    ∃ ordinal context origin state next changed,
      position ≤ ordinal ∧ native.returned ordinal context origin state request reply next changed ∧
        CallerControlUse owner child history (control owner child context) := by
  induction run with
  | done => contradiction
  | supervisor source operation rest ih =>
    obtain ⟨ordinal, context, origin, state, next, changed, bound, effect, snapshot⟩ :=
      ih (step_good good source (supervisor.projection _ _ _ _ _ _ operation)) member
    exact ⟨ordinal, context, origin, state, next, changed, by omega, effect, snapshot⟩
  | native selectedOrigin selectedRequest selectedReply operation rest ih =>
    rcases List.mem_cons.mp member with selected | later
    · have requests : request = selectedRequest := congrArg Prod.fst selected
      have replies : reply = selectedReply := congrArg Prod.snd selected
      subst request reply
      exact ⟨_, _, _, _, _, _, Nat.le_refl _, operation, good_control good⟩
    · obtain ⟨ordinal, context, origin, state, next, changed, bound, effect, snapshot⟩ :=
        ih (native_good good operation) later
      exact ⟨ordinal, context, origin, state, next, changed, by omega, effect, snapshot⟩


-- §AR-entry.caller.origin: Encode namespace-interpreted PID/incarnation pairs without narrowing.
def taskKey (task : ProcessIdentity) : Nat := task.incarnation * 2147483648 + task.pid

theorem taskKey_injective {left right : ProcessIdentity} (same : taskKey left = taskKey right) :
    left = right := by
  have leftBound := left.bounded
  have rightBound := right.bounded
  have pid : left.pid = right.pid := by unfold taskKey at same; omega
  have incarnation : left.incarnation = right.incarnation := by unfold taskKey at same; omega
  cases left
  cases right
  simp_all only

-- §FS-entry.release: These are committed socket bytes, including acknowledgement loss.
-- Descriptor lookup in the same tick determines the endpoint object; bytes are unsigned octets.
inductive SocketObservation where
  | none
  | read (actor : ProcessIdentity) (descriptor requested : Nat) (bytes : List Nat)
  | wrote (actor : ProcessIdentity) (descriptor : Nat) (bytes : List Nat) (lost : Bool)
  | interrupted (toParent toChild : Nat)

-- §AR-entry.caller.origin: A C event retains its actual task run and local source ordinal.
structure SourceReference where
  program : Nat
  ordinal : Nat

-- §AR-entry.caller.origin: This label identifies the actual primitive at its kernel position.
inductive PrimitiveFamily where
  | native
  | metadata

structure PrimitiveLabel where
  family : PrimitiveFamily
  code : Nat
  kernel : Bool

-- §AR-entry.caller.origin: The descriptor table and socket event share one kernel position.
structure Tick where
  before : Context
  action : Action
  after : Context
  objects : Nat → Nat → Option Nat
  cloexec : Nat → Nat → Bool
  socket : SocketObservation
  source : Option SourceReference
  primitive : Option PrimitiveLabel := none

-- §AR-entry.caller.values: This is one descriptor binding in the same sampled global tick.
def TickBinding (tick : Tick) (actorKey fd object : Nat) (flag : Bool) : Prop :=
  tick.objects actorKey fd = some object ∧ tick.cloexec actorKey fd = flag

-- §FS-entry.image: Linux cgroup placement is the effect of one classified command-file write.
def PlacementRecording (groups : Nat → Option Nat) (tick : Tick) : Prop :=
  ∀ group, tick.action = .placement group →
    ∃ actor fd object bytes lost, fd ≤ 2147483647 ∧
      tick.socket = .wrote actor fd bytes lost ∧
      tick.objects (taskKey actor) fd = some object ∧ groups object = some group

-- §AR-entry.caller.origin: These are raw descriptor observations from the same source tick.
def CgroupAbsent (groups : Nat → Option Nat) (tick : Tick) (actor : ProcessIdentity) : Prop :=
  ∀ fd object, fd ≤ 2147483647 → tick.objects (taskKey actor) fd = some object → groups object = none

def WriteOutsideCgroup (groups : Nat → Option Nat) (tick : Tick) : Prop :=
  ∀ actor fd bytes lost object, fd ≤ 2147483647 →
    tick.socket = .wrote actor fd bytes lost →
    tick.objects (taskKey actor) fd = some object → groups object = none

-- §AR-entry.caller.origin: Keep the producer's exact source reference and actor exclusions.
def WriteSourceOrExternal (owner child : ProcessIdentity) (tick : Tick) : Prop :=
  ∀ actor fd bytes lost, tick.socket = .wrote actor fd bytes lost →
    (∃ reference, tick.source = some reference) ∨ (actor ≠ owner ∧ actor ≠ child)

theorem absent_writer_outside_cgroup {groups : Nat → Option Nat} {tick : Tick}
    (absent : ∀ actor fd bytes lost, tick.socket = .wrote actor fd bytes lost → CgroupAbsent groups tick actor) :
    WriteOutsideCgroup groups tick := by
  intro actor fd bytes lost object bounded wrote present
  exact absent actor fd bytes lost wrote fd object bounded present

theorem recorded_write_cannot_place {groups : Nat → Option Nat} {tick : Tick}
    (recording : PlacementRecording groups tick) (outside : WriteOutsideCgroup groups tick) :
    ∀ group, tick.action ≠ .placement group := by
  intro group placed
  obtain ⟨actor, fd, object, bytes, lost, bounded, wrote, present, classified⟩ := recording group placed
  have absent := outside actor fd bytes lost object bounded wrote present
  rw [absent] at classified
  contradiction


inductive Journal (mayTrace : ProcessIdentity → Prop) (owner child : ProcessIdentity)
    (history : List Nat) : Context → List Tick → Context → Prop
  | done (context : Context) : Journal mayTrace owner child history context [] context
  | next (tick : Tick) {ticks : List Tick} {after : Context}
      (source : SourceUse mayTrace history tick.before tick.action)
      (operation : Step mayTrace owner child tick.before tick.action tick.after)
      (rest : Journal mayTrace owner child history tick.after ticks after) :
      Journal mayTrace owner child history tick.before (tick :: ticks) after

-- §FS-entry.release: All parent, metadata and native ordinals use one journal.
def TickAt : List Tick → Nat → Tick → Prop
  | [], _, _ => False
  | current :: _, 0, tick => current = tick
  | _ :: ticks, offset + 1, tick => TickAt ticks offset tick

theorem tickAt_getElem {ticks : List Tick} {offset : Nat} {tick : Tick}
    (selected : TickAt ticks offset tick) : ticks[offset]? = some tick := by
  induction ticks generalizing offset with
  | nil => contradiction
  | cons current ticks ih =>
    cases offset with
    | zero => exact congrArg some selected
    | succ offset => exact ih selected

def At (start : Nat) (ticks : List Tick) (ordinal : Nat) (context : Context) : Prop :=
  ∃ offset tick, ordinal = start + offset ∧ TickAt ticks offset tick ∧ context = tick.before

-- §FS-entry.image: This predicate names the actual post-grant suffix of the shared journal.
def NoPlacementFrom (start : Nat) (ticks : List Tick) (cutoff : Nat) : Prop :=
  ∀ offset tick, cutoff ≤ start + offset → TickAt ticks offset tick →
    ∀ group, tick.action ≠ .placement group

-- §FS-entry.image: Later workload events remain outside the proved admission-to-exec interval.
def NoPlacementBefore (start : Nat) (ticks : List Tick) (cutoff limit : Nat) : Prop :=
  ∀ offset tick, cutoff ≤ start + offset → start + offset < limit → TickAt ticks offset tick →
    ∀ group, tick.action ≠ .placement group

-- §FS-entry.provenance: Real later caller activity rules out an earlier actual parent exit.
def ParentLiveBefore (start : Nat) (ticks : List Tick) (limit : Nat) : Prop :=
  ∀ offset tick, start + offset < limit → TickAt ticks offset tick → tick.after.parentAlive = true

private theorem step_parent_live {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {history : List Nat} {before after : Context} {action : Action}
    (good : Good owner history before) (source : SourceUse mayTrace history before action)
    (operation : Step mayTrace owner child before action after) (live : after.parentAlive = true) :
    before.parentAlive = true := by
  cases operation with
  | nativeFrame after tracer options issued parent alive space group =>
    simpa only [parent] using live
  | nativeUnsafe after unprotected => exact False.elim (unprotected (good_context_safe good))
  | other after actor request value permission opcode =>
    exact False.elim (opcode (source permission).2.1)
  | parentKilled => cases live
  | parentDetached => cases live
  | _ => exact live

theorem journal_checkpoint_parent_live {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {history : List Nat} {start : Nat}
    {before after : Context} {ticks : List Tick} {offset : Nat} {checkpoint : Tick}
    (journal : Journal mayTrace owner child history before ticks after) (good : Good owner history before)
    (selected : TickAt ticks offset checkpoint) (live : checkpoint.after.parentAlive = true) :
    before.parentAlive = true ∧ ParentLiveBefore start ticks (start + offset + 1) := by
  induction journal generalizing start offset with
  | done => cases offset <;> contradiction
  | next current source operation rest ih =>
    cases offset with
    | zero =>
      cases selected
      refine ⟨step_parent_live good source operation live, ?_⟩
      intro index tick bounded actual
      cases index with
      | zero => cases actual; exact live
      | succ index => omega
    | succ offset =>
      obtain ⟨middleLive, prior⟩ := ih (start := start + 1)
        (step_good good source operation) selected
      refine ⟨step_parent_live good source operation middleLive, ?_⟩
      intro index tick bounded actual
      cases index with
      | zero => cases actual; exact middleLive
      | succ index => exact prior index tick (by omega) actual

theorem journal_parent_live_before {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {history : List Nat} {start namespaceId : Nat} {cgroup : Option Nat}
    {after : Context} {ticks : List Tick} {offset : Nat} {checkpoint : Tick}
    (journal : Journal mayTrace owner child history (born namespaceId cgroup) ticks after)
    (selected : TickAt ticks offset checkpoint) (live : checkpoint.after.parentAlive = true) :
    ParentLiveBefore start ticks (start + offset + 1) :=
  (journal_checkpoint_parent_live journal (Or.inl rfl) selected live).2

theorem journal_member_good {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity}
    {history : List Nat} {before after : Context} {ticks : List Tick}
    (good : Good owner history before) (journal : Journal mayTrace owner child history before ticks after)
    {offset : Nat} {tick : Tick} (selected : ticks[offset]? = some tick) :
    Good owner history tick.before := by
  induction journal generalizing offset with
  | done => simp at selected
  | next current source operation rest ih =>
    cases offset with
    | zero =>
      have same : current = tick := by simpa using selected
      subst tick; exact good
    | succ offset =>
      exact ih (step_good good source operation) (by simpa using selected)

-- §FS-entry.provenance: The metadata/native adapter erases this exact sampled journal position.
theorem journal_snapshot {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity}
    {history : List Nat} {start namespaceId : Nat} {cgroup : Option Nat}
    {ticks : List Tick} {after context : Context} {ordinal : Nat}
    (journal : Journal mayTrace owner child history (born namespaceId cgroup) ticks after)
    (sampled : At start ticks ordinal context) :
    CallerControlUse owner child history (control owner child context) := by
  obtain ⟨offset, tick, position, selected, same⟩ := sampled
  subst context
  exact good_control (journal_member_good (Or.inl rfl) journal (tickAt_getElem selected))

-- §AR-entry.effects: Parent death may detach before the pending fatal signal is observed.
-- Separate childDeath events retain the intervening live kernel outcomes.

-- §AR-entry.caller.origin: Carry installed-stack snapshots through actual source labels.
inductive Ancestry (runtime : CallerLineageContract) :
    ProcessIdentity → List ByteArray → List (Nat × Nat) → ProcessIdentity → List ByteArray → Prop
  | done (task : ProcessIdentity) (installed : List ByteArray) :
      Ancestry runtime task installed [] task installed
  | next {before middle after : ProcessIdentity} {initial changed final : List ByteArray}
      {rest : List (Nat × Nat)} (kind request : Nat)
      (operation : runtime.step kind request before middle initial changed)
      (source : CallerLineageAllowed kind request)
      (remaining : Ancestry runtime middle changed rest after final) :
      Ancestry runtime before initial ((kind, request) :: rest) after final

theorem ancestry_lineage {runtime : CallerLineageContract} {before after : ProcessIdentity}
    {initial final : List ByteArray} {source : List (Nat × Nat)}
    (prior : CallerLineage runtime before initial)
    (path : Ancestry runtime before initial source after final) : CallerLineage runtime after final := by
  induction path with
  | done => exact prior
  | next kind request operation source remaining ih =>
    exact ih (.step kind request prior operation source)

-- §FS-entry.provenance: This is one live runtime snapshot's installed/active projection law.
-- It does not assume the installed stack is empty or that the application prepared it correctly.
def StackObservation (installed : List ByteArray) (state : State) : Prop :=
  installed = [] → state.filters = []

theorem source_startup_lineage {runtime : CallerLineageContract} {owner child : ProcessIdentity}
    {before installed : List ByteArray} {source : List (Nat × Nat)} {startup : State}
    (ancestor : CallerLineage runtime owner before)
    (path : Ancestry runtime owner before source child installed)
    (observed : StackObservation installed startup) : CallerLineage runtime child startup.filters := by
  have lineage := ancestry_lineage ancestor path
  have clean := caller_lineage_clean lineage
  have active := observed clean
  simpa only [active, clean] using lineage

end LeanCage.Entry.CallerPhysical

namespace LeanCage.Entry.CallerPhysical

-- §AR-entry.effects: The maintained native request enum contains only these primitive tags.
def LocalEntryCode (code : Nat) : Prop := code ≤ 27

theorem native_code_is_local (request : Request) : LocalEntryCode request.op.code.toNat := by
  unfold LocalEntryCode
  cases request.op <;> decide

end LeanCage.Entry.CallerPhysical
