import LeanCageEntry.State
import Init.Data.UInt.Bitwise

namespace LeanCage.Entry

-- §AR-entry.effects: Component projections commute with the individual Linux updates.
theorem after_projection {β : Type} (fs : Filesystem) (commands : List Command)
    (initial : State) (project : State → β) (step : Request → β → β)
    (commutes : ∀ request state, project (update fs request state) = step request (project state)) :
    project (after fs commands initial) =
      commands.foldl (fun value command => step command.request value) (project initial) := by
  induction commands generalizing initial with
  | nil => rfl
  | cons command rest ih =>
    change project (after fs rest (update fs command.request initial)) = _
    rw [ih, commutes]
    rfl

def defaultBits (request : Request) : UInt64 :=
  match request.op with
  | .signalDefault => 1 <<< (request.a - 1)
  | _ => 0

def boundingMask (request : Request) : UInt64 :=
  match request.op with
  | .prctl => if request.a == 24 then ~~~(1 <<< request.b) else -1
  | _ => -1

theorem update_defaults (fs : Filesystem) (request : Request) (state : State) :
    (update fs request state).defaults = state.defaults ||| defaultBits request := by
  cases request with
  | mk op a b c text args data =>
    cases op <;> dsimp [update, defaultBits]
    all_goals repeat first | rfl | exact UInt64.or_zero.symm | split

theorem update_bounding (fs : Filesystem) (request : Request) (state : State) :
    (update fs request state).boundingCaps = state.boundingCaps &&& boundingMask request := by
  cases request with
  | mk op a b c text args data =>
    cases op <;> dsimp [update, boundingMask]
    all_goals try exact UInt64.and_neg_one.symm
    case prctl =>
      by_cases equal : a = 24
      · simp [equal]
      · have different : (a == 24) = false := beq_eq_false_iff_ne.mpr equal
        simp only [different, Bool.false_eq_true, ↓reduceIte, UInt64.and_neg_one]
        repeat first | rfl | split

theorem fold_or_mask (commands : List Command) (initial : UInt64) :
    commands.foldl (fun value command => value ||| defaultBits command.request) initial =
      initial ||| commands.foldr (fun command value => defaultBits command.request ||| value) 0 := by
  induction commands generalizing initial with
  | nil => simp
  | cons command rest ih =>
    simp only [List.foldl_cons, List.foldr_cons, ih, UInt64.or_assoc]

theorem fold_and_mask (commands : List Command) (initial : UInt64) :
    commands.foldl (fun value command => value &&& boundingMask command.request) initial =
      initial &&& commands.foldr (fun command value => boundingMask command.request &&& value)
        (-1) := by
  induction commands generalizing initial with
  | nil => exact UInt64.and_neg_one.symm
  | cons command rest ih =>
    simp only [List.foldl_cons, List.foldr_cons, ih, UInt64.and_assoc]

-- §FS-entry.control: This is reduction of the actual request list, independent of initial state.
set_option maxRecDepth 10000 in
theorem setup_default_bits (p : Inputs) (normal : p.fault = "normal") :
    (setup p).foldr (fun command value => defaultBits command.request ||| value) 0 =
      18446744073709289215 := by
  simp [setup, signalSetup, handshake, handleSetup, rootSetup, credentialSetup, filterSetup,
    cmd, defaultBits, normal, List.range, List.range.loop]
  decide

set_option maxRecDepth 10000 in
theorem setup_bounding_mask (p : Inputs) (normal : p.fault = "normal") :
    (setup p).foldr (fun command value => boundingMask command.request &&& value)
      (-1) = 18446741874686296064 := by
  simp [setup, signalSetup, handshake, handleSetup, rootSetup, credentialSetup, filterSetup,
    cmd, boundingMask, normal, List.range, List.range.loop]
  decide

theorem after_signal_defaults (fs : Filesystem) (p : Inputs) (initial : State)
    (normal : p.fault = "normal") :
    (after fs (setup p) initial).defaults ||| 262400 = 18446744073709551615 := by
  rw [after_projection fs (setup p) initial State.defaults
    (fun request value => value ||| defaultBits request) (update_defaults fs),
    fold_or_mask, setup_default_bits p normal, UInt64.or_assoc]
  change initial.defaults ||| (18446744073709551615 : UInt64) = _
  exact UInt64.or_neg_one

-- §FS-entry.runtime: The supported kernel has no capability numbered 41 or higher.
theorem after_bounding_empty (fs : Filesystem) (p : Inputs) (initial : State)
    (normal : p.fault = "normal")
    (kernelWidth : initial.boundingCaps &&& 18446741874686296064 = 0) :
    (after fs (setup p) initial).boundingCaps = 0 := by
  rw [after_projection fs (setup p) initial State.boundingCaps
    (fun request value => value &&& boundingMask request) (update_bounding fs),
    fold_and_mask, setup_bounding_mask p normal]
  exact kernelWidth

theorem setup_eq_normal (p : Inputs) (normal : p.fault = "normal") :
    setup p = setup { p with fault := "normal" } := by
  simp [setup, signalSetup, handshake, handleSetup, rootSetup, credentialSetup, filterSetup,
    cmd, normal]

def filterStep (request : Request) (filters : List ByteArray) : List ByteArray :=
  match request.op with
  | .filter => filters ++ [request.data]
  | _ => filters

theorem update_filters (fs : Filesystem) (request : Request) (state : State) :
    (update fs request state).filters = filterStep request state.filters := by
  cases request with
  | mk op a b c text args data =>
    cases op <;> dsimp [update, filterStep]
    all_goals repeat first | rfl | split

set_option maxRecDepth 10000 in
theorem after_filters (fs : Filesystem) (p : Inputs) (initial : State)
    (normal : p.fault = "normal") :
    (after fs (setup p) initial).filters = initial.filters ++ [LeanCageM3.Filter.bytes] := by
  rw [after_projection fs (setup p) initial State.filters filterStep (update_filters fs),
    setup_eq_normal p normal]
  rfl

def locationStep (fs : Filesystem) (request : Request) (location : Nat × Nat) : Nat × Nat :=
  match request.op with
  | .chroot => (fs.rootObject location.1 location.2 request.text, location.2)
  | .chdir => (location.1, fs.workingObject location.1 location.2 request.text)
  | _ => location

theorem update_location (fs : Filesystem) (request : Request) (state : State) :
    ((update fs request state).root, (update fs request state).cwd) =
      locationStep fs request (state.root, state.cwd) := by
  cases request with
  | mk op a b c text args data =>
    cases op <;> dsimp [update, locationStep]
    all_goals repeat first | rfl | split

set_option maxRecDepth 10000 in
theorem after_location (fs : Filesystem) (p : Inputs) (initial : State)
    (normal : p.fault = "normal") :
    ((after fs (setup p) initial).root, (after fs (setup p) initial).cwd) =
      (fs.rootObject initial.root initial.cwd p.root,
       fs.workingObject (fs.rootObject initial.root initial.cwd p.root) initial.cwd "/workspace") := by
  rw [after_projection fs (setup p) initial (fun state => (state.root, state.cwd))
    (locationStep fs) (update_location fs), setup_eq_normal p normal]
  rfl

def identityStep (request : Request) (identity : IDs × IDs) : IDs × IDs :=
  match request.op with
  | .setresuid => (identity.1.reassign request.a.toUInt32 request.b.toUInt32 request.c.toUInt32,
      identity.2)
  | .setresgid => (identity.1,
      identity.2.reassign request.a.toUInt32 request.b.toUInt32 request.c.toUInt32)
  | _ => identity

theorem update_identity (fs : Filesystem) (request : Request) (state : State) :
    ((update fs request state).uid, (update fs request state).gid) =
      identityStep request (state.uid, state.gid) := by
  cases request with
  | mk op a b c text args data =>
    cases op <;> dsimp [update, identityStep]
    all_goals repeat first | rfl | split

set_option maxRecDepth 10000 in
theorem after_identity (fs : Filesystem) (p : Inputs) (initial : State)
    (normal : p.fault = "normal") (specified : p.uid ≠ 4294967295) :
    ((after fs (setup p) initial).uid, (after fs (setup p) initial).gid) =
      (IDs.leased p.uid, IDs.leased p.uid) := by
  rw [after_projection fs (setup p) initial (fun state => (state.uid, state.gid))
    identityStep (update_identity fs), setup_eq_normal p normal]
  change (initial.uid.reassign p.uid.toUInt64.toUInt32 p.uid.toUInt64.toUInt32 p.uid.toUInt64.toUInt32,
    initial.gid.reassign p.uid.toUInt64.toUInt32 p.uid.toUInt64.toUInt32 p.uid.toUInt64.toUInt32) = _
  simp only [UInt32.toUInt32_toUInt64, IDs.reassign_all _ p.uid specified]

-- §FS-entry.control: These equations preserve object identities and the supplied ID values.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 500000 in
theorem after_values (fs : Filesystem) (p : Inputs) (initial : State)
    (normal : p.fault = "normal") (specified : p.uid ≠ 4294967295) :
    let current := after fs (setup p) initial
    current.uid = IDs.leased p.uid ∧ current.gid = IDs.leased p.uid ∧ current.groups = [] ∧
    current.effectiveCaps = 0 ∧ current.permittedCaps = 0 ∧ current.inheritableCaps = 0 ∧
    current.ambientCaps = 0 ∧ current.securebits = 15 ∧ current.dumpable = 0 ∧
    current.noNewPrivs = true ∧ current.filters = initial.filters ++ [LeanCageM3.Filter.bytes] ∧
    current.signalMask = 0 ∧ current.root = fs.rootObject initial.root initial.cwd p.root ∧
    current.cwd = fs.workingObject (fs.rootObject initial.root initial.cwd p.root) initial.cwd "/workspace" ∧
    current.umask = 63 := by
  have identity := after_identity fs p initial normal specified
  have location := after_location fs p initial normal
  refine ⟨congrArg Prod.fst identity, congrArg Prod.snd identity,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, after_filters fs p initial normal, ?_,
    congrArg Prod.fst location, congrArg Prod.snd location, ?_⟩
  all_goals rw [setup_eq_normal p normal]
  all_goals first
    | rfl
    | (change (0 : UInt64) &&& 18446744073709289215 = 0; exact UInt64.zero_and)
    | (change (63 : UInt64) &&& 511 = 63; decide)

theorem high_descriptor_not_standard (fd : UInt32) (high : 4 ≤ fd.toNat) :
    fd ≠ 0 ∧ fd ≠ 1 ∧ fd ≠ 2 ∧ fd ≠ 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro equal <;> rw [equal] at high <;> simp at high

theorem descriptor_fits (fd : UInt32) : fd.toUInt64 ≤ 4294967295 := by
  apply UInt64.le_iff_toNat_le.mpr
  have bound := fd.toNat_lt
  simp only [UInt32.toNat_toUInt64]
  change fd.toNat ≤ 4294967295
  omega

def handleStep (request : Request) (handles : UInt32 → Option Handle) : UInt32 → Option Handle :=
  match request.op with
  | .dup2 => if request.a.toUInt32 = request.b.toUInt32 then handles else
      duplicate handles request.a.toUInt32 request.b.toUInt32 false
  | .dup3 => duplicate handles request.a.toUInt32 request.b.toUInt32 (request.c &&& 524288 != 0)
  | .closeRange => fun fd => if request.a.toUInt32 ≤ fd && fd ≤ request.b.toUInt32 then
      (if request.c &&& 4 != 0 then (handles fd).map (fun h => { h with cloexec := true }) else none)
      else handles fd
  | _ => handles

theorem update_handles (fs : Filesystem) (request : Request) (state : State) :
    (update fs request state).handles = handleStep request state.handles := by
  cases request with
  | mk op a b c text args data =>
    cases op <;> dsimp [update, handleStep]
    all_goals repeat first | rfl | split

set_option maxRecDepth 10000 in
theorem after_handles (fs : Filesystem) (p : Inputs) (initial : State)
    (normal : p.fault = "normal") (inputHigh : 4 ≤ p.input.toNat)
    (outputHigh : 4 ≤ p.output.toNat) (errorsHigh : 4 ≤ p.errors.toNat) :
    (after fs (setup p) initial).handles =
      fun fd => if 4 ≤ fd && fd ≤ 4294967295 then none else
        duplicate (duplicate (duplicate (duplicate initial.handles p.input 0 false) p.output 1 false)
          p.errors 2 false) p.failure 3 true fd := by
  obtain ⟨input0, _, _, _⟩ := high_descriptor_not_standard p.input inputHigh
  obtain ⟨_, output1, _, _⟩ := high_descriptor_not_standard p.output outputHigh
  obtain ⟨_, _, errors2, _⟩ := high_descriptor_not_standard p.errors errorsHigh
  rw [after_projection fs (setup p) initial State.handles handleStep (update_handles fs)]
  simp [setup, signalSetup, handshake, handleSetup, rootSetup, credentialSetup, filterSetup,
    cmd, handleStep, normal, List.range, List.range.loop, input0, output1, errors2]

-- §FS-entry.inputs: Closing the high range leaves exactly the intended four object references.
theorem after_handle_objects (fs : Filesystem) (p : Inputs) (initial : State)
    (normal : p.fault = "normal")
    (inputHigh : 4 ≤ p.input.toNat)
    (outputHigh : 4 ≤ p.output.toNat) (errorsHigh : 4 ≤ p.errors.toNat)
    (failureHigh : 4 ≤ p.failure.toNat) :
    ∀ fd : UInt32, (after fs (setup p) initial).handles fd =
      if fd = 0 then (initial.handles p.input).map (fun h => { h with cloexec := false })
      else if fd = 1 then (initial.handles p.output).map (fun h => { h with cloexec := false })
      else if fd = 2 then (initial.handles p.errors).map (fun h => { h with cloexec := false })
      else if fd = 3 then (initial.handles p.failure).map (fun h => { h with cloexec := true })
      else none := by
  obtain ⟨out0, _, _, _⟩ := high_descriptor_not_standard p.output outputHigh
  obtain ⟨err0, err1, _, _⟩ := high_descriptor_not_standard p.errors errorsHigh
  obtain ⟨fail0, fail1, fail2, _⟩ := high_descriptor_not_standard p.failure failureHigh
  rw [after_handles fs p initial normal inputHigh outputHigh errorsHigh]
  intro fd
  by_cases low : fd.toNat < 4
  · have cases : fd.toNat = 0 ∨ fd.toNat = 1 ∨ fd.toNat = 2 ∨ fd.toNat = 3 := by omega
    rcases cases with h | h | h | h
    · have equal : fd = 0 := UInt32.toNat.inj h
      subst fd
      simp [duplicate]
    · have equal : fd = 1 := UInt32.toNat.inj h
      subst fd
      simp [duplicate, out0]
    · have equal : fd = 2 := UInt32.toNat.inj h
      subst fd
      simp [duplicate, err0, err1]
    · have equal : fd = 3 := UInt32.toNat.inj h
      subst fd
      simp [duplicate, fail0, fail1, fail2]
  · have high : 4 ≤ fd.toNat := by omega
    obtain ⟨fd0, fd1, fd2, fd3⟩ := high_descriptor_not_standard fd high
    have widened : (4 : UInt32) ≤ fd := UInt32.le_iff_toNat_le.mpr high
    have bound : fd ≤ 4294967295 := UInt32.le_iff_toNat_le.mpr (by
      have := fd.toNat_lt
      change fd.toNat ≤ 4294967295
      omega)
    simp [widened, bound, fd0, fd1, fd2, fd3]

def stableOperation (command : Command) : Bool :=
  match command.request.op with
  | .setresuid | .setresgid | .capset => false
  | _ => true

theorem stable_advance (fs : Filesystem) (command : Command) (before observed : State)
    (stable : stableOperation command = true) :
    advance fs command.request before observed = update fs command.request before := by
  cases command with
  | mk request expected stage failure =>
    cases request with
    | mk op a b c text args data => cases op <;> simp_all [stableOperation, advance, collateral]

theorem observed_stable (fs : Filesystem) (commands : List Command)
    (stable : commands.all stableOperation = true) (initial : State) (observed : Nat → State) :
    afterObserved fs commands initial observed = after fs commands initial := by
  induction commands generalizing initial observed with
  | nil => rfl
  | cons command rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at stable
    change afterObserved fs rest (advance fs command.request initial (observed 0)) _ =
      after fs rest (update fs command.request initial)
    rw [stable_advance fs command initial (observed 0) stable.1]
    exact ih stable.2 _ _

theorem after_append (fs : Filesystem) (left right : List Command) (initial : State) :
    after fs (left ++ right) initial = after fs right (after fs left initial) := by
  simp only [after, List.foldl_append]

theorem observed_append (fs : Filesystem) (left right : List Command)
    (initial : State) (observed : Nat → State) :
    afterObserved fs (left ++ right) initial observed =
      afterObserved fs right (afterObserved fs left initial observed)
        (fun n => observed (n + left.length)) := by
  induction left generalizing initial observed with
  | nil => rfl
  | cons command rest ih =>
    simpa only [List.cons_append, List.length_cons, afterObserved, Nat.add_assoc] using
      ih (advance fs command.request initial (observed 0)) (fun n => observed (n + 1))

theorem observed_append_neutral (fs : Filesystem) (left right : List Command)
    (leading : ∀ initial observed, afterObserved fs left initial observed = after fs left initial)
    (trailing : ∀ initial observed, afterObserved fs right initial observed = after fs right initial)
    (initial : State) (observed : Nat → State) :
    afterObserved fs (left ++ right) initial observed = after fs (left ++ right) initial := by
  rw [observed_append, leading, trailing, after_append]

-- §FS-entry.control: The actual tail contains capset and the final dumpability reset.
set_option maxRecDepth 10000 in
theorem credential_tail_neutral (fs : Filesystem) (p : Inputs) (initial : State)
    (normal : p.fault = "normal") (observed : Nat → State) :
    afterObserved fs ((credentialSetup p).drop 46) initial observed =
      after fs ((credentialSetup p).drop 46) initial := by
  have normalized : credentialSetup p = credentialSetup {p with fault := "normal"} := by
    simp [credentialSetup, cmd, normal]
  rw [normalized]
  rfl

set_option maxRecDepth 10000 in
theorem credential_collateral_neutral (fs : Filesystem) (p : Inputs)
    (initial : State) (normal : p.fault = "normal") (observed : Nat → State) :
    afterObserved fs (credentialSetup p) initial observed = after fs (credentialSetup p) initial := by
  have prefixStable : ((credentialSetup p).take 46).all stableOperation = true := by
    have normalized : credentialSetup p = credentialSetup {p with fault := "normal"} := by
      simp [credentialSetup, cmd, normal]
    rw [normalized]
    rfl
  have combined := observed_append_neutral fs ((credentialSetup p).take 46)
    ((credentialSetup p).drop 46) (observed_stable fs _ prefixStable)
    (fun initial observed => credential_tail_neutral fs p initial normal observed) initial observed
  simpa only [List.take_append_drop] using combined

set_option maxRecDepth 10000 in
theorem entry_prefix_collateral_neutral (fs : Filesystem) (p : Inputs)
    (initial : State) (normal : p.fault = "normal") (observed : Nat → State) :
    afterObserved fs (signalSetup p ++ handshake p ++ handleSetup p ++ rootSetup p ++ credentialSetup p)
      initial observed =
      after fs (signalSetup p ++ handshake p ++ handleSetup p ++ rootSetup p ++ credentialSetup p) initial := by
  have startStable : (signalSetup p ++ handshake p ++ handleSetup p ++ rootSetup p).all stableOperation = true := by
    have normalized : handshake p = handshake {p with fault := "normal"} := by simp [handshake, cmd, normal]
    rw [normalized]
    rfl
  exact observed_append_neutral fs _ _ (observed_stable fs _ startStable)
    (fun initial observed => credential_collateral_neutral fs p initial normal observed) initial observed

-- §FS-entry.control: All permitted collateral changes are reset by later executing operations.
theorem setup_collateral_neutral (fs : Filesystem) (p : Inputs) (initial : State)
    (normal : p.fault = "normal") (observed : Nat → State) :
    afterObserved fs (setup p) initial observed = after fs (setup p) initial := by
  have filtersStable : (filterSetup p).all stableOperation = true := rfl
  exact observed_append_neutral fs _ _
    (fun initial observed => entry_prefix_collateral_neutral fs p initial normal observed)
    (observed_stable fs _ filtersStable) initial observed

end LeanCage.Entry
