import LeanCageEntry.Worker
import Effects

namespace LeanCage.Entry

namespace ArgumentMeaning

-- §FS-entry.inputs: Positional ASCII value is independent of the decoder's acceptance checks.
def decimalValue (initial : Nat) : List UInt8 → Nat
  | [] => initial
  | byte :: rest => decimalValue (initial * 10 + (byte.toNat - 48)) rest

theorem digit_value {limit initial value : Nat} {byte : UInt8}
    (parsed : Arguments.digit limit initial byte = some value) :
    value = initial * 10 + (byte.toNat - 48) := by
  unfold Arguments.digit at parsed
  split at parsed
  · contradiction
  · dsimp only at parsed
    split at parsed
    · cases parsed
      rfl
    · contradiction

theorem digits_value {limit initial value : Nat} {bytes : List UInt8}
    (parsed : Arguments.digits limit initial bytes = some value) :
    value = decimalValue initial bytes := by
  induction bytes generalizing initial with
  | nil => cases parsed; rfl
  | cons byte rest ih =>
    simp only [Arguments.digits] at parsed
    cases step : Arguments.digit limit initial byte with
    | none => simp [step] at parsed
    | some next =>
      have remaining := ih (by simpa [step] using parsed)
      rw [remaining, digit_value step]
      rfl

theorem unsigned_value {limit value : Nat} {bytes : List UInt8}
    (parsed : Arguments.unsigned limit bytes = some value) : value = decimalValue 0 bytes := by
  cases bytes with
  | nil => contradiction
  | cons first rest =>
    change (if first.toNat == 48 && !rest.isEmpty then none else
      Arguments.digits limit 0 (first :: rest)) = some value at parsed
    split at parsed
    · contradiction
    · exact digits_value parsed

end ArgumentMeaning

-- §FS-entry.inputs: Interpretation is about the bytes the native caller supplied.
def ParsedHandoff (args : List String) (p : Inputs) : Prop :=
  ∃ mode uidText inputText outputText errorsText failureText uidValue,
    args = mode :: uidText :: p.root :: inputText :: outputText ::
      errorsText :: failureText :: p.fault :: p.argv.toList ∧
    (mode = "run" ∨ mode = "check") ∧ p.preflight = (mode == "check") ∧
    Arguments.unsigned 100999 uidText.toUTF8.data.toList = some uidValue ∧
    p.uid.toNat = uidValue ∧ (100000 ≤ uidValue ∧ uidValue ≤ 100999) ∧
    Worker.descriptor inputText = some p.input ∧ Worker.descriptor outputText = some p.output ∧
    Worker.descriptor errorsText = some p.errors ∧ Worker.descriptor failureText = some p.failure ∧
    inputsValid p = true

-- §AR-entry.caller: Every accepted private argv is tied to its original strings and values.
theorem worker_parse_exact (args : List String) (p : Inputs)
    (accepted : Worker.parse args = some p) : ParsedHandoff args p := by
  cases args with
  | nil => contradiction
  | cons mode args => cases args with
    | nil => contradiction
    | cons uid args => cases args with
      | nil => contradiction
      | cons root args => cases args with
        | nil => contradiction
        | cons input args => cases args with
          | nil => contradiction
          | cons output args => cases args with
            | nil => contradiction
            | cons errors args => cases args with
              | nil => contradiction
              | cons failure args => cases args with
                | nil => contradiction
                | cons fault argv =>
                  simp only [Worker.parse] at accepted
                  split at accepted
                  · contradiction
                  · rename_i supported
                    cases decoded : Arguments.unsigned 100999 uid.toUTF8.data.toList with
                    | none => simp only [decoded, bind, Option.bind_none, reduceCtorEq] at accepted
                    | some value =>
                      simp only [decoded, bind, Option.bind_some] at accepted
                      split at accepted
                      · contradiction
                      · rename_i low
                        cases i : Worker.descriptor input with
                        | none => simp only [i, Option.bind_none, reduceCtorEq] at accepted
                        | some iv =>
                          cases o : Worker.descriptor output with
                          | none => simp only [i, o, Option.bind_some, Option.bind_none, reduceCtorEq] at accepted
                          | some ov =>
                            cases e : Worker.descriptor errors with
                            | none => simp only [i, o, e, Option.bind_some, Option.bind_none, reduceCtorEq] at accepted
                            | some ev =>
                              cases f : Worker.descriptor failure with
                              | none => simp only [i, o, e, f, Option.bind_some, Option.bind_none, reduceCtorEq] at accepted
                              | some fv =>
                                simp only [i, o, e, f, Option.bind_some] at accepted
                                split at accepted
                                · rename_i valid
                                  cases accepted
                                  refine ⟨mode, uid, input, output, errors, failure, value,
                                    by simp, ?_, rfl, decoded, ?_, ?_, i, o, e, f, valid⟩
                                  · by_cases isRun : mode = "run"
                                    · exact Or.inl isRun
                                    · by_cases isCheck : mode = "check"
                                      · exact Or.inr isCheck
                                      · simp [isRun, isCheck] at supported
                                  · change (UInt32.ofNat value).toNat = value
                                    apply UInt32.toNat_ofNat_of_lt'
                                    have := Arguments.unsigned_bound decoded
                                    change value < 4294967296
                                    omega
                                  · exact ⟨by omega, Arguments.unsigned_bound decoded⟩
                                · contradiction

namespace ArgumentMeaning

-- §AR-entry.caller.values: This value interface is shared with the strict source proof.
def byteValues (uid input output errors failure : Nat) (mode root fault : List UInt8)
    (argv args : List (List UInt8)) : Prop :=
  ∃ uidText inputText outputText errorsText failureText,
    args = mode :: uidText :: root :: inputText :: outputText :: errorsText ::
      failureText :: fault :: argv ∧
    Arguments.unsigned 100999 uidText = some uid ∧
    Arguments.unsigned 2147483647 inputText = some input ∧
    Arguments.unsigned 2147483647 outputText = some output ∧
    Arguments.unsigned 2147483647 errorsText = some errors ∧
    Arguments.unsigned 2147483647 failureText = some failure

-- §AR-entry.caller.values: The source proof produces this exact imported proposition.
def nativeValues (uid input output errors failure : Nat) (mode root fault : List UInt8)
    (argv args : List (List UInt8)) : Prop :=
  ∀ actualUid actualInput actualOutput actualErrors actualFailure actualMode actualRoot actualFault actualArgv,
    byteValues actualUid actualInput actualOutput actualErrors actualFailure
      actualMode actualRoot actualFault actualArgv args →
    actualUid = uid ∧ actualInput = input ∧ actualOutput = output ∧
      actualErrors = errors ∧ actualFailure = failure ∧ actualMode = mode ∧
      actualRoot = root ∧ actualFault = fault ∧ actualArgv = argv

end ArgumentMeaning

-- §AR-entry.caller.values: Values come from the real parser, including its UInt32 narrowing.
theorem worker_byte_values (args : List String) (p : Inputs)
    (accepted : Worker.parse args = some p) :
    ∃ mode, (mode = "run" ∨ mode = "check") ∧ p.preflight = (mode == "check") ∧
      ArgumentMeaning.byteValues p.uid.toNat p.input.toNat p.output.toNat p.errors.toNat
        p.failure.toNat mode.toUTF8.data.toList p.root.toUTF8.data.toList
        p.fault.toUTF8.data.toList (p.argv.toList.map (·.toUTF8.data.toList))
        (args.map (·.toUTF8.data.toList)) := by
  obtain ⟨mode, uidText, inputText, outputText, errorsText, failureText, uidValue,
    original, supported, preflight, uid, uidExact, _, input, output, errors, failure, _⟩ :=
      worker_parse_exact args p accepted
  obtain ⟨iv, input, inputExact, _, _⟩ := Worker.descriptor_exact _ _ input
  obtain ⟨ov, output, outputExact, _, _⟩ := Worker.descriptor_exact _ _ output
  obtain ⟨ev, errors, errorsExact, _, _⟩ := Worker.descriptor_exact _ _ errors
  obtain ⟨fv, failure, failureExact, _, _⟩ := Worker.descriptor_exact _ _ failure
  refine ⟨mode, supported, preflight, uidText.toUTF8.data.toList,
    inputText.toUTF8.data.toList, outputText.toUTF8.data.toList,
    errorsText.toUTF8.data.toList, failureText.toUTF8.data.toList, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [original]
  · simpa [uidExact] using uid
  · simpa [inputExact] using input
  · simpa [outputExact] using output
  · simpa [errorsExact] using errors
  · simpa [failureExact] using failure

-- §AR-entry.caller.values: A source certificate is consumed by the actual worker parser.
theorem worker_native_values (args : List String) (p : Inputs)
    (uid input output errors failure : Nat) (mode root fault : List UInt8)
    (argv : List (List UInt8))
    (native : ArgumentMeaning.nativeValues uid input output errors failure mode root fault argv
      (args.map (·.toUTF8.data.toList)))
    (parsed : Worker.parse args = some p) :
    ∃ selectedMode, (selectedMode = "run" ∨ selectedMode = "check") ∧
      p.preflight = (selectedMode == "check") ∧
      p.uid.toNat = uid ∧ p.input.toNat = input ∧ p.output.toNat = output ∧
      p.errors.toNat = errors ∧ p.failure.toNat = failure ∧
      selectedMode.toUTF8.data.toList = mode ∧ p.root.toUTF8.data.toList = root ∧
      p.fault.toUTF8.data.toList = fault ∧ p.argv.toList.map (·.toUTF8.data.toList) = argv := by
  obtain ⟨selectedMode, supported, preflight, values⟩ := worker_byte_values args p parsed
  exact ⟨selectedMode, supported, preflight, native _ _ _ _ _ _ _ _ _ values⟩

-- §AR-entry.caller: Production reaches the very same reified definition used by the body proof.
theorem worker_normal_control (p : Inputs) (normal : p.fault = "normal") :
    Worker.executeAllowed false p = (admission p).interpret Linux.call := by
  simp [Worker.executeAllowed, Worker.enabled, normal]

-- §FS-entry.control: Parsing supplies values; physical caller premises are separate.
theorem worker_admission_values {fs : Filesystem} (platform : PrimitiveContract fs)
    (args : List String) (p : Inputs) (accepted : Worker.parse args = some p)
    (production : Worker.enabled false p = true) (initial current : State)
    (kernelWidth : initial.boundingCaps &&& 18446741874686296064 = 0)
    {trace : List (Request × Reply)} {request : Request}
    (control : AtExec (admission p) trace request)
    (effects : KernelTrace platform initial trace current) :
    ParsedHandoff args p ∧ Restricted fs p initial current ∧ request.op = .exec ∧
      request.text = p.argv[0]! ∧ request.args = p.argv ∧ request.data = environmentBytes := by
  exact ⟨worker_parse_exact args p accepted,
    admission_value_state platform p (Worker.production_mode p production) initial current
      kernelWidth control effects⟩

namespace PhysicalHandoff

-- §FS-entry.release: Positions refer to the same physical channel history.
def grantBeforeRead (sent read : Nat) : Prop := sent < read

-- §AR-entry.caller.values: Ordinary objects and both channel endpoints use disjoint identities.
def objectCode (tag identity : Nat) : Nat := identity * 3 + tag

theorem objectCode_injective {leftTag rightTag left right : Nat}
    (leftBound : leftTag < 3) (rightBound : rightTag < 3)
    (same : objectCode leftTag left = objectCode rightTag right) :
    leftTag = rightTag ∧ left = right := by
  unfold objectCode at same
  omega

-- §AR-entry.caller.values: This small proposition is exported to the source proof.
def binding (objects : Nat → Option Nat) (cloexec : Nat → Bool)
    (fd object : Nat) (flag : Bool) : Prop :=
  objects fd = some object ∧ cloexec fd = flag

-- §FS-entry.inputs: The loader observes the same physical table at the source image boundary.
-- Descriptor modes are supplied by the named prepared-object projection; neither a
-- clean table nor reserved slots are premises of this mapping.
def loadedHandles (objects : Nat → Option Nat) (cloexec : Nat → Bool)
    (readable writable : Nat → Bool) (state : State) : Prop :=
  state.handles = fun fd => (objects fd.toNat).map fun object =>
    { object, readable := readable fd.toNat, writable := writable fd.toNat,
      cloexec := cloexec fd.toNat }

theorem loaded_binding {objects : Nat → Option Nat} {cloexec readable writable : Nat → Bool}
    {state : State} {fd : UInt32} {object : Nat} {flag : Bool}
    (loaded : loadedHandles objects cloexec readable writable state)
    (physical : binding objects cloexec fd.toNat object flag) :
    state.handles fd = some
      { object, readable := readable fd.toNat, writable := writable fd.toNat, cloexec := flag } := by
  rcases physical with ⟨present, flags⟩
  rw [loaded]
  dsimp only
  rw [present]
  simp only [Option.map_some, flags]

theorem loaded_absent {objects : Nat → Option Nat} {cloexec readable writable : Nat → Bool}
    {state : State} {fd : UInt32}
    (loaded : loadedHandles objects cloexec readable writable state) (absent : objects fd.toNat = none) :
    state.handles fd = none := by
  rw [loaded]
  dsimp only
  rw [absent]
  rfl

end PhysicalHandoff

end LeanCage.Entry
