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

end LeanCage.Entry
