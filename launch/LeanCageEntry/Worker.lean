import LeanCageEntry
import LeanCageEntry.Startup
import LeanCageM3.API

namespace LeanCage.Entry.Worker

-- §FS-entry.inputs: Parse the private worker ABI totally before performing admission effects.
def descriptor (text : String) : Option UInt32 := do
  let n ← Arguments.unsigned 2147483647 text.toUTF8.data.toList
  if n < 4 then none else some n.toUInt32

-- §FS-entry.inputs: The actual caller's narrowing preserves the decoded descriptor value.
theorem descriptor_exact (text : String) (fd : UInt32) (accepted : descriptor text = some fd) :
    ∃ value, Arguments.unsigned 2147483647 text.toUTF8.data.toList = some value ∧
      fd.toNat = value ∧ 4 ≤ value ∧ value ≤ 2147483647 := by
  unfold descriptor at accepted
  change (Arguments.unsigned 2147483647 text.toUTF8.data.toList).bind
    (fun n => if n < 4 then none else some n.toUInt32) = some fd at accepted
  cases parsed : Arguments.unsigned 2147483647 text.toUTF8.data.toList with
  | none =>
    rw [parsed] at accepted
    change (none : Option UInt32) = some fd at accepted
    contradiction
  | some value =>
    rw [parsed] at accepted
    change (if value < 4 then none else some value.toUInt32) = some fd at accepted
    split at accepted
    · contradiction
    · cases accepted
      have bound := Arguments.unsigned_bound parsed
      refine ⟨value, rfl, ?_, by omega, bound⟩
      change (UInt32.ofNat value).toNat = value
      apply UInt32.toNat_ofNat_of_lt'
      change value < 4294967296
      omega

def parse (args : List String) : Option Inputs := do
  match args with
  | mode :: uid :: root :: input :: output :: errors :: failure :: fault :: argv =>
    if mode != "run" && mode != "check" then none else do
    let uid ← Arguments.unsigned 100999 uid.toUTF8.data.toList
    if uid < 100000 then none else do
    let p : Inputs := ⟨uid.toUInt32, root, ← descriptor input, ← descriptor output,
      ← descriptor errors, ← descriptor failure, argv.toArray, mode == "check", fault⟩
    if inputsValid p then some p else none
  | _ => none

-- §AR-application-verification.next: Production explicitly rejects test selectors.
def enabled (allowTestModes : Bool) (p : Inputs) : Bool :=
  allowTestModes || p.fault == "normal"

def executeAllowed (allowTestModes : Bool) (p : Inputs) : BaseIO UInt32 :=
  if enabled allowTestModes p then (admission p).interpret Linux.call else pure 125

theorem production_mode (p : Inputs) (accepted : enabled false p = true) : p.fault = "normal" := by
  simpa [enabled] using accepted

theorem production_rejects_mode (p : Inputs) (unsupported : p.fault ≠ "normal") :
    executeAllowed false p = pure 125 := by
  simp [executeAllowed, enabled, unsupported]

theorem normal_builds_agree (p : Inputs) (normal : p.fault = "normal") :
    executeAllowed false p = executeAllowed true p := by
  simp [executeAllowed, enabled, normal]

-- §FS-entry.runtime: Startup and setup share the same executable control used by the proof.
def startup (allowTestModes : Bool) (args : List String) : Startup UInt32 := do
  let .ok marker ← Startup.read "/leancage-m3-disposable-vm" 64 | return 125
  if marker != "LeanCage-M3-root-VM-v1".toUTF8 then return 125
  let .ok status ← Startup.read "/proc/self/status" 8192 | return 125
  let some status := String.fromUTF8? status | return 125
  if !(status.splitOn "\n").contains "Threads:\t1" then return 125
  match parse args with
  | none => return 125
  | some p =>
    if enabled allowTestModes p then Startup.admission (admission p) else return 125

-- §AR-metadata.frame: Startup uses the same bounded owned-handle control as public reads.
def inspect (path : String) (limit : Nat) : IO (Except IO.Error ByteArray) :=
  LeanCageM3.Metadata.inspect path limit

-- §FS-entry.runtime: Main calls this interpreter; no independent startup model is executed.
def run (allowTestModes : Bool) (args : List String) : IO UInt32 :=
  (startup allowTestModes args).interpret inspect (fun request => Linux.call request)

end LeanCage.Entry.Worker
