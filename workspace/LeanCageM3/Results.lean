import LeanCageM3.Policy

namespace LeanCageM3
open Lean

-- §FS-workspace.results: Historical entry, observed outcomes and cleanup knowledge are independent.
inductive Entry where
  | no | yes | unknown
  deriving DecidableEq, Repr

structure Result where
  kind : Nat
  stage : Nat
  detail : Nat
  entry : Entry
  clean : Bool
  triggers : Nat
  uid : Nat
  run : Nat
  cpu : Nat
  peak : Nat
  stdoutBytes : Nat
  stderrBytes : Nat
  elapsed : Nat
  exportState : Nat
  omitted : Nat
  exportDigest : ByteArray
  oomKills : Nat
  taskDenials : Nat
  exportError : Nat
  deriving DecidableEq

def little (bytes : ByteArray) (offset width : Nat) : Nat :=
  (List.range width).foldl (fun n i => n + (bytes[offset + i]?.getD 0).toNat * 2 ^ (8 * i)) 0

def resultValid (r : Result) : Bool :=
  (r.kind ≤ 4 || r.kind == 7) && r.triggers ≤ 63 && r.exportState ≤ 3 &&
  r.exportError ≤ 4095 && (if r.exportState < 2 then r.exportError == 0 else r.exportError > 0) &&
  ((r.kind != 0 && r.kind != 2 && r.kind != 3) || r.run > 0) &&
  r.exportDigest.size == 32 && (r.exportState == 1 || r.exportDigest == ByteArray.mk (Array.replicate 32 0)) &&
  ((r.run == 0 && r.uid == 0) || (r.run > 0 && 100000 ≤ r.uid && r.uid ≤ 100999)) &&
  match r.kind with
  | 0 => r.stage == 0 && r.detail ≤ 255 && r.entry == .yes
  | 1 => 1 ≤ r.stage && r.stage ≤ 8 && 0 < r.detail && r.detail ≤ 4095 && r.entry == .no
  | 2 => r.stage == 0 && 0 < r.detail && r.detail ≤ 64 && r.entry == .yes
  | 3 => r.stage == 0 && r.detail == 0 && r.triggers > 0
  | 4 => r.stage == 9 && 0 < r.detail && r.detail ≤ 4095
  | 7 => r.stage == 0 && r.detail == 0 && r.entry == .no && r.run == 0 && r.uid == 0 && r.clean && r.triggers == 0
  | _ => false

-- §AR-workspace.transport: Exact lengths, version, sequence, tags and reserved bytes; no console
-- parsing.
private def parseResult (bytes : ByteArray) : Except String Result := do
  if bytes.size != 160 || bytes.extract 0 4 != "LC3R".toUTF8 ||
      little bytes 4 2 != 1 || little bytes 16 8 != 0 || little bytes 24 4 != 128 ||
      little bytes 28 4 != 0 || little bytes 156 4 != 0 then
    throw "invalid private result frame"
  let entry ← match little bytes 40 4 with
    | 0 => pure Entry.no
    | 1 => pure Entry.yes
    | 2 => pure Entry.unknown
    | _ => throw "invalid entry knowledge"
  let cleanup := little bytes 44 4
  if cleanup > 1 then throw "invalid cleanup knowledge"
  let r : Result := ⟨little bytes 6 2, little bytes 32 4, little bytes 36 4, entry,
    cleanup == 1, little bytes 48 4, little bytes 52 4, little bytes 8 8,
    little bytes 56 8, little bytes 64 8, little bytes 72 8, little bytes 80 8, little bytes 88 8, little bytes 96 4, little bytes 100 4,
    bytes.extract 104 136, little bytes 136 8, little bytes 144 8, little bytes 152 4⟩
  return r

def validateResult (r : Result) : Except String Result :=
  if resultValid r then .ok r else .error "inconsistent private result"

def decodeResult (bytes : ByteArray) : Except String Result := do
  validateResult (← parseResult bytes)

-- §AR-workspace.proofs: Every accepted public frame passes the concrete knowledge/bounds checks.
theorem decodeResult_valid (bytes : ByteArray) (result : Result)
    (accepted : decodeResult bytes = .ok result) : resultValid result = true := by
  unfold decodeResult at accepted
  cases parsed : parseResult bytes with
  | error error =>
    rw [parsed] at accepted
    contradiction
  | ok value =>
    rw [parsed] at accepted
    change validateResult value = .ok result at accepted
    unfold validateResult at accepted
    split at accepted
    · cases accepted; assumption
    · contradiction

def Entry.label : Entry → String
  | .no => "no"
  | .yes => "yes"
  | .unknown => "unknown"

def hexBytes (bytes : ByteArray) : String :=
  String.ofList (bytes.data.toList.flatMap fun byte =>
    let n := byte.toNat
    ["0123456789abcdef".toList[n / 16]!, "0123456789abcdef".toList[n % 16]!])

def Result.json (r : Result) : Json := Json.mkObj [
  ("schema", "leancage-result-v1"), ("profile", toJson profile),
  ("runtime_manifest_digest", toJson runtimeDigest), ("run_id", toJson r.run),
  ("termination", toJson (match r.kind with
    | 0 => "exited" | 1 => "setup_failed" | 2 => "signaled" | 3 => "cancelled"
    | 7 => "preflight_supported" | _ => "unknown")),
  ("stage", toJson r.stage), ("detail", toJson r.detail), ("entry", toJson r.entry.label),
  ("cleanup", toJson (if r.clean then "complete" else "unknown")), ("cancellation_bits", toJson r.triggers),
  ("uid", toJson r.uid), ("cpu_usage_us", if r.triggers &&& 16 != 0 then Json.null else toJson r.cpu),
  ("memory_peak_bytes", if r.triggers &&& 16 != 0 then Json.null else toJson r.peak),
  ("stdout_bytes", if r.kind == 4 && r.triggers &&& 8 != 0 then Json.null else toJson r.stdoutBytes),
  ("stderr_bytes", if r.kind == 4 && r.triggers &&& 8 != 0 then Json.null else toJson r.stderrBytes),
  ("elapsed_ms", if r.triggers &&& 16 != 0 then Json.null else toJson r.elapsed),
  ("stdout_artifact", toJson s!"/m3-results/{r.run}/stdout"),
  ("stderr_artifact", toJson s!"/m3-results/{r.run}/stderr"),
  ("export", toJson (match r.exportState with
    | 0 => "discarded" | 1 => "complete" | 2 => "failed" | _ => "unavailable")),
  ("export_digest", if r.exportState == 1 then toJson (hexBytes r.exportDigest) else Json.null),
  ("export_errno", toJson r.exportError), ("export_omitted", toJson r.omitted), ("oom_kill_events", if r.triggers &&& 16 != 0 then Json.null else toJson r.oomKills),
  ("task_limit_events", if r.triggers &&& 16 != 0 then Json.null else toJson r.taskDenials),
  ("assurance", toJson "conditional-model-and-VM-evidence; native/Linux correspondence and hardware channels open") ]

-- §AR-workspace.proofs: Guest bytes and cancellation requests cannot establish entry or cleanup.
structure Knowledge where
  entry : Entry := .no
  cancelled : Bool := false
  extinct : Bool := false
  released : Bool := false
  deriving DecidableEq, Repr

inductive Observation where
  | guestBytes (bytes : ByteArray)
  | cancel
  | execObserved
  | reportLost
  | scopeExtinct
  | releaseObserved

def observe (state : Knowledge) : Observation → Knowledge
  | .guestBytes _ => state
  | .cancel => { state with cancelled := true }
  | .execObserved => { state with entry := .yes }
  | .reportLost => { state with entry := if state.entry == .yes then .yes else .unknown }
  | .scopeExtinct => { state with extinct := true }
  | .releaseObserved => if state.extinct then { state with released := true } else state

theorem guest_output_untrusted (state : Knowledge) (bytes : ByteArray) :
    observe state (.guestBytes bytes) = state := rfl

theorem cancel_not_completion (state : Knowledge) :
    (observe state .cancel).extinct = state.extinct ∧
      (observe state .cancel).entry = state.entry := ⟨rfl, rfl⟩

theorem release_requires_extinction (state : Knowledge)
    (before : state.released = false) (after : (observe state .releaseObserved).released = true) :
    state.extinct = true := by
  change (if state.extinct then { state with released := true } else state).released = true at after
  split at after
  · assumption
  · simp_all

theorem report_loss_preserves_entry (state : Knowledge) (entered : state.entry = .yes) :
    (observe state .reportLost).entry = .yes := by simp [observe, entered]

-- §AR-workspace.proofs: Any number of forged guest frames leaves private knowledge unchanged.
def guestOutputTrace (state : Knowledge) : List ByteArray → Knowledge
  | [] => state
  | bytes :: rest => guestOutputTrace (observe state (.guestBytes bytes)) rest

theorem private_report_knowledge (state : Knowledge) (outputs : List ByteArray) :
    guestOutputTrace state outputs = state := by
  induction outputs with
  | nil => rfl
  | cons bytes rest ih => exact ih

end LeanCageM3
