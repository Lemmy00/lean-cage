import LeanCageHost.Validation
import LeanCageHost.Transport

namespace LeanCage.Host.Policy
open Filesystem

structure Accepted where
  value : Json.Value
  raw : ByteArray
  transport : Transport.Limits
  snapshot : Snapshot.Limits
  wallMilliseconds : Nat

def Accepted.sameBudgets (first second : Accepted) : Bool :=
  decide (first.transport = second.transport) &&
    first.snapshot.workspaceBytes == second.snapshot.workspaceBytes &&
    first.snapshot.workspaceInodes == second.snapshot.workspaceInodes &&
    first.snapshot.stdinBytes == second.snapshot.stdinBytes &&
    first.wallMilliseconds == second.wallMilliseconds

def boundedNatural (value : Json.Value) (key : String) (maximum : Nat) : Option Nat :=
  (Json.get? value key).bind (fun value => Json.naturalBelow? value maximum)

-- §FS-host-boundary.snapshot: Derive every host budget from the same accepted policy object.
def budgets (value : Json.Value) (raw : ByteArray) : Except String Accepted := do
  let some limits := Json.get? value "limits" | throw "missing policy limits"
  let some stdout := boundedNatural limits "stdout_max_bytes" captureMax
    | throw "unsupported stdout limit"
  let some stderr := boundedNatural limits "stderr_max_bytes" captureMax
    | throw "unsupported stderr limit"
  let some workspace := boundedNatural limits "workspace_max_bytes" workspaceMax
    | throw "unsupported workspace byte limit"
  let some inodes := boundedNatural limits "workspace_max_inodes" inodeMax
    | throw "unsupported workspace inode limit"
  let some stdin := boundedNatural limits "stdin_max_bytes" stdinMax
    | throw "unsupported stdin limit"
  let some wall := boundedNatural limits "wall_time_ms" 3600000
    | throw "unsupported wall time limit"
  let transport := Transport.Limits.mk stdout stderr workspace inodes
  let snapshot := Snapshot.Limits.mk workspace inodes stdin
  if !transport.valid || !snapshot.supported || wall == 0 || raw.size > reportMax then
    throw "policy exceeds supported host bounds"
  return ⟨value, raw, transport, snapshot, wall⟩

def replace (value : Json.Value) (key : String) (replacement : Json.Value) : Json.Value :=
  match value with
  | .object fields => .object (fields.map (fun field =>
      if field.1 == key then (key, replacement) else field))
  | other => other

def inputValue (identity : Option String) : Json.Value :=
  match identity with
  | none => .null
  | some identity => .string identity

def acceptsInput (value : Json.Value) (key : String) (identity : Option String) : Bool :=
  match Json.get? value key with
  | some .null => true
  | some (.string expected) => identity == some expected
  | _ => false

-- §FS-host-boundary.snapshot: Supplied identities must match the frozen bytes.
def bind (policy : Accepted) (frozen : Snapshot.Frozen) : Except String Accepted := do
  if !acceptsInput policy.value "workspace_input" frozen.workspaceIdentity ||
      !acceptsInput policy.value "stdin_input" frozen.stdinIdentity then
    throw "supplied snapshot differs from the policy input identity"
  let value := replace (replace policy.value "workspace_input" (inputValue frozen.workspaceIdentity))
    "stdin_input" (inputValue frozen.stdinIdentity)
  let bytes := Json.render value
  if bytes.size > reportMax then throw "bound policy exceeds 65536 bytes"
  budgets value bytes

-- §FS-host-boundary.caller: Interpret binary64 timeout bits as an exact rational.
def timeoutNanoseconds (field : GatewayWire.Field) (wallMilliseconds : Nat) : Except String Nat := do
  if field.kind == GatewayWire.absentKind then
    return 60000000000 + wallMilliseconds * 1000000
  if field.kind != GatewayWire.timeoutKind || field.bytes.size != 8 then
    throw "invalid VM timeout representation"
  let bits := fromLittleEndian field.bytes
  let exponent := bits / 2 ^ 52 % 2048
  let fraction := bits % 2 ^ 52
  if bits / 2 ^ 63 != 0 || exponent == 2047 || (exponent == 0 && fraction == 0) then
    throw "VM timeout must be positive and finite"
  let mantissa := if exponent == 0 then fraction else 2 ^ 52 + fraction
  let shift := if exponent == 0 then 1074 else 1075 - exponent
  if exponent > 1034 then throw "VM timeout is outside the supported bound"
  let denominator := 2 ^ shift
  if mantissa > 3660 * denominator then throw "VM timeout is outside the supported bound"
  return (mantissa * 1000000000 + denominator - 1) / denominator

end LeanCage.Host.Policy
