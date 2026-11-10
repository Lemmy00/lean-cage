import LeanCageHost.Program

namespace LeanCage.Host.Runtime
open Filesystem

def perform (request : Request) : LeanCage.Host.Program Reply :=
  LeanCage.Host.Program.liftFilesystem (Filesystem.Program.effect request)

def clock : LeanCage.Host.Program (Result Nat) := do
  let reply ← perform { op := .clock }
  if reply.1 != 0 || reply.2.size != 16 then return .error (failure "monotonic clock" reply)
  let seconds := fromLittleEndian (reply.2.extract 0 8)
  let nanos := fromLittleEndian (reply.2.extract 8 16)
  if seconds > 2 ^ 63 - 1 || nanos ≥ 1000000000 then
    return .error "invalid monotonic clock representation"
  return .ok (seconds * 1000000000 + nanos)

-- §FS-host-boundary.transport: Bound the supplied and returned poll lists.
def poll (descriptors : List (UInt64 × Nat)) (milliseconds : Nat) :
    LeanCage.Host.Program (Result (List Nat)) := do
  if descriptors.length > 8 || milliseconds > 100 ||
      !descriptors.all (fun item => item.1.toNat ≤ 2147483647 && (item.2 == 1 || item.2 == 4)) then
    return .error "invalid bounded poll request"
  let input := descriptors.foldl (fun bytes item =>
    bytes ++ littleEndian 8 item.1.toNat ++ littleEndian 8 item.2) ByteArray.empty
  let reply ← perform { op := .poll, first := milliseconds.toUInt64, left := input }
  if nativeError reply then return .error (failure "poll" reply)
  if reply.1.toNat > descriptors.length || reply.2.size != 8 * descriptors.length then
    return .error "invalid bounded poll reply"
  return .ok ((List.range descriptors.length).map (fun index =>
    fromLittleEndian (reply.2.extract (8 * index) (8 * (index + 1)))))

inductive Read where
  | pending
  | eof
  | data (bytes : ByteArray)

-- §FS-host-boundary.transport: Even a readiness indication cannot waive the actual read-size check.
def read (fd : UInt64) (amount : Nat) : LeanCage.Host.Program (Result Read) := do
  if amount == 0 || amount > chunkMax then return .error "invalid bounded runtime read"
  let reply ← perform { op := .read, first := fd, second := amount.toUInt64 }
  if nativeError reply then
    if errorNumber reply == 11 || errorNumber reply == 4 then return .ok .pending
    return .error (failure "runtime read" reply)
  if reply.1.toNat != reply.2.size || reply.2.size > amount then
    return .error "runtime read returned invalid bytes"
  if reply.2.isEmpty then return .ok .eof
  return .ok (.data reply.2)

end LeanCage.Host.Runtime
