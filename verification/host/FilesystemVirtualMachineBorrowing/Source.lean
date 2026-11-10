import FilesystemRuntime
import LeanCageHost.VirtualMachine

namespace LeanCage.Host.VirtualMachine
open Filesystem

-- §FS-host-boundary.ownership: Only the new raw connection may later be closed by VM control.
def ConnectionFresh (held : UInt64) (state : State) : Prop :=
  ∀ fd, state.connection = some fd → fd ≠ held

def afterWait (state : State) (observed : Except String (Option UInt32)) : State :=
  match observed with
  | .ok (some code) => { state with exitCode := some code }
  | .ok none => state
  | .error error => state.fail error

-- §AR-host-boundary.interfaces: A definitional source continuation, retaining all branches.
def loopAfterSend (fuel : Nat) {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (path : ByteArray) (boot diagnostic : UInt64)
    (began duration now : Nat) (state : State) : LeanCage.Host.Program State := do
  if state.error.isSome then return state
  if state.channelEof && state.exitCode.isSome && !state.bootOpen && !state.diagnosticOpen then
    return state
  let descriptors := events state boot diagnostic
  let ready ← Runtime.poll descriptors 100
  let .ok ready := ready | return state.fail "VM readiness observation failed"
  let next ← consumeReady descriptors ready boot diagnostic now state
  if next.error.isSome then return next
  loop fuel child path boot diagnostic began duration next

-- §AR-host-boundary.interfaces: A definitional source continuation, retaining all branches.
def loopAfterConnection (fuel : Nat) {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (path : ByteArray) (boot diagnostic : UInt64)
    (began duration now : Nat) (state : State) : LeanCage.Host.Program State := do
  if state.error.isSome then return state
  if state.exitCode.isSome && state.connection.isNone then return state.fail "VM failed to start"
  let state ← if state.cancellation && state.sent.isNone then
      match state.connection with
      | none => pure state
      | some fd => do
        let sent ← Runtime.perform { op := .write, first := fd, left := "C".toUTF8 }
        if sent.1 == 1 && sent.2.isEmpty then pure { state with sent := some now }
        else pure (state.fail "VM cancellation transmission failed")
    else pure state
  if state.error.isSome then return state
  if state.channelEof && state.exitCode.isSome && !state.bootOpen && !state.diagnosticOpen then
    return state
  let descriptors := events state boot diagnostic
  let ready ← Runtime.poll descriptors 100
  let .ok ready := ready | return state.fail "VM readiness observation failed"
  let next ← consumeReady descriptors ready boot diagnostic now state
  if next.error.isSome then return next
  loop fuel child path boot diagnostic began duration next

-- §AR-host-boundary.interfaces: This is the unchanged executable continuation after tryWait.
def loopAfterWait (fuel : Nat) {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (path : ByteArray) (boot diagnostic : UInt64)
    (began duration : Nat) (state : State) : LeanCage.Host.Program State := do
  if state.error.isSome then return state
  let clock ← Runtime.clock
  let .ok now := clock | return state.fail "VM clock observation failed"
  if let some error := deadlineError state began duration now then return state.fail error
  let state ← if state.connection.isNone then do
      let connected ← connect path
      match connected with
      | .error error => pure (state.fail error.message)
      | .ok connection => pure { state with connection }
    else pure state
  if state.error.isSome then return state
  if state.exitCode.isSome && state.connection.isNone then return state.fail "VM failed to start"
  let state ← if state.cancellation && state.sent.isNone then
      match state.connection with
      | none => pure state
      | some fd => do
        let sent ← Runtime.perform { op := .write, first := fd, left := "C".toUTF8 }
        if sent.1 == 1 && sent.2.isEmpty then pure { state with sent := some now }
        else pure (state.fail "VM cancellation transmission failed")
    else pure state
  if state.error.isSome then return state
  if state.channelEof && state.exitCode.isSome && !state.bootOpen && !state.diagnosticOpen then
    return state
  let descriptors := events state boot diagnostic
  let ready ← Runtime.poll descriptors 100
  let .ok ready := ready | return state.fail "VM readiness observation failed"
  let next ← consumeReady descriptors ready boot diagnostic now state
  if next.error.isSome then return next
  loop fuel child path boot diagnostic began duration next

theorem loop_borrow_source (fuel : Nat) {configuration : IO.Process.StdioConfig}
    (child : IO.Process.Child configuration) (path : ByteArray) (boot diagnostic : UInt64)
    (began duration : Nat) (state : State) :
    loop (fuel + 1) child path boot diagnostic began duration state = (do
      let observed ← LeanCage.Host.Program.effect (.tryWait child)
      loopAfterWait fuel child path boot diagnostic began duration (afterWait state observed)) := rfl

-- §AR-host-boundary.interfaces: This exact continuation releases only the owned connection.
def runAfterState {configuration : IO.Process.StdioConfig} (child : IO.Process.Child configuration)
    (state : State) : LeanCage.Host.Program Result := do
  let state ← reap child state
  if let some fd := state.connection then close fd
  let state := if state.exitCode != some 33 then state.fail "VM ended without a complete exit" else state
  return Result.ofState state (if state.exitCode.isSome then "complete" else "unknown")

end LeanCage.Host.VirtualMachine
