import LeanCageHost.Runtime
import LeanCageHost.Transport
import LeanCageHost.Validation

namespace LeanCage.Host.VirtualMachine
open Filesystem

def diagnosticMax : Nat := 4 * 1024 * 1024

def arguments (bundle : Validation.Bundle) (directory : String) : IO.Process.SpawnArgs := {
  cmd := bundle.root ++ "/emulator/usr/bin/qemu-system-x86_64"
  args := #["-L", bundle.root ++ "/emulator/usr/share/qemu", "-no-user-config", "-nodefaults",
    "-machine", "pc,accel=tcg", "-cpu", "max", "-smp", "1", "-m", "2048M",
    "-bios", bundle.root ++ "/emulator/usr/share/seabios/bios-256k.bin", "-display", "none",
    "-monitor", "none", "-nic", "none", "-no-reboot", "-serial", "stdio",
    "-chardev", "socket,id=control,path=" ++ directory ++ "/control.sock,server=on,wait=on",
    "-serial", "chardev:control", "-device", "isa-debug-exit,iobase=0xf4,iosize=0x04",
    "-kernel", bundle.root ++ "/profile/kernel", "-initrd", directory ++ "/request.cpio",
    "-append", "console=ttyS0,115200 rdinit=/init panic=1 oops=panic loglevel=3 clocksource=acpi_pm tsc=unstable"]
  inheritEnv := false
  env := #[("PATH", some "/usr/bin:/bin"), ("LC_ALL", some "C"),
    ("LD_LIBRARY_PATH", some (bundle.root ++ "/emulator/usr/lib/x86_64-linux-gnu")),
    ("QEMU_MODULE_DIR", some (bundle.root ++ "/emulator/usr/lib/x86_64-linux-gnu/qemu"))]
  stdin := .null
  stdout := .piped
  stderr := .piped
  setsid := false }

structure State where
  transport : Transport.State
  connection : Option UInt64 := none
  channelEof : Bool := false
  controlOpen : Bool := true
  bootOpen : Bool := true
  diagnosticOpen : Bool := true
  boot : ByteArray := .empty
  diagnostic : ByteArray := .empty
  cancellation : Bool := false
  sent : Option Nat := none
  ended : Option Nat := none
  exitCode : Option UInt32 := none
  error : Option String := none

def State.fail (state : State) (message : String) : State :=
  { state with error := state.error.or (some message) }

structure Result where
  transport : Transport.State
  boot : ByteArray
  exitCode : Option UInt32
  cleanup : String
  error : Option String

def Result.ofState (state : State) (cleanup : String) : Result :=
  ⟨state.transport, state.boot, state.exitCode, cleanup, state.error⟩

def close (fd : UInt64) : LeanCage.Host.Program Unit := do
  let _ ← Runtime.perform { op := .close, first := fd }
  pure ()

-- §FS-host-boundary.ownership: Failed connection attempts relinquish their own fresh socket.
def connect (path : ByteArray) : LeanCage.Host.Program (Filesystem.Result (Option UInt64)) := do
  if path.size > 107 || !rawPathValid path then return .error "VM socket path exceeds its bound"
  let created ← Runtime.perform { op := .socket }
  let some fd := descriptor created | return .error (failure "socket" created)
  let connected ← Runtime.perform { op := .connect, first := fd, left := path }
  if connected.1 == 0 && connected.2.isEmpty then return .ok (some fd)
  let error := errorNumber connected
  close fd
  if nativeError connected && [2, 11, 111, 115].contains error then return .ok none
  return .error (failure "VM socket connect" connected)

def events (state : State) (boot diagnostic : UInt64) : List (UInt64 × Nat) :=
  (if state.controlOpen then [(3, 1)] else []) ++
  (if state.channelEof then [] else state.connection.toList.map (fun fd => (fd, 1))) ++
  (if state.bootOpen then [(boot, 1)] else []) ++
  (if state.diagnosticOpen then [(diagnostic, 1)] else [])

def collect (bytes part : ByteArray) : Except String ByteArray :=
  if bytes.size + part.size > diagnosticMax then .error "VM diagnostic bound exceeded"
  else .ok (bytes ++ part)

-- §FS-host-boundary.transport: All bytes enter their checked consumer through this actual read.
def consume (fd boot diagnostic : UInt64) (now : Nat) (state : State) :
    LeanCage.Host.Program State := do
  let budget := if fd == 3 then 1
    else if fd == boot then min chunkMax (diagnosticMax + 1 - state.boot.size)
    else if fd == diagnostic then min chunkMax (diagnosticMax + 1 - state.diagnostic.size)
    else chunkMax
  let read ← Runtime.read fd budget
  match read with
  | .error error => return state.fail error.message
  | .ok .pending => return state
  | .ok .eof =>
    if fd == 3 then return { state with cancellation := true, controlOpen := false }
    else if fd == boot then return { state with bootOpen := false }
    else if fd == diagnostic then return { state with diagnosticOpen := false }
    else return { state with
      channelEof := true
      ended := some now
      transport := state.transport.step .eof }
  | .ok (.data part) =>
    if fd == 3 then
      if part == "C".toUTF8 then return { state with cancellation := true, controlOpen := false }
      else return state.fail "invalid parent cancellation event"
    else if fd == boot then
      match collect state.boot part with
      | .error error => return state.fail error
      | .ok bytes => return { state with boot := bytes }
    else if fd == diagnostic then
      match collect state.diagnostic part with
      | .error error => return state.fail error
      | .ok bytes => return { state with diagnostic := bytes }
    else
      let transport := state.transport.step (.data part)
      match transport.error with
      | some error => return ({ state with transport } : State).fail error.message
      | none => return { state with transport }

def consumeReady : List (UInt64 × Nat) → List Nat → UInt64 → UInt64 → Nat → State →
    LeanCage.Host.Program State
  | [], [], _, _, _, state => pure state
  | (fd, _) :: rest, ready :: more, boot, diagnostic, now, state => do
    let next ← if ready == 0 then pure state else consume fd boot diagnostic now state
    if next.error.isSome then return next
    consumeReady rest more boot diagnostic now next
  | _, _, _, _, _, state => pure (state.fail "invalid VM poll event correspondence")

def deadlineError (state : State) (began duration now : Nat) : Option String :=
  if now < began then some "monotonic clock moved backwards"
  else if now - began > duration then some "VM deadline expired"
  else if state.sent.any (fun sent => now < sent || now - sent > 15000000000) then
    some "VM cancellation grace expired"
  else if state.ended.any (fun ended => now < ended || now - ended > 10000000000) then
    some "VM exit observation expired"
  else if state.connection.isNone && now - began > min duration 15000000000 then
    some "VM control channel did not open"
  else none

-- §FS-host-boundary.acceptance: Exhausted progress is explicit failure, independent of scheduling.
def loop : Nat → {configuration : IO.Process.StdioConfig} → IO.Process.Child configuration →
    ByteArray → UInt64 → UInt64 → Nat → Nat → State → LeanCage.Host.Program State
  | 0, _, _, _, _, _, _, _, state => pure (state.fail "VM made no bounded progress")
  | fuel + 1, _, child, path, boot, diagnostic, began, duration, state => do
    let observed ← LeanCage.Host.Program.effect (.tryWait child)
    let state := match observed with
      | .ok (some code) => { state with exitCode := some code }
      | .ok none => state
      | .error error => state.fail error
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

def observeExit : Nat → {configuration : IO.Process.StdioConfig} →
    IO.Process.Child configuration → LeanCage.Host.Program (Option UInt32)
  | 0, _, _ => pure none
  | fuel + 1, _, child => do
    let status ← LeanCage.Host.Program.effect (.tryWait child)
    match status with
    | .ok (some code) => return some code
    | .error _ => return none
    | .ok none =>
      let _ ← Runtime.poll [] 100
      observeExit fuel child

-- §AR-application-verification.lifetime: A signal request alone never supplies a reap observation.
def reap {configuration : IO.Process.StdioConfig} (child : IO.Process.Child configuration)
    (state : State) : LeanCage.Host.Program State := do
  if state.exitCode.isSome then return state
  let _ ← LeanCage.Host.Program.effect (.terminate child)
  let observed ← observeExit 30 child
  if observed.isSome then return { state with exitCode := observed }
  let _ ← Runtime.perform { op := .signal, first := child.pid.toUInt64, second := 9 }
  let observed ← observeExit 50 child
  return { state with exitCode := observed }

def run (bundle : Validation.Bundle) (directory : String) (duration : Nat)
    (transport : Transport.State) : LeanCage.Host.Program Result := do
  let arguments := arguments bundle directory
  let child ← LeanCage.Host.Program.effect (.spawn arguments)
  -- §FS-host-boundary.ownership: A returned spawn error does not prove that no child committed.
  let .ok child := child
    | return ⟨transport, .empty, none, "unknown", some "VM process creation failed"⟩
  let boot ← LeanCage.Host.Program.effect (.descriptor child.stdout)
  let diagnostic ← LeanCage.Host.Program.effect (.descriptor child.stderr)
  let initial : State := { transport }
  let state ← match descriptor boot, descriptor diagnostic with
    | some boot, some diagnostic => do
      let began ← Runtime.clock
      match began with
      | .error error => pure (initial.fail error.message)
      | .ok began =>
        loop (duration / 1000000 + Transport.retainedBudget transport.limits +
          2 * diagnosticMax + 1024) child (directory ++ "/control.sock").toUTF8
          boot diagnostic began duration initial
    | _, _ => pure (initial.fail "VM stream ownership could not be established")
  let state ← reap child state
  if let some fd := state.connection then close fd
  let state := if state.exitCode != some 33 then state.fail "VM ended without a complete exit" else state
  return Result.ofState state (if state.exitCode.isSome then "complete" else "unknown")

end LeanCage.Host.VirtualMachine
