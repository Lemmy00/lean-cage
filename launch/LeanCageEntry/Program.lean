import LeanCageM3.Filter
import LeanCageM3.Policy

namespace LeanCage.Entry

-- §FS-entry.inputs: Descriptor slots carry values, rather than successful-operation labels.
structure Inputs where
  uid : UInt32
  root : String
  input : UInt32
  output : UInt32
  errors : UInt32
  failure : UInt32
  argv : Array String
  preflight : Bool
  fault : String := "normal"
  deriving Repr

def handlesValid (p : Inputs) : Bool :=
  let fds := [p.input, p.output, p.errors, p.failure]
  fds.all (fun fd => fd ≥ 4 && fd ≤ 2147483647) &&
  p.input != p.output && p.input != p.errors && p.input != p.failure &&
  p.output != p.errors && p.output != p.failure && p.errors != p.failure

def inputsValid (p : Inputs) : Bool :=
  p.uid ≥ 100000 && p.uid ≤ 100999 && handlesValid p &&
  !p.root.isEmpty && !p.root.contains '\x00' && p.root.utf8ByteSize < 160 &&
  LeanCageM3.argvValid p.argv

-- §AR-entry.effects: One request denotes one operation, with exact arguments and owned bytes.
inductive Op where
  | signalMask | signalDefault | traceMe | stop
  | dup2 | dup3 | closeRange | chroot | chdir | setsid | umask
  | prctl | setgroups | setresgid | setresuid | capset | capget
  | getresuid | getresgid | getgroups | fsuid | fsgid | filter | exec
  | write | exit | pause
  deriving Repr, DecidableEq, BEq

def Op.code : Op → UInt32
  | .signalMask => 0 | .signalDefault => 1 | .traceMe => 2 | .stop => 3
  | .dup2 => 4 | .dup3 => 5 | .closeRange => 6 | .chroot => 7 | .chdir => 8
  | .setsid => 9 | .umask => 10 | .prctl => 11 | .setgroups => 12
  | .setresgid => 13 | .setresuid => 14 | .capset => 15 | .capget => 16
  | .getresuid => 17 | .getresgid => 18 | .getgroups => 19 | .fsuid => 20
  | .fsgid => 21 | .filter => 22 | .exec => 23 | .write => 24 | .exit => 25
  | .pause => 26

structure Request where
  op : Op
  a : UInt64 := 0
  b : UInt64 := 0
  c : UInt64 := 0
  text : String := ""
  args : Array String := #[]
  data : ByteArray := .empty

abbrev Reply := UInt64 × ByteArray

inductive Expected where
  | exact (value : UInt64)
  | processId
  | fileMode
  | bytes (value : ByteArray)

def Expected.accepts : Expected → Reply → Bool
  | .exact value, (ret, _) => ret == value
  | .processId, (ret, _) => 1 ≤ ret && ret ≤ 2147483647
  | .fileMode, (ret, _) => ret ≤ 511
  | .bytes value, (ret, output) => ret == 0 && output == value

structure Command where
  request : Request
  expected : Expected := .exact 0
  stage : UInt32
  failure : UInt32

structure Failure where
  fd : UInt32
  stage : UInt32
  error : UInt32
  deriving Repr, DecidableEq, BEq

-- §FS-entry.control: Unexpected returns are terminal protocol errors, not successful setup.
def replyError (reply : Reply) : UInt32 :=
  let error := (0 : UInt64) - reply.1
  if 1 ≤ error && error ≤ 4095 then error.toUInt32 else 71

def commandFailure (command : Command) (reply : Reply) : Failure :=
  ⟨command.failure, command.stage, replyError reply⟩

def little (value : UInt64) (count : Nat) : ByteArray :=
  ⟨(List.range count).toArray.map (fun i => (value >>> (i * 8).toUInt64).toUInt8)⟩

def environment : Array String :=
  #["PATH=/usr/local/bin:/usr/bin:/bin", "LANG=C.UTF-8", "LC_ALL=C.UTF-8",
    "HOME=/workspace", "TMPDIR=/workspace/.tmp", "TZ=UTC",
    "PYTHONDONTWRITEBYTECODE=1", "PYTHONNOUSERSITE=1"]

def environmentBytes : ByteArray :=
  environment.foldl (fun bytes text => bytes ++ text.toUTF8 |>.push 0) .empty

def cmd (p : Inputs) (stage : UInt32) (request : Request)
    (expected : Expected := .exact 0) (beforeHandles : Bool := false) : Command :=
  ⟨request, expected, stage, if beforeHandles then p.failure else 3⟩

-- §FS-entry.control: The same concrete sequence is consumed by execution and the proof.
def signalSetup (p : Inputs) : List Command :=
  let early := cmd p 1 (beforeHandles := true)
  [early { op := .signalMask, a := 18446744073709551615 }] ++
  ((List.range 64).filterMap fun i =>
    let signal := i + 1
    if signal == 9 || signal == 19 then none else
      some (early { op := .signalDefault, a := signal.toUInt64 })) ++
  [early { op := .signalMask }]

def handshake (p : Inputs) : List Command :=
  let early := cmd p 1 (beforeHandles := true)
  (if p.fault == "pause_setup" then [early { op := .pause, a := 2000 }] else []) ++
  [early { op := .traceMe }, early { op := .stop }]

def handleSetup (p : Inputs) : List Command :=
  [cmd p 3 { op := .dup2, a := if p.fault == "handles_fail" then 4294967295 else p.input.toUInt64, b := 0 } (.exact 0) true,
   cmd p 3 { op := .dup2, a := p.output.toUInt64, b := 1 } (.exact 1) true,
   cmd p 3 { op := .dup2, a := p.errors.toUInt64, b := 2 } (.exact 2) true,
   cmd p 3 { op := .dup3, a := p.failure.toUInt64, b := 3, c := 524288 } (.exact 3) true,
   cmd p 3 { op := .closeRange, a := 4, b := 4294967295 }]

def rootSetup (p : Inputs) : List Command :=
  [cmd p 2 { op := .chroot, text := p.root },
   cmd p 2 { op := .chdir, text := "/workspace" },
   cmd p 2 { op := .setsid } .processId]

def credentialSetup (p : Inputs) : List Command :=
  [cmd p 4 { op := .umask, a := 63 } .fileMode,
   cmd p 4 { op := .prctl, a := 28, b := 15 }] ++
  -- §FS-entry.runtime: Linux 6.18.59 has capabilities 0..40; reject a different universe.
  [cmd p 4 { op := .prctl, a := 23, b := 41 } (.exact (0 - 22))] ++
  ((List.range 41).map fun cap => cmd p 4 { op := .prctl, a := 24, b := cap.toUInt64 }) ++
  [cmd p 4 { op := .prctl, a := 47, b := 4 },
   cmd p 4 { op := .setgroups },
   cmd p 4 { op := .setresgid, a := p.uid.toUInt64, b := p.uid.toUInt64, c := p.uid.toUInt64 },
   cmd p 4 { op := .setresuid, a := p.uid.toUInt64, b := p.uid.toUInt64, c := p.uid.toUInt64 },
   cmd p 4 { op := .capset },
   cmd p 4 { op := .capget } (.bytes (little 0 24)),
   cmd p 4 { op := .getresuid } (.bytes (little p.uid.toUInt64 4 ++ little p.uid.toUInt64 4 ++ little p.uid.toUInt64 4)),
   cmd p 4 { op := .getresgid } (.bytes (little p.uid.toUInt64 4 ++ little p.uid.toUInt64 4 ++ little p.uid.toUInt64 4)),
   cmd p 4 { op := .getgroups },
   cmd p 4 { op := .fsuid, a := 4294967295 } (.exact p.uid.toUInt64),
   cmd p 4 { op := .fsgid, a := 4294967295 } (.exact p.uid.toUInt64),
   cmd p 4 { op := .prctl, a := 4 }] ++
  (if p.fault == "credentials_fail" then
    [cmd p 4 { op := .prctl, a := 4294967295 }] else [])

def filterSetup (p : Inputs) : List Command :=
  [cmd p 5 { op := .prctl, a := 21 },
   cmd p 6 { op := .prctl, a := 38, b := if p.fault == "nnp_fail" ||
       p.fault == "error_drop" || p.fault == "error_short" then 2 else 1 },
   cmd p 7 { op := .filter, data := if p.fault == "filter_fail" then .empty else LeanCageM3.Filter.bytes }]

-- §FS-entry.control: The executing definition composes these functional setup boundaries.
def setup (p : Inputs) : List Command :=
  signalSetup p ++ handshake p ++ handleSetup p ++ rootSetup p ++
    credentialSetup p ++ filterSetup p

def execRequest (p : Inputs) : Request :=
  { op := .exec, text := if p.fault == "exec_fail" then "/nonexistent" else p.argv[0]!,
    args := p.argv, data := environmentBytes }

-- §FS-entry.control: A generic monadic implementation keeps the effectful and proof paths equal.
def runCommands {m : Type → Type} [Monad m] (call : Request → m Reply) :
    List Command → m (Option Failure)
  | [] => pure none
  | command :: rest => do
    let reply ← call command.request
    if command.expected.accepts reply then runCommands call rest
    else pure (some (commandFailure command reply))

def failureBytes (failure : Failure) : ByteArray :=
  little failure.stage.toUInt64 4 ++ little failure.error.toUInt64 4

def terminate {m : Type → Type} [Monad m] (call : Request → m Reply)
    (p : Inputs) (failure : Failure) : m UInt32 := do
  if p.fault != "error_drop" then
    let bytes := failureBytes failure
    let bytes := if p.fault == "error_short" then bytes.extract 0 3 else bytes
    let _ ← call { op := .write, a := failure.fd.toUInt64, data := bytes }
  let _ ← call { op := .exit, a := 125 }
  return 125

def finishSetup {m : Type → Type} [Monad m] (call : Request → m Reply) (p : Inputs)
    (outcome : Option Failure) : m UInt32 := do
  match outcome with
  | some failure => terminate call p failure
  | none =>
    if p.preflight then
      let _ ← call { op := .write, a := 3, data := little 0 8 }
      let _ ← call { op := .exit }
      return 0
    else
      let reply ← call (execRequest p)
      terminate call p ⟨3, 8, replyError reply⟩

def execute {m : Type → Type} [Monad m] (call : Request → m Reply) (p : Inputs) : m UInt32 := do
  if !inputsValid p then return ← terminate call p ⟨p.failure, 1, 22⟩
  let outcome ← runCommands call (setup p)
  finishSetup call p outcome

end LeanCage.Entry
