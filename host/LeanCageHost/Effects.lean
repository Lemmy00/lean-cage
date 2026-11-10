import LeanCageHost.Bytes

namespace LeanCage.Host.Filesystem

inductive Op where
  | openAt | read | write | close | stat | mkdirAt | renameNew | unlinkAt
  | random | dirOpen | dirNext | dirClose | sha256 | clock | temporary | euid
  | socket | connect | poll | socketError | setAttribute | getAttribute | workingDirectory | signal
  | authenticate | equalSecret
  | closeOnExec
  | directoryIdentity
  | selfExecutable
  | filesystemType | inodeFlags
  deriving DecidableEq, Repr

structure Request where
  op : Op
  first : UInt64 := 0
  second : UInt64 := 0
  third : UInt64 := 0
  left : ByteArray := .empty
  right : ByteArray := .empty
  deriving DecidableEq

abbrev Reply := UInt64 × ByteArray

-- §AR-host-boundary.interfaces: Execution and proofs use these same primitive requests.
inductive Program (α : Type) where
  | pure (value : α)
  | call (request : Request) (next : Reply → Program α)

def Program.bind {α β : Type} (program : Program α) (next : α → Program β) : Program β :=
  match program with
  | .pure value => next value
  | .call request rest => .call request (fun reply => (rest reply).bind next)

instance : Monad Program where
  pure := Program.pure
  bind := Program.bind

def Program.effect (request : Request) : Program Reply := .call request .pure

def Program.interpret {m : Type → Type} [Monad m] {α : Type}
    (call : Request → m Reply) : Program α → m α
  | .pure value => Pure.pure value
  | .call request next => do
    let reply ← call request
    (next reply).interpret call

def Op.code : Op → UInt32
  | .openAt => 0 | .read => 1 | .write => 2 | .close => 3 | .stat => 4
  | .mkdirAt => 5 | .renameNew => 6 | .unlinkAt => 7 | .random => 8
  | .dirOpen => 9 | .dirNext => 10 | .dirClose => 11 | .sha256 => 12
  | .clock => 13 | .temporary => 14 | .euid => 15
  | .socket => 16 | .connect => 17 | .poll => 18 | .socketError => 19
  | .setAttribute => 20 | .getAttribute => 21 | .workingDirectory => 22 | .signal => 23
  | .authenticate => 24 | .equalSecret => 25
  | .closeOnExec => 26
  | .directoryIdentity => 27
  | .selfExecutable => 28
  | .filesystemType => 29
  | .inodeFlags => 30

def nativeError (reply : Reply) : Bool := reply.1.toNat ≥ 2 ^ 63

def errorNumber (reply : Reply) : Nat :=
  let number := (0 - reply.1).toNat
  if 1 ≤ number ∧ number ≤ 4095 then number else 5

def rawPathValid (bytes : ByteArray) : Bool :=
  bytes.size ≤ 4095 && !bytes.data.toList.contains 0

def cwd : UInt64 := 0 - 100
def readFlags : UInt64 := 524288 + 131072 + 2048
def directoryFlags : UInt64 := 524288 + 131072 + 65536
def newFileFlags : UInt64 := 524288 + 131072 + 128 + 64 + 1

def Op.leftPath : Op → Bool
  | .openAt | .mkdirAt | .renameNew | .unlinkAt | .temporary | .connect
    | .setAttribute | .getAttribute => true
  | _ => false

-- §FS-host-boundary.caller: Unsupported native execution returns ENOSYS in the pure fallback.
@[extern "leancage_host_primitive"]
def primitive (_op : UInt32) (_first _second _third : UInt64)
    (_left _right : @& ByteArray) : BaseIO Reply := pure (0 - 38, .empty)

-- §FS-host-boundary.ownership: A path is terminated only after its full byte/NUL check.
def rawCall (request : Request) : BaseIO Reply := do
  if (request.op.leftPath && !rawPathValid request.left) ||
      (request.op == .renameNew && !rawPathValid request.right) then
    return (0 - 22, .empty)
  let left := if request.op.leftPath then request.left.push 0 else request.left
  let right := if request.op == .renameNew then request.right.push 0 else request.right
  primitive request.op.code request.first request.second request.third left right

namespace Lookup

def extMagic : Nat := 61267
def tmpMagic : Nat := 16914836
def casefoldFlag : Nat := 1073741824
def encryptionFlag : Nat := 2048
def unsupported : Reply := (0 - 95, .empty)

def word? (width : Nat) (reply : Reply) : Option Nat :=
  if reply.1 == 0 && reply.2.size == width then some (fromLittleEndian reply.2) else none

def extAllowed (reply : Reply) : Bool :=
  match word? 4 reply with
  | none => false
  | some flags => (flags &&& (casefoldFlag ||| encryptionFlag)) == 0

-- §FS-host-boundary.lookup: Each probe has one syscall; all acceptance decisions execute here.
def check (fd : UInt64) : Program Bool :=
  .call { op := .filesystemType, first := fd } fun observed =>
    match word? 8 observed with
    | none => pure false
    | some magic =>
      if magic == tmpMagic then pure true
      else if magic == extMagic then
        .call { op := .inodeFlags, first := fd } fun flags => pure (extAllowed flags)
      else pure false

def descriptor? (reply : Reply) : Option UInt64 :=
  if nativeError reply || !reply.2.isEmpty || reply.1.toNat > 2147483647 then none
  else some reply.1

-- §FS-host-boundary.lookup: Initial cwd/root opens and mount crossings check the returned FD.
def opened (request : Request) (reply : Reply) : Program Reply :=
  if request.op == .openAt && request.second == directoryFlags then
    match descriptor? reply with
    | none => pure reply
    | some fd => do
      let accepted ← check fd
      if accepted then return reply
      let _ ← Program.effect { op := .close, first := fd }
      return unsupported
  else pure reply

def parents (request : Request) : List UInt64 :=
  match request.op with
  | .openAt => if request.first == cwd then [] else [request.first]
  | .mkdirAt | .unlinkAt => [request.first]
  | .renameNew => [request.first, request.second]
  | .dirOpen => [request.first]
  | _ => []

def checkAll : List UInt64 → Program Bool
  | [] => pure true
  | fd :: rest => do
    let accepted ← check fd
    if accepted then checkAll rest else pure false

end Lookup

-- §FS-host-boundary.lookup: The source operation expands to this exact interruptible program.
def guardedCall (request : Request) : Program Reply := do
  let accepted ← Lookup.checkAll (Lookup.parents request)
  if !accepted then return Lookup.unsupported
  let reply ← Program.effect request
  Lookup.opened request reply

def Program.lower {α : Type} : Program α → Program α
  | .pure value => .pure value
  | .call request next => (guardedCall request).bind (fun reply => (next reply).lower)

-- §AR-host-boundary.primitives: No probe/open/close is erased from the lowered primitive program.
def call (request : Request) : BaseIO Reply := (guardedCall request).interpret rawCall

def execute {α : Type} (program : Program α) : BaseIO α := program.interpret call

-- §FS-host-boundary.acceptance: Prefixes retain arbitrary replies and a lost final call.
inductive Prefix {α : Type} : Program α → List (Request × Option Reply) → Prop where
  | empty (program : Program α) : Prefix program []
  | returned (request : Request) (next : Reply → Program α) (reply : Reply)
      (tail : List (Request × Option Reply)) (rest : Prefix (next reply) tail) :
      Prefix (.call request next) ((request, some reply) :: tail)
  | lost (request : Request) (next : Reply → Program α) :
      Prefix (.call request next) [(request, none)]

inductive Returns {α : Type} : Program α → List (Request × Reply) → α → Prop where
  | pure (value : α) : Returns (.pure value) [] value
  | call (request : Request) (next : Reply → Program α) (reply : Reply)
      (tail : List (Request × Reply)) (value : α) (rest : Returns (next reply) tail value) :
      Returns (.call request next) ((request, reply) :: tail) value

end LeanCage.Host.Filesystem
