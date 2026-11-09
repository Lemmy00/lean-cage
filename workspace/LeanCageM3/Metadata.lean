import Lean

namespace LeanCageM3.Metadata

inductive Op where
  | open | read | close
  deriving DecidableEq, Repr

structure Request where
  op : Op
  fd : UInt32 := 0
  amount : UInt64 := 0
  path : String := ""
  deriving DecidableEq, Repr

abbrev Reply := UInt64 × ByteArray

structure Failure where
  operation : Op
  code : UInt32
  path : String
  deriving DecidableEq, Repr

abbrev Result := Except Failure ByteArray

-- §AR-metadata.control: The interpreter executes the control used by the proof.
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

def nativeError (reply : Reply) : Bool := 9223372036854775808 ≤ reply.1

def error (operation : Op) (path : String) (reply : Reply) : Failure :=
  let number := (0 - reply.1).toNat
  ⟨operation, (if 1 ≤ number ∧ number ≤ 4095 then number else 5).toUInt32, path⟩

def protocolError (operation : Op) (path : String) : Failure := ⟨operation, 5, path⟩

def openDescriptor (reply : Reply) : Option UInt32 :=
  if nativeError reply || !reply.2.isEmpty || reply.1.toNat > 2147483647 then none
  else some reply.1.toUInt32

def readAmount (limit size : Nat) : Nat := min 4096 (limit + 1 - size)

-- §FS-metadata.bounds: Validate the actual bytes before extending the bounded prefix.
def loop : Nat → String → UInt32 → Nat → ByteArray → Program Result
  | fuel, path, fd, limit, bytes =>
    if bytes.size > limit then pure (.ok bytes)
    else match fuel with
    | 0 => pure (.error (protocolError .read path))
    | fuel + 1 =>
      let requested := readAmount limit bytes.size
      .call ⟨.read, fd, requested.toUInt64, ""⟩ fun reply =>
        if nativeError reply then pure (.error (error .read path reply))
        else if reply.1.toNat != reply.2.size || reply.2.size > requested then
          pure (.error (protocolError .read path))
        else if reply.2.isEmpty then pure (.ok bytes)
        else loop fuel path fd limit (bytes ++ reply.2)

-- §FS-metadata.ownership: Every returning read path attempts to close its own handle.
def finish (path : String) (fd : UInt32) (result : Result) : Program Result :=
  .call ⟨.close, fd, 0, ""⟩ fun reply =>
    match result with
    | .error failure => pure (.error failure)
    | .ok bytes =>
      if reply.1 == 0 && reply.2.isEmpty then pure (.ok bytes)
      else if nativeError reply then pure (.error (error .close path reply))
      else pure (.error (protocolError .close path))

-- §AR-metadata.control: Only this program chooses the metadata descriptor and its lifetime.
def bounded (path : String) (limit : Nat) : Program Result :=
  if path.toUTF8.data.toList.contains 0 then pure (.error ⟨.open, 22, path⟩)
  else .call ⟨.open, 0, 0, path⟩ fun reply =>
    match openDescriptor reply with
    | none => pure (.error (if nativeError reply then error .open path reply else protocolError .open path))
    | some fd => (loop (limit + 1) path fd limit .empty).bind (finish path fd)

-- §AR-metadata.primitives: Evaluation without the native adapter fails with ENOSYS.
@[extern "leancage_metadata_primitive"]
def primitive (_op : UInt32) (_fd : UInt32) (_amount : UInt64) (_path : @& String) : BaseIO Reply :=
  pure (0 - 38, .empty)

def Op.code : Op → UInt32
  | .open => 0 | .read => 1 | .close => 2

def call (request : Request) : BaseIO Reply :=
  primitive request.op.code request.fd request.amount request.path

def Failure.toIOError (failure : Failure) : IO.Error :=
  .otherError failure.code s!"metadata {repr failure.operation}: {failure.path}"

def inspection (result : Result) : Except IO.Error ByteArray :=
  result.mapError Failure.toIOError

-- §FS-metadata.loss: An exception is a returned error; runtime loss returns no metadata result.
def inspect (path : String) (limit : Nat) : IO (Except IO.Error ByteArray) := do
  return inspection (← (bounded path limit).interpret (m := BaseIO) call)

def readBounded (path : System.FilePath) (limit : Nat) : IO ByteArray := do
  match ← inspect path.toString limit with
  | .ok bytes => return bytes
  | .error error => throw error

end LeanCageM3.Metadata
