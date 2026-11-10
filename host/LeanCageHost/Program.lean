import Lean
import LeanCageHost.Files

namespace LeanCage.Host

-- §AR-host-boundary.interfaces: Each constructor names one specified runtime operation.
inductive Effect : Type → Type where
  | filesystem (request : Filesystem.Request) : Effect Filesystem.Reply
  | spawn (arguments : IO.Process.SpawnArgs) :
      Effect (Except String (IO.Process.Child arguments.toStdioConfig))
  | read (handle : IO.FS.Handle) (amount : Nat) : Effect (Except String ByteArray)
  | wait {configuration : IO.Process.StdioConfig} (child : IO.Process.Child configuration) :
      Effect (Except String UInt32)
  | terminate {configuration : IO.Process.StdioConfig} (child : IO.Process.Child configuration) :
      Effect (Except String Unit)
  | tryWait {configuration : IO.Process.StdioConfig} (child : IO.Process.Child configuration) :
      Effect (Except String (Option UInt32))
  | descriptor (handle : IO.FS.Handle) : Effect Filesystem.Reply

-- §AR-host-boundary.primitives: A borrowed stream descriptor retains its runtime handle owner.
@[extern "leancage_host_handle_descriptor"]
def streamDescriptor (_handle : @& IO.FS.Handle) : BaseIO Filesystem.Reply :=
  pure (0 - 38, .empty)

inductive Program (α : Type) where
  | pure (value : α)
  | call {β : Type} (effect : Effect β) (next : β → Program α)

def Program.bind {α β : Type} (program : Program α) (next : α → Program β) : Program β :=
  match program with
  | .pure value => next value
  | .call effect rest => .call effect (fun reply => (rest reply).bind next)

instance : Monad Program where
  pure := Program.pure
  bind := Program.bind

def Program.liftFilesystem {α : Type} : Filesystem.Program α → Program α
  | .pure value => .pure value
  | .call request next => .call (.filesystem request) (fun reply => Program.liftFilesystem (next reply))

def Program.effect {α : Type} (effect : Effect α) : Program α := .call effect .pure

-- §FS-host-boundary.transport: Native length conversion follows its positive bounded guard.
def Effect.interpret {α : Type} : Effect α → IO α
  | .filesystem request => return ← Filesystem.call request
  | .spawn arguments => do
    try return .ok (← IO.Process.spawn arguments)
    catch _ => return .error "host process creation failed"
  | .read handle amount => do
    if amount == 0 || amount > chunkMax then return .error "invalid host stream read bound"
    try
      let bytes ← handle.read amount.toUSize
      if bytes.size > amount then return .error "host stream exceeded requested read bound"
      return .ok bytes
    catch _ => return .error "host stream read failed"
  | .wait child => do
    try return .ok (← child.wait)
    catch _ => return .error "host process wait failed"
  | .terminate child => do
    try child.kill; return .ok ()
    catch _ => return .error "host process cancellation failed"
  | .tryWait child => do
    try return .ok (← child.tryWait)
    catch _ => return .error "host process observation failed"
  | .descriptor handle => return ← streamDescriptor handle

def Program.interpret {α : Type} : Program α → IO α
  | .pure value => Pure.pure value
  | .call effect next => do
    let reply ← effect.interpret
    (next reply).interpret

-- §FS-host-boundary.transport: Check returned bytes before extending the retained prefix.
def readStream : Nat → IO.FS.Handle → Nat → ByteArray → Program (Except String ByteArray)
  | 0, _, _, _ => pure (.error "host stream made no bounded progress")
  | fuel + 1, handle, limit, bytes =>
    if bytes.size > limit then pure (.error "host stream byte bound exceeded")
    else .call (.read handle (min chunkMax (limit + 1 - bytes.size))) fun reply =>
      match reply with
      | .error error => pure (.error error)
      | .ok part =>
        if part.size > min chunkMax (limit + 1 - bytes.size) then
          pure (.error "host stream returned invalid bytes")
        else if part.isEmpty then pure (.ok bytes)
        else if bytes.size + part.size > limit then pure (.error "host stream byte bound exceeded")
        else readStream fuel handle limit (bytes ++ part)

end LeanCage.Host
