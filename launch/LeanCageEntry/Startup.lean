import LeanCageEntry.Script

namespace LeanCage.Entry

-- §FS-entry.runtime: Reify the real startup guards as well as admission effects.
inductive Startup (α : Type) where
  | pure (value : α)
  | inspect (path : String) (limit : Nat) (next : Except IO.Error ByteArray → Startup α)
  | call (request : Request) (next : Reply → Startup α)

def Startup.bind {α β : Type} (program : Startup α) (next : α → Startup β) : Startup β :=
  match program with
  | .pure value => next value
  | .inspect path limit rest => .inspect path limit (fun reply => (rest reply).bind next)
  | .call request rest => .call request (fun reply => (rest reply).bind next)

instance : Monad Startup where
  pure := Startup.pure
  bind := Startup.bind

def Startup.read (path : String) (limit : Nat) : Startup (Except IO.Error ByteArray) :=
  .inspect path limit .pure

def Startup.admission {α : Type} : Script α → Startup α
  | .pure value => .pure value
  | .call request next => .call request (fun reply => Startup.admission (next reply))

-- §AR-entry.effects: The interpreter executes only the operation selected by shared control.
def Startup.interpret {α : Type}
    (read : String → Nat → IO (Except IO.Error ByteArray))
    (call : Request → IO Reply) : Startup α → IO α
  | .pure value => Pure.pure value
  | .inspect path limit next => do
    let reply ← read path limit
    (next reply).interpret read call
  | .call request next => do
    let reply ← call request
    (next reply).interpret read call

end LeanCage.Entry
