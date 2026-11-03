import LeanCageEntry.Program

namespace LeanCage.Entry

-- §AR-entry.effects: Reify the executing control, including every possible primitive return.
inductive Script (α : Type) where
  | pure (value : α)
  | call (request : Request) (next : Reply → Script α)

def Script.bind {α β : Type} (program : Script α) (next : α → Script β) : Script β :=
  match program with
  | .pure value => next value
  | .call request rest => .call request (fun reply => (rest reply).bind next)

instance : Monad Script where
  pure := Script.pure
  bind := Script.bind

def Script.effect (request : Request) : Script Reply := .call request .pure

-- §FS-entry.control: Interpretation only performs the request chosen by the shared Lean program.
def Script.interpret {m : Type → Type} [Monad m] {α : Type}
    (call : Request → m Reply) : Script α → m α
  | .pure value => Pure.pure value
  | .call request next => do
    let reply ← call request
    (next reply).interpret call

-- §FS-entry.control: External loss is a stopped prefix, not a fabricated successful reply.
inductive Script.Prefix {α : Type} : Script α → List (Request × Reply) → Script α → Prop
  | refl (program : Script α) : Prefix program [] program
  | step (request : Request) (next : Reply → Script α) (reply : Reply)
      {trace : List (Request × Reply)} {last : Script α}
      (rest : Prefix (next reply) trace last) :
      Prefix (.call request next) ((request, reply) :: trace) last

def admission (p : Inputs) : Script UInt32 := execute Script.effect p

end LeanCage.Entry
