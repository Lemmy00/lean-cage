import ProgramProofs
import FilesystemAccessProofs.Phases
import LeanCageHost.Entrypoint

namespace LeanCage.Host.PrimitiveFilesystem

-- §AR-host-boundary.interfaces: Runtime effects stay unchanged; filesystem effects expand once.
def lowerEffect {α : Type} : Effect α → Program α
  | .filesystem request => Program.liftFilesystem (Filesystem.guardedCall request)
  | other => Program.effect other

def lower {α : Type} : Program α → Program α
  | .pure value => .pure value
  | .call effect next => (lowerEffect effect).bind (fun reply => lower (next reply))

def primitiveEffect {α : Type} : Effect α → IO α
  | .filesystem request => return ← Filesystem.rawCall request
  | other => other.interpret

def interpret {α : Type} : Program α → IO α
  | .pure value => pure value
  | .call effect next => do
    let reply ← primitiveEffect effect
    interpret (next reply)

private theorem io_bind_assoc {α β γ : Type} (first : IO α) (second : α → IO β)
    (third : β → IO γ) : (first >>= second) >>= third = first >>= (fun value => second value >>= third) := by
  funext state
  change EST.bind (EST.bind first second) third state =
    EST.bind first (fun value => EST.bind (second value) third) state
  simp only [EST.bind]
  cases first state <;> rfl

private theorem io_bind_pure {α : Type} (first : IO α) : first >>= pure = first := by
  funext state
  change EST.bind first EST.pure state = first state
  simp only [EST.bind]
  cases first state <;> rfl

private theorem lift_bind {α β : Type} (first : BaseIO α) (second : α → BaseIO β) :
    BaseIO.toIO (first >>= second) = (BaseIO.toIO first >>= fun value => BaseIO.toIO (second value)) := by
  funext state
  cases first state
  rfl

private theorem interpret_bind {α β : Type} (program : Program α) (next : α → Program β) :
    interpret (program.bind next) = (interpret program >>= fun value => interpret (next value)) := by
  induction program with
  | pure value => rfl
  | call effect continuation ih =>
    change (primitiveEffect effect >>= fun reply => interpret ((continuation reply).bind next)) =
      (primitiveEffect effect >>= fun reply => interpret (continuation reply)) >>= fun value => interpret (next value)
    rw [io_bind_assoc]
    exact congrArg (fun rest => primitiveEffect effect >>= rest) (funext ih)

theorem lift_filesystem_source {α : Type} (program : Filesystem.Program α) :
    interpret (Program.liftFilesystem program) = BaseIO.toIO (program.interpret Filesystem.rawCall) := by
  induction program with
  | pure value => rfl
  | call request next ih =>
    change ((return ← Filesystem.rawCall request) >>= fun reply => interpret (Program.liftFilesystem (next reply))) =
      BaseIO.toIO (Filesystem.rawCall request >>= fun reply => (next reply).interpret Filesystem.rawCall)
    rw [lift_bind]
    have first : (return ← Filesystem.rawCall request) = BaseIO.toIO (Filesystem.rawCall request) := by
      funext state
      cases Filesystem.rawCall request state
      rfl
    rw [first]
    exact congrArg (fun rest => BaseIO.toIO (Filesystem.rawCall request) >>= rest) (funext ih)

-- §AR-host-boundary.primitives: This equality names the actual Effect.interpret filesystem arm.
theorem filesystem_effect_source (request : Filesystem.Request) :
    Effect.interpret (.filesystem request) =
      BaseIO.toIO ((Filesystem.guardedCall request).interpret Filesystem.rawCall) := by
  funext state
  cases (Filesystem.guardedCall request).interpret Filesystem.rawCall state
  rfl

theorem lower_effect_source {α : Type} (effect : Effect α) :
    effect.interpret = interpret (lowerEffect effect) := by
  cases effect with
  | filesystem request =>
    rw [lowerEffect, lift_filesystem_source]
    exact filesystem_effect_source request
  | spawn arguments | read handle amount | wait child | terminate child | tryWait child | descriptor handle =>
    exact (io_bind_pure _).symm

theorem application_source {α : Type} (program : Program α) : program.interpret = interpret (lower program) := by
  induction program with
  | pure value => rfl
  | call effect next ih =>
    change (effect.interpret >>= fun reply => (next reply).interpret) =
      interpret ((lowerEffect effect).bind (fun reply => lower (next reply)))
    rw [interpret_bind, ← lower_effect_source]
    exact congrArg (fun rest => effect.interpret >>= rest) (funext ih)

theorem entrypoint_source : Entrypoint.run.interpret = interpret (lower Entrypoint.run) :=
  application_source Entrypoint.run

-- §FS-host-boundary.acceptance: A source effect keeps its entire active primitive prefix.
inductive Prefix {α : Type} : Program α → List Program.Event → List Program.Event → Prop where
  | stop (program : Program α) : Prefix program [] []
  | active {β : Type} (effect : Effect β) (next : β → Program α) (inside : List Program.Event)
      (source : Program.Prefix (lowerEffect effect) inside) : Prefix (.call effect next) [.lost effect] inside
  | completed {β : Type} (effect : Effect β) (next : β → Program α) (reply : β)
      (inside logical tail : List Program.Event) (adapter : Program.Returns (lowerEffect effect) inside reply)
      (rest : Prefix (next reply) logical tail) :
      Prefix (.call effect next) (.returned effect reply :: logical) (inside ++ tail)

theorem lowered_prefix_source {α : Type} (program : Program α) {raw : List Program.Event}
    (source : Program.Prefix (lower program) raw) : ∃ logical, Prefix program logical raw := by
  induction program generalizing raw with
  | pure value => cases source; exact ⟨[], .stop _⟩
  | call effect next ih =>
    change Program.Prefix ((lowerEffect effect).bind (fun reply => lower (next reply))) raw at source
    rcases Program.prefix_bind_split _ _ source with active | ⟨first, reply, last, adapter, rest, shape⟩
    · exact ⟨_, .active effect next raw active⟩
    · obtain ⟨logical, refined⟩ := ih reply rest
      rw [shape]
      exact ⟨_, .completed effect next reply first logical last adapter refined⟩

theorem logical_prefix_source {α : Type} {program : Program α} {logical raw : List Program.Event}
    (source : Prefix program logical raw) : Program.Prefix program logical := by
  induction source with
  | stop program => exact .empty _
  | active effect next inside actual => exact .lost _ _
  | completed effect next reply inside logical tail adapter rest ih => exact .returned effect next reply logical ih

end LeanCage.Host.PrimitiveFilesystem
