import FilesystemRunningHistory
import FilesystemChannelWrites
import RuntimeEffects

namespace LeanCage.Host.Kernel
open Filesystem

theorem channel_borrow {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId} {held : UInt64} {handle : Handle}
    {α : Type} {program : Program α} {post : α → Prop}
    (source : ChannelWritePost runtime actor held handle post program) :
    ActorBorrowPost runtime actor held handle post program := by
  induction source with
  | pure property => exact .pure property
  | call avoid raw preserve following ih => exact .call preserve ih

theorem actor_borrow_weaken_from {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId} {held : UInt64} {handle : Handle}
    {α : Type} {program : Program α} {first post : α → Prop}
    (source : ActorBorrowPost runtime actor held handle first program)
    (weaken : ∀ value, first value → post value) : ActorBorrowPost runtime actor held handle post program := by
  induction source with
  | pure property => exact .pure (weaken _ property)
  | call preserve following ih => exact .call preserve ih

theorem runtime_only_borrow {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (raw : handle.rawOwned = true)
    {α : Type} {program : Program α} (source : Program.RuntimeOnly program) :
    ActorBorrowPost runtime actor held handle (fun _ => True) (PrimitiveFilesystem.lower program) := by
  induction source with
  | pure => exact .pure True.intro
  | call effect next allowed following ih =>
    cases effect with
    | filesystem => exact False.elim allowed
    | spawn | read | wait | terminate | tryWait | descriptor =>
      apply ActorBorrowPost.call
      · intro before after observed actual live
        exact runtime_keeps_raw sdk actor _ actual (by trivial) live raw
      · intro before after reply actual live
        exact ih reply

private theorem program_bind_associative {α β γ : Type} (first : Program α)
    (second : α → Program β) (third : β → Program γ) :
    (first.bind second).bind third = first.bind (fun value => (second value).bind third) := by
  induction first with
  | pure => rfl
  | call effect next ih => exact congrArg (Program.call effect) (funext ih)

theorem lower_source_bind {α β : Type} (first : Program α) (next : α → Program β) :
    PrimitiveFilesystem.lower (first.bind next) =
      (PrimitiveFilesystem.lower first).bind (fun value => PrimitiveFilesystem.lower (next value)) := by
  induction first with
  | pure => rfl
  | call effect continuation ih =>
    change (PrimitiveFilesystem.lowerEffect effect).bind _ =
      ((PrimitiveFilesystem.lowerEffect effect).bind _).bind _
    rw [program_bind_associative]
    exact congrArg (Program.bind (PrimitiveFilesystem.lowerEffect effect)) (funext ih)

namespace Lowered

theorem actor_bind {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId} {held : UInt64} {handle : Handle}
    {α β : Type} {program : Program α} {next : α → Program β} {first : α → Prop} {post : β → Prop}
    (source : ActorBorrowPost runtime actor held handle first (PrimitiveFilesystem.lower program))
    (tail : ∀ value, first value →
      ActorBorrowPost runtime actor held handle post (PrimitiveFilesystem.lower (next value))) :
    ActorBorrowPost runtime actor held handle post (PrimitiveFilesystem.lower (program.bind next)) := by
  rw [lower_source_bind]
  exact actor_borrow_bind source tail

theorem actor_filesystem {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (actor : ActorId) {held : UInt64} {handle : Handle}
    {α : Type} {program : Filesystem.Program α} {post : α → Prop}
    (source : BorrowPost kernel held handle post program.lower) :
    ActorBorrowPost runtime actor held handle post (PrimitiveFilesystem.lower (Program.liftFilesystem program)) := by
  rw [PrimitiveFilesystem.lower_lift_filesystem]
  exact actor_borrow_lift actor source

theorem checked_bind_borrow {kernel : Contract} (held : UInt64) (handle : Handle)
    {α β : Type} (first : ExceptT Failure Filesystem.Program α)
    (next : α → ExceptT Failure Filesystem.Program β)
    (source : BorrowPost kernel held handle (fun _ => True) first.run.lower)
    (tail : ∀ value, BorrowPost kernel held handle (fun _ => True) (next value).run.lower) :
    BorrowPost kernel held handle (fun _ => True) ((first >>= next).run).lower := by
  change BorrowPost kernel held handle (fun _ => True) (first.run.bind (ExceptT.bindCont next)).lower
  rw [Filesystem.Program.lower_bind]
  apply Kernel.borrow_bind source
  intro result _
  cases result with
  | error => exact .pure True.intro
  | ok value => exact tail value

end Lowered

-- §FS-host-boundary.caller: Forward reference preservation uses the actual actor's
-- completed source prefix. It needs neither a future return nor a current-reference premise.
theorem actor_borrow_history {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId} {held : UInt64} {handle : Handle}
    {α : Type} {program current : Program α} {post : α → Prop}
    (source : ActorBorrowPost runtime actor held handle post program)
    {origin : OperationOrigin} {ordinal : Nat} {before after : World} {events : List Program.Event}
    (history : ActorHistoryWith runtime actor origin ordinal before events after)
    (reached : Residual program events current) (live : before.handles held = some handle) :
    after.handles held = some handle ∧ ActorBorrowPost runtime actor held handle post current := by
  induction history generalizing program with
  | nil => cases reached; exact ⟨live, source⟩
  | environment actual tail ih =>
    apply ih source reached
    rw [kernel.interference_handles _ _ actual]
    exact live
  | returned actual sampled tail ih =>
    cases reached with
    | call residual =>
      cases source with
      | call preserve following =>
        exact ih (following _ _ _ actual live) residual (preserve _ _ _ actual live)

-- §FS-host-boundary.acceptance: At a live source head the inherited reference is produced
-- from this exact handoff/history, even if a later exit has already retired its resources.
theorem selected_borrowed_reference {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState}
    (history : SelectedActorHistory runtime initial all tick actor engine)
    {held : UInt64} {handle : Handle}
    (source : ActorBorrowPost runtime actor held handle (fun _ => True) sourceProgram)
    (reached : Residual sourceProgram engine.events engine.current)
    (inherited : history.launch.references held = some handle) :
    engine.references held = some handle ∧
      ActorBorrowPost runtime actor held handle (fun _ => True) engine.current := by
  exact actor_borrow_history source history.history reached inherited

end LeanCage.Host.Kernel
