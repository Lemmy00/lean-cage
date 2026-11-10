import FilesystemLoweredPaths
import FilesystemRecording

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

theorem returns_source {α : Type} (program : Filesystem.Program α)
    {events : List (Request × Reply)} {value : α} (run : Returns program.lower events value) :
    ∃ logical, Returns program logical value := by
  induction program generalizing events with
  | pure result => cases run; exact ⟨[], .pure _⟩
  | call request next ih =>
    obtain ⟨inside, reply, tail, adapter, rest, trace⟩ := adapter_returns_bind_split _ _ run
    obtain ⟨logical, source⟩ := ih reply rest
    exact ⟨(request, reply) :: logical, .call request next reply logical value source⟩

theorem close_result_identity {α : Type} (fd : UInt64) (value : Result α) :
    (closeResult fd value).lower = closeResult fd value := by
  unfold closeResult
  change Filesystem.Program.call { op := .close, first := fd } _ = Filesystem.Program.call _ _
  apply congrArg (Filesystem.Program.call { op := .close, first := fd })
  funext reply
  cases value with
  | error error => rfl
  | ok value =>
    change (if reply.1 == 0 && reply.2.isEmpty then Filesystem.Program.pure (Except.ok value : Result α)
      else Filesystem.Program.pure (Except.error (failure "close" reply))).lower = _
    split <;> rfl

theorem release_parent_identity (parent : UInt64) (child : Result UInt64) :
    (SourcePaths.releaseParent parent child).lower = SourcePaths.releaseParent parent child := by
  let next (reply : Result UInt64) : Filesystem.Program (Result UInt64) := match reply with
    | .ok fd => .pure (.ok fd)
    | .error error => match child with
      | .error _ => .pure (.error error)
      | .ok fd => closeResult fd (.error error)
  change ((closeResult parent child).bind next).lower = (closeResult parent child).bind next
  rw [Filesystem.Program.lower_bind, close_result_identity]
  apply congrArg (Filesystem.Program.bind (closeResult parent child))
  funext reply
  cases reply with
  | ok fd => rfl
  | error error =>
    cases child with
    | error original => rfl
    | ok fd => exact close_result_identity fd (.error error)

-- §AR-host-boundary.primitives: Helper splitting counts raw probe calls, not logical calls.
theorem recorded_run_bind_split {kernel : Contract} {origin : FilesystemOrigin} {ordinal : Nat} {α β : Type}
    (program : Filesystem.Program α) (next : α → Filesystem.Program β)
    {before after : World} {events : List (Request × Reply)} {result : β}
    (run : RecordedRun kernel origin ordinal (program.bind next).lower before events after result) :
    ∃ first value last middle,
      events = first ++ last ∧ RecordedRun kernel origin ordinal program.lower before first middle value ∧
      RecordedRun kernel origin (ordinal + first.length) (next value).lower middle last after result := by
  rw [Filesystem.Program.lower_bind] at run
  exact Kernel.recorded_run_bind_split _ _ run

theorem lowering_identity {α : Type} {program : Filesystem.Program α}
    (source : RequestProfile (fun request => guardedCall request = Filesystem.Program.effect request) program) :
    program.lower = program := by
  induction source with
  | pure value => rfl
  | call request next same following ih =>
    change (guardedCall request).bind (fun reply => (next reply).lower) = Filesystem.Program.call request next
    rw [same]
    exact congrArg (Filesystem.Program.call request) (funext ih)

theorem history_borrow {kernel : Contract}
    (held : UInt64) (handle : Handle) {α : Type} {program : Filesystem.Program α}
    {post : α → Prop} {origin : FilesystemOrigin} {ordinal : Nat}
    {before after : World} {events : List (Request × Reply)} {result : α}
    (source : BorrowPost kernel held handle post program.lower)
    (run : RecordedRun kernel origin ordinal program.lower before events after result)
    (live : before.handles held = some handle) : after.handles held = some handle ∧ post result :=
  borrow_returns source ⟨run.1, recorded_history_erase run.2⟩ live

end LeanCage.Host.Kernel.Lowered
