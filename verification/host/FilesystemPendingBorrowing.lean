import FilesystemBorrowedOccurrences

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.acceptance: A selected current call is already a valid
-- pending prefix, independently of the reply later observed on that call.
theorem prefix_last_pending {α : Type} {program : Filesystem.Program α}
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix program (before ++ [(request, observed)])) :
    Prefix program (before ++ [(request, none)]) := by
  generalize trace : before ++ [(request, observed)] = events at source
  induction source generalizing before with
  | empty =>
    have length := congrArg List.length trace
    simp only [List.length_append, List.length_singleton, List.length_nil] at length
    omega
  | lost actual next =>
    cases before with
    | nil => cases trace; exact .lost _ _
    | cons head tail =>
      have length := congrArg List.length trace
      simp only [List.length_cons, List.length_append, List.length_nil] at length
      omega
  | returned actual next reply tail rest ih =>
    cases before with
    | nil => cases trace; exact .lost _ _
    | cons head earlier =>
      have same := List.cons.inj trace
      exact same.1 ▸ Prefix.returned actual next reply _ (ih same.2)

-- §FS-host-boundary.ownership: The current use retains its actual reference before
-- its syscall commits. Earlier returns and interleavings are replayed; no future
-- acknowledgement or cleanup result is required.
theorem borrowed_pending_reference {kernel : Contract} {origin : FilesystemOrigin} {ordinal : Nat}
    {held : UInt64} {handle : Handle} {needs : Request → Prop}
    {α : Type} {program : Filesystem.Program α}
    (source : BorrowUses kernel held handle needs program)
    {before after : World} {events : List (Request × Reply)} {request : Request}
    (active : Prefix program (Publication.completed events ++ [(request, none)]))
    (history : RecordedHistory kernel origin ordinal before events after)
    (live : before.handles held = some handle) (needed : needs request) :
    after.handles held = some handle := by
  induction history generalizing program with
  | nil =>
    cases source with
    | unused forbidden =>
      exact False.elim ((request_prefix forbidden active (request, none) (by simp [Publication.completed])) needed)
    | call preserve continuation => exact live
  | environment actual tail ih =>
    apply ih source active ?_
    rw [kernel.interference_handles _ _ actual]
    exact live
  | cons actual sampled tail ih =>
    change Prefix program ((_, some _) :: (Publication.completed _ ++ [(request, none)])) at active
    have whole := active
    cases active with
    | returned operation next reply rest following =>
      cases source with
      | unused forbidden =>
        have missing := request_prefix forbidden whole
          (request, none) (by simp [Publication.completed])
        exact False.elim (missing needed)
      | call preserve continuation =>
        exact ih (continuation _ _ _ actual live) following (preserve _ _ _ actual live)

theorem actor_borrow_recorded_prefix {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId} {held : UInt64} {handle : Handle}
    {α : Type} {program : Program α} {post : α → Prop}
    (source : ActorBorrowPost runtime actor held handle post program)
    {origin : OperationOrigin} {ordinal : Nat} {before after : World} {events : List Program.Event}
    (history : ActorHistoryWith runtime actor origin ordinal before events after)
    (active : Program.Prefix program events) (live : before.handles held = some handle) :
    after.handles held = some handle := by
  induction history generalizing program with
  | nil => exact live
  | environment actual tail ih =>
    apply ih source active
    rw [kernel.interference_handles _ _ actual]
    exact live
  | returned actual sampled tail ih =>
    cases active with
    | returned effect next reply rest following =>
      cases source with
      | call preserve continuation => exact ih (continuation _ _ _ actual live) following (preserve _ _ _ actual live)

end LeanCage.Host.Kernel

namespace LeanCage.Host.Program

-- §FS-host-boundary.acceptance: Erasing only the selected last operation
-- leaves the actual completed prefix before its entry or acknowledgement.
theorem prefix_before_last {α : Type} {program : Program α} {before : List Event} {event : Event}
    (source : Prefix program (before ++ [event])) : Prefix program before := by
  generalize trace : before ++ [event] = events at source
  induction source generalizing before with
  | empty =>
    have length := congrArg List.length trace
    simp only [List.length_append, List.length_singleton, List.length_nil] at length
    omega
  | lost actual next =>
    cases before with
    | nil => exact .empty _
    | cons head tail =>
      have length := congrArg List.length trace
      simp only [List.length_cons, List.length_append, List.length_nil] at length
      omega
  | returned actual next reply tail rest ih =>
    cases before with
    | nil => exact .empty _
    | cons head earlier =>
      have same := List.cons.inj trace
      exact same.1 ▸ Prefix.returned actual next reply _ (ih same.2)

end LeanCage.Host.Program
