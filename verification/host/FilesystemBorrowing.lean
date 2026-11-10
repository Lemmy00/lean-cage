import FilesystemDescriptors
import FilesystemPrefixes

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: Each call rule uses only that actual primitive's FD effect.
inductive BorrowPost (kernel : Contract) (fd : UInt64) (handle : Handle)
    {α : Type} (post : α → Prop) : Filesystem.Program α → Prop where
  | pure {value : α} (property : post value) : BorrowPost kernel fd handle post (.pure value)
  | call {request : Request} {next : Reply → Filesystem.Program α}
      (preserve : ∀ before after observed,
        kernel.step before request observed after → before.handles fd = some handle → after.handles fd = some handle)
      (following : ∀ before after reply,
        kernel.step before request (some reply) after → before.handles fd = some handle →
        BorrowPost kernel fd handle post (next reply)) : BorrowPost kernel fd handle post (.call request next)

theorem borrow_bind {kernel : Contract} {fd : UInt64} {handle : Handle} {α β : Type}
    {program : Filesystem.Program α} {next : α → Filesystem.Program β} {pre : α → Prop} {post : β → Prop}
    (first : BorrowPost kernel fd handle pre program)
    (tail : ∀ value, pre value → BorrowPost kernel fd handle post (next value)) :
    BorrowPost kernel fd handle post (program.bind next) := by
  induction first with
  | pure property => exact tail _ property
  | call preserve following ih => exact .call preserve (fun before after reply operation live =>
      ih before after reply operation live)

theorem borrow_weaken {kernel : Contract} {fd : UInt64} {handle : Handle} {α : Type}
    {program : Filesystem.Program α} {first last : α → Prop} (source : BorrowPost kernel fd handle first program)
    (weakening : ∀ value, first value → last value) : BorrowPost kernel fd handle last program := by
  induction source with
  | pure property => exact .pure (weakening _ property)
  | call preserve following ih => exact .call preserve ih

-- §FS-host-boundary.acceptance: Borrowed FDs survive every actual interruption/interference cut.
theorem borrow_prefix {kernel : Contract} {fd : UInt64} {handle : Handle} {α : Type}
    {program : Filesystem.Program α} {post : α → Prop} (source : BorrowPost kernel fd handle post program)
    {before after : World} {events : List (Request × Option Reply)}
    (run : PhysicalPrefix kernel program before events after) (live : before.handles fd = some handle) :
    after.handles fd = some handle := by
  induction run with
  | stop => exact live
  | environment interference tail ih =>
    apply ih source
    rw [kernel.interference_handles _ _ interference]
    exact live
  | returned operation tail ih =>
    cases source with
    | call preserve following => exact ih (following _ _ _ operation live) (preserve _ _ _ operation live)
  | lost operation => cases source with | call preserve following => exact preserve _ _ _ operation live

theorem borrow_returns {kernel : Contract} {fd : UInt64} {handle : Handle} {α : Type}
    {program : Filesystem.Program α} {post : α → Prop} (source : BorrowPost kernel fd handle post program)
    {before after : World} {events : List (Request × Reply)} {value : α}
    (run : ConcurrentRun kernel program before events after value) (live : before.handles fd = some handle) :
    after.handles fd = some handle ∧ post value := by
  rcases run with ⟨original, history⟩
  induction history generalizing program with
  | nil world =>
    cases original
    cases source with
    | pure property => exact ⟨live, property⟩
  | @cons before between after request reply events operation tail ih =>
    cases original with
    | call _ next _ _ _ continued =>
      cases source with
      | call preserve following =>
        exact ih (following _ _ _ operation live) (preserve _ _ _ operation live) continued
  | environment interference tail ih =>
    apply ih source ?_ original
    rw [kernel.interference_handles _ _ interference]
    exact live

def Successful {α : Type} (post : α → Prop) : Result α → Prop
  | .error _ => True
  | .ok value => post value

theorem passive_borrow {kernel : Contract} (descriptors : DescriptorContract kernel)
    (fd : UInt64) (handle : Handle) (request : Request) (passive : RetainsDescriptors request.op) :
    BorrowPost kernel fd handle (fun _ => True) (Filesystem.Program.effect request) := by
  apply BorrowPost.call
  · intro before after observed operation live
    rw [descriptors.retained _ _ _ _ operation passive]
    exact live
  · intro before after reply operation live
    exact .pure True.intro

theorem close_borrow {kernel : Contract} (descriptors : DescriptorContract kernel)
    (fd held : UInt64) (handle : Handle) {α : Type} (value : Result α) (different : held ≠ fd) :
    BorrowPost kernel held handle (fun result => result = value ∨ ∃ error, result = .error error)
      (closeResult fd value) := by
  apply BorrowPost.call
  · intro before after observed operation live
    rw [descriptors.close_other _ _ _ _ _ operation rfl different]
    exact live
  · intro before after reply operation live
    cases value with
    | error error => exact .pure (.inl rfl)
    | ok value =>
      dsimp only
      split
      · exact .pure (.inl rfl)
      · exact .pure (.inr ⟨_, rfl⟩)

theorem open_fresh_borrow {kernel : Contract} (descriptors : DescriptorContract kernel)
    (fd : UInt64) (handle : Handle) (request : Request) (allocating : AllocatesDescriptor request.op) :
    BorrowPost kernel fd handle (fun reply => ∀ opened,
      descriptor reply = some opened → opened ≠ fd) (Filesystem.Program.effect request) := by
  apply BorrowPost.call
  · intro before after observed operation live
    exact descriptors.allocate_existing _ _ _ _ _ _ operation allocating live
  · intro before after reply operation live
    apply BorrowPost.pure
    intro opened recognized same
    obtain ⟨fresh, _⟩ := descriptors.allocated_fresh _ _ _ _ _ operation allocating recognized
    subst opened
    rw [live] at fresh
    cases fresh

end LeanCage.Host.Kernel
