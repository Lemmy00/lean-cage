import FilesystemSourceFrames
import RunDirectoryProofs.Cleanup

namespace LeanCage.Host.Kernel
open Filesystem

def KeepsReference (fd : UInt64) (request : Request) : Prop :=
  request.op ≠ .dirClose ∧ (request.op = .close → fd ≠ request.first)

theorem syscall_keeps_reference {kernel : Contract} (laws : DescriptorContract kernel)
    {before after : World} {request : Request} {observed : Option Reply} {fd : UInt64} {handle : Handle}
    (actual : kernel.step before request observed after) (keeps : KeepsReference fd request)
    (live : before.handles fd = some handle) : after.handles fd = some handle := by
  by_cases allocating : AllocatesDescriptor request.op
  · exact laws.allocate_existing _ _ _ _ _ _ actual allocating live
  · by_cases closing : request.op = .close
    · rw [laws.close_other _ _ _ _ _ actual closing (keeps.2 closing)]; exact live
    · have passive : RetainsDescriptors request.op := by
        unfold AllocatesDescriptor at allocating
        simp only [RetainsDescriptors]
        exact ⟨fun h => allocating (.inl h), fun h => allocating (.inr (.inl h)),
          fun h => allocating (.inr (.inr h)), closing, keeps.1⟩
      rw [laws.retained _ _ _ _ actual passive]
      exact live

-- §FS-host-boundary.ownership: Once a scope ends, source must contain no later use of that
-- resource.
inductive BorrowUses (kernel : Contract) (fd : UInt64) (handle : Handle) (needs : Request → Prop)
    {α : Type} : Filesystem.Program α → Prop where
  | unused {program : Filesystem.Program α}
      (source : RequestProgram (fun request => ¬ needs request) program) : BorrowUses kernel fd handle needs program
  | call {request : Request} {next : Reply → Filesystem.Program α}
      (preserve : ∀ before after observed, kernel.step before request observed after →
        before.handles fd = some handle → after.handles fd = some handle)
      (following : ∀ before after reply, kernel.step before request (some reply) after →
        before.handles fd = some handle → BorrowUses kernel fd handle needs (next reply)) :
      BorrowUses kernel fd handle needs (.call request next)

theorem borrow_then_uses {kernel : Contract} {fd : UInt64} {handle : Handle} {needs : Request → Prop}
    {α β : Type} {program : Filesystem.Program α} {next : α → Filesystem.Program β} {post : α → Prop}
    (first : BorrowPost kernel fd handle post program)
    (tail : ∀ value, post value → BorrowUses kernel fd handle needs (next value)) :
    BorrowUses kernel fd handle needs (program.bind next) := by
  induction first with
  | pure property => exact tail _ property
  | call preserve following ih => exact .call preserve ih

inductive PrefixResource (kernel : Contract) (fd : UInt64) (handle : Handle) (needs : Request → Prop) :
    World → List (Request × Option Reply) → World → Prop where
  | nil (world : World) : PrefixResource kernel fd handle needs world [] world
  | environment {before between after : World} {events : List (Request × Option Reply)}
      (interference : kernel.interference before between)
      (tail : PrefixResource kernel fd handle needs between events after) :
      PrefixResource kernel fd handle needs before events after
  | returned {before between after : World} {request : Request} {reply : Reply}
      {events : List (Request × Option Reply)} (actual : kernel.step before request (some reply) between)
      (resource : needs request → before.handles fd = some handle)
      (tail : PrefixResource kernel fd handle needs between events after) :
      PrefixResource kernel fd handle needs before ((request, some reply) :: events) after
  | lost {before after : World} {request : Request} (actual : kernel.step before request none after)
      (resource : needs request → before.handles fd = some handle) :
      PrefixResource kernel fd handle needs before [(request, none)] after

theorem no_resource_prefix {kernel : Contract} {fd : UInt64} {handle : Handle} {needs : Request → Prop}
    {α : Type} {program : Filesystem.Program α} {before after : World} {events : List (Request × Option Reply)}
    (source : RequestProgram (fun request => ¬ needs request) program)
    (run : PhysicalPrefix kernel program before events after) : PrefixResource kernel fd handle needs before events after := by
  induction run with
  | stop => exact .nil _
  | environment interference tail ih => exact .environment interference (ih source)
  | returned actual tail ih =>
    cases source with
    | call notNeeded following =>
      exact .returned actual (fun needed => False.elim (notNeeded needed)) (ih (following _))
  | lost actual =>
    cases source with
    | call notNeeded following => exact .lost actual (fun needed => False.elim (notNeeded needed))

-- §FS-host-boundary.acceptance: Every selected use precedes its source release, even under loss.
theorem borrowed_use_prefix {kernel : Contract} {fd : UInt64} {handle : Handle} {needs : Request → Prop}
    {α : Type} {program : Filesystem.Program α} (source : BorrowUses kernel fd handle needs program)
    {before after : World} {events : List (Request × Option Reply)}
    (run : PhysicalPrefix kernel program before events after) (live : before.handles fd = some handle) :
    PrefixResource kernel fd handle needs before events after := by
  induction run with
  | stop => exact .nil _
  | environment interference tail ih =>
    apply PrefixResource.environment interference
    apply ih source
    rw [kernel.interference_handles _ _ interference]
    exact live
  | returned actual tail ih =>
    cases source with
    | unused none => exact no_resource_prefix none (.returned actual tail)
    | call preserve following =>
      exact .returned actual (fun _ => live) (ih (following _ _ _ actual live) (preserve _ _ _ actual live))
  | lost actual =>
    cases source with
    | unused none => exact no_resource_prefix none (.lost actual)
    | call preserve following => exact .lost actual (fun _ => live)

def callScript : List Request → Filesystem.Program Unit
  | [] => .pure ()
  | request :: rest => .call request fun _ => callScript rest

def cleanupScript (owned : RunDirectory.Owned) : List Request := [
  {op := .unlinkAt, first := owned.directory.fd, left := "request.cpio".toUTF8},
  {op := .unlinkAt, first := owned.directory.fd, left := "control.sock".toUTF8},
  {op := .unlinkAt, first := owned.directory.fd, left := "policy.json".toUTF8},
  {op := .close, first := owned.directory.fd},
  {op := .unlinkAt, first := owned.container.fd, second := 512, left := owned.name},
  {op := .close, first := owned.container.fd}]

theorem cleanup_script (owned : RunDirectory.Owned) : RunDirectory.cleanup owned = callScript (cleanupScript owned) := rfl

def UnlinksThrough (fd : UInt64) (request : Request) : Prop := request.op = .unlinkAt ∧ request.first = fd

private theorem script_unused (fd : UInt64) (handle : Handle) {kernel : Contract} (requests : List Request)
    (none : ∀ request ∈ requests, ¬ UnlinksThrough fd request) :
    BorrowUses kernel fd handle (UnlinksThrough fd) (callScript requests) := by
  apply BorrowUses.unused
  induction requests with
  | nil => exact .pure _
  | cons request rest ih => exact .call (none _ (by simp)) (fun _ => ih (by
      intro query member; exact none query (by simp [member])))

private theorem script_keep {kernel : Contract} (laws : DescriptorContract kernel)
    (fd : UInt64) (handle : Handle) (request : Request) (rest : List Request)
    (keeps : KeepsReference fd request)
    (tail : BorrowUses kernel fd handle (UnlinksThrough fd) (callScript rest)) :
    BorrowUses kernel fd handle (UnlinksThrough fd) (callScript (request :: rest)) :=
  .call (fun _ _ _ actual live => syscall_keeps_reference laws actual keeps live) (fun _ _ _ _ _ => tail)

theorem cleanup_directory_uses {kernel : Contract} (laws : DescriptorContract kernel)
    (owned : RunDirectory.Owned) (handle : Handle) (distinct : owned.directory.fd ≠ owned.container.fd) :
    BorrowUses kernel owned.directory.fd handle (UnlinksThrough owned.directory.fd) (RunDirectory.cleanup owned) := by
  rw [cleanup_script]
  unfold cleanupScript
  apply script_keep laws _ _ _ _ (by simp [KeepsReference])
  apply script_keep laws _ _ _ _ (by simp [KeepsReference])
  apply script_keep laws _ _ _ _ (by simp [KeepsReference])
  apply script_unused
  intro request member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [UnlinksThrough, Ne.symm distinct]

theorem cleanup_container_uses {kernel : Contract} (laws : DescriptorContract kernel)
    (owned : RunDirectory.Owned) (handle : Handle) (distinct : owned.directory.fd ≠ owned.container.fd) :
    BorrowUses kernel owned.container.fd handle (UnlinksThrough owned.container.fd) (RunDirectory.cleanup owned) := by
  rw [cleanup_script]
  unfold cleanupScript
  apply script_keep laws _ _ _ _ (by simp [KeepsReference])
  apply script_keep laws _ _ _ _ (by simp [KeepsReference])
  apply script_keep laws _ _ _ _ (by simp [KeepsReference])
  apply script_keep laws _ _ _ _ (by simpa [KeepsReference] using Ne.symm distinct)
  apply script_keep laws _ _ _ _ (by simp [KeepsReference])
  exact script_unused _ _ _ (by intro request member; rcases List.mem_singleton.mp member with rfl; simp [UnlinksThrough])

end LeanCage.Host.Kernel
