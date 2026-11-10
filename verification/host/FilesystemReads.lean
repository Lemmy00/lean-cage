import FilesystemMarkers
import RunDirectoryProofs.Requests

namespace LeanCage.Host.Kernel
open Filesystem

def ReadsDescriptor (fd : UInt64) (request : Request) : Prop := request.op = .read → request.first = fd

theorem readLoop_reads_descriptor (fuel : Nat) (fd : UInt64) (limit : Nat) (bytes : ByteArray) :
    RequestProgram (ReadsDescriptor fd) (readLoop fuel fd limit bytes) := by
  induction fuel generalizing bytes with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold readLoop
    split
    · exact .pure _
    · apply RequestProgram.call (fun _ => rfl)
      intro reply
      split
      · exact .pure _
      · split
        · exact .pure _
        · split
          · exact .pure _
          · split
            · exact .pure _
            · exact ih _

theorem copyOpened_reads_descriptor (fd : UInt64) (limit : Nat) :
    RequestProgram (ReadsDescriptor fd) (copyOpened fd limit) := by
  unfold copyOpened
  apply RequestProgram.call (by intro impossible; cases impossible)
  intro reply
  split
  · exact .pure _
  · split
    · exact .pure _
    · apply request_bind (readLoop_reads_descriptor _ _ _ _)
      intro result
      cases result with
      | error => exact .pure _
      | ok bytes =>
        apply RequestProgram.call (by intro impossible; cases impossible)
        intro finalReply
        split
        · exact .pure _
        · split <;> exact .pure _

inductive PrefixReads (kernel : Contract) (allowed : ObjectId → Prop) :
    World → List (Request × Option Reply) → World → Prop where
  | nil (world : World) : PrefixReads kernel allowed world [] world
  | environment {before between after : World} {events : List (Request × Option Reply)}
      (interference : kernel.interference before between) (tail : PrefixReads kernel allowed between events after) :
      PrefixReads kernel allowed before events after
  | returned {before between after : World} {request : Request} {reply : Reply}
      {events : List (Request × Option Reply)} (operation : kernel.step before request (some reply) between)
      (target : request.op = .read → ∃ handle, before.handles request.first = some handle ∧ allowed handle.object)
      (tail : PrefixReads kernel allowed between events after) :
      PrefixReads kernel allowed before ((request, some reply) :: events) after
  | lost {before after : World} {request : Request} (operation : kernel.step before request none after)
      (target : request.op = .read → ∃ handle, before.handles request.first = some handle ∧ allowed handle.object) :
      PrefixReads kernel allowed before [(request, none)] after

-- §FS-host-boundary.snapshot: A source guard and borrowed reference control every possible read.
theorem borrowed_reads {kernel : Contract} {α : Type} {program : Filesystem.Program α}
    {post : α → Prop} {fd : UInt64} {handle : Handle} {allowed : ObjectId → Prop}
    (borrowing : BorrowPost kernel fd handle post program) (source : RequestProgram (ReadsDescriptor fd) program)
    {before after : World} {events : List (Request × Option Reply)}
    (run : PhysicalPrefix kernel program before events after) (live : before.handles fd = some handle)
    (objectAllowed : allowed handle.object) : PrefixReads kernel allowed before events after := by
  induction run with
  | stop => exact .nil _
  | environment interference tail ih =>
    apply PrefixReads.environment interference
    apply ih borrowing source
    rw [kernel.interference_handles _ _ interference]
    exact live
  | @returned request next reply before between after events operation tail ih =>
    cases borrowing with
    | call preserve following =>
      cases source with
      | call descriptor remaining =>
        apply PrefixReads.returned operation
        · intro read
          exact ⟨handle, by rw [descriptor read]; exact live, objectAllowed⟩
        · exact ih (following _ _ _ operation live) (remaining reply) (preserve _ _ _ operation live)
  | @lost request next before after operation =>
    cases source with
    | call descriptor remaining =>
      apply PrefixReads.lost operation
      intro read
      exact ⟨handle, by rw [descriptor read]; exact live, objectAllowed⟩

-- §FS-host-boundary.publication: A caller copy cannot expose the guarded private-key object.
theorem guarded_copy_never_reads_key {kernel : Contract} (laws : DescriptorContract kernel)
    (fd : UInt64) (handle : Handle) (limit : Nat) (key : ObjectId)
    {before after : World} {events : List (Request × Option Reply)}
    (run : PhysicalPrefix kernel (copyOpened fd limit) before events after)
    (live : before.handles fd = some handle) (different : handle.object ≠ key) :
    PrefixReads kernel (· ≠ key) before events after :=
  borrowed_reads (copyOpened_borrow laws fd handle fd limit) (copyOpened_reads_descriptor fd limit) run live different

end LeanCage.Host.Kernel
