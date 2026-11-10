import FilesystemOwnership
import PublicationProofs.Writes

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: Environment writes remain distinct from application authority.
inductive WritesWithin (kernel : Contract) (allowed : ObjectId → Prop) :
    World → List (Request × Reply) → World → Prop where
  | nil (world : World) : WritesWithin kernel allowed world [] world
  | cons {before between after : World} {request : Request} {reply : Reply}
      {events : List (Request × Reply)} (operation : kernel.step before request (some reply) between)
      (target : request.op = .write → ∃ handle,
        before.handles request.first = some handle ∧ allowed handle.object)
      (tail : WritesWithin kernel allowed between events after) :
      WritesWithin kernel allowed before ((request, reply) :: events) after
  | environment {before between after : World} {events : List (Request × Reply)}
      (interference : kernel.interference before between)
      (tail : WritesWithin kernel allowed between events after) :
      WritesWithin kernel allowed before events after

theorem history_allocated {kernel : Contract} {before after : World}
    {events : List (Request × Reply)} (history : History kernel before events after)
    (object : ObjectId) (known : before.allocated object = true) : after.allocated object = true := by
  induction history with
  | nil => exact known
  | cons operation tail ih => exact ih (kernel.allocation_monotone _ _ _ _ _ operation known)
  | environment interference tail ih => exact ih (kernel.interference_allocation _ _ _ interference known)

theorem writes_append {kernel : Contract} {allowed : ObjectId → Prop} {first middle last : World}
    {before after : List (Request × Reply)}
    (initial : WritesWithin kernel allowed first before middle)
    (final : WritesWithin kernel allowed middle after last) :
    WritesWithin kernel allowed first (before ++ after) last := by
  induction initial with
  | nil => exact final
  | cons operation target tail ih => exact .cons operation target (ih final)
  | environment interference tail ih => exact .environment interference (ih final)

theorem writes_mono {kernel : Contract} {firstAllowed lastAllowed : ObjectId → Prop}
    {before after : World} {events : List (Request × Reply)}
    (run : WritesWithin kernel firstAllowed before events after)
    (inclusion : ∀ object, firstAllowed object → lastAllowed object) :
    WritesWithin kernel lastAllowed before events after := by
  induction run with
  | nil => exact .nil _
  | cons operation target tail ih =>
    apply WritesWithin.cons operation
    · intro write
      obtain ⟨handle, actual, allowed⟩ := target write
      exact ⟨handle, actual, inclusion _ allowed⟩
    · exact ih
  | environment interference tail ih => exact .environment interference ih

theorem nonwrite_history {kernel : Contract} {allowed : ObjectId → Prop} {before after : World}
    {events : List (Request × Reply)} (history : History kernel before events after)
    (readonly : ∀ event ∈ events, event.1.op ≠ .write) :
    WritesWithin kernel allowed before events after := by
  induction history with
  | nil => exact .nil _
  | @cons before between after request reply events operation tail ih =>
    exact .cons operation (fun write => False.elim (readonly (request, reply) (by simp) write))
      (ih (fun event member => readonly event (by simp [member])))
  | environment interference tail ih => exact .environment interference (ih readonly)

theorem fixed_write_history {kernel : Contract} {before after : World}
    {events : List (Request × Reply)} (history : History kernel before events after)
    (fd : UInt64) (handle : Handle) (live : before.handles fd = some handle)
    (writes : ∀ event ∈ events, event.1.op = .write ∧ event.1.first = fd) :
    WritesWithin kernel (· = handle.object) before events after := by
  induction history with
  | nil => exact .nil _
  | @cons before between after request reply events operation tail ih =>
    have head := writes (request, reply) (by simp)
    have sameFd : request.first = fd := head.2
    have retained : between.handles fd = some handle := by
      rw [kernel.write_handles _ _ _ _ operation head.1]
      exact live
    apply WritesWithin.cons operation
    · intro _
      exact ⟨handle, by rw [sameFd]; exact live, rfl⟩
    · exact ih retained (fun event member => writes event (by simp [member]))
  | environment interference tail ih =>
    apply WritesWithin.environment interference
    apply ih
    · rw [kernel.interference_handles _ _ interference]
      exact live
    · exact writes

theorem writeLoop_calls (fuel : Nat) (fd : UInt64) (bytes : ByteArray) (offset : Nat)
    {events : List (Request × Reply)} {result : Filesystem.Result Unit}
    (run : Returns (writeLoop fuel fd bytes offset) events result) :
    ∀ event ∈ events, event.1.op = .write ∧ event.1.first = fd := by
  induction fuel generalizing offset events with
  | zero => cases run; simp
  | succ fuel ih =>
    unfold writeLoop at run
    split at run
    · cases run; simp
    · obtain ⟨reply, tail, rfl, continued⟩ := Snapshot.returns_call_split run
      intro event member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨rfl, rfl⟩
      · split at continued
        · cases continued; simp at member
        · split at continued
          · cases continued; simp at member
          · exact ih _ continued event member

-- §FS-host-boundary.publication: All acknowledged partial writes retain one actual opened object.
theorem writeLoop_targets (kernel : Contract) (fuel : Nat) (fd : UInt64)
    (bytes : ByteArray) (offset : Nat) {before after : World}
    {events : List (Request × Reply)} {result : Filesystem.Result Unit} {handle : Handle}
    (run : ConcurrentRun kernel (writeLoop fuel fd bytes offset) before events after result)
    (live : before.handles fd = some handle) :
    WritesWithin kernel (· = handle.object) before events after :=
  fixed_write_history run.2 fd handle live (writeLoop_calls _ _ _ _ run.1)

theorem acknowledged_write_calls (fd : UInt64) (bytes : ByteArray) (offset : Nat)
    {events : List (Request × Reply)}
    (writes : Publication.AcknowledgedWrites fd bytes offset events) :
    ∀ event ∈ events, event.1.op = .write ∧ event.1.first = fd := by
  induction writes with
  | done => simp
  | more _ _ _ _ _ _ _ _ _ ih =>
    intro event member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨rfl, rfl⟩
    · exact ih event member

-- §FS-host-boundary.ownership: The real exclusive writer cannot modify a preexisting object.
theorem writeNew_only_fresh (kernel : Contract) (parent : UInt64) (name bytes : ByteArray)
    (mode : UInt64) {before after : World} {events : List (Request × Reply)}
    (run : ConcurrentRun kernel (writeNew parent name bytes mode) before events after (.ok ())) :
    WritesWithin kernel (fun object => before.allocated object = false) before events after := by
  obtain ⟨_, fd, opened, writing, closing, shape, descriptor, written, closed⟩ :=
    Publication.writeNew_source _ _ _ _ run.1
  have history := run.2
  rw [shape] at history
  obtain ⟨opening, created, leading, operation, tail⟩ := history_head history
  obtain ⟨object, description, fresh, _, _, _, _, live⟩ := kernel.exclusive_file _ _ _ _ _ operation rfl rfl descriptor
  have original : before.allocated object = false := by
    cases allocation : before.allocated object with
    | false => rfl
    | true =>
      have allocated := history_allocated leading object allocation
      rw [fresh] at allocated
      contradiction
  obtain ⟨writtenWorld, writes, closes⟩ := history_split writing closing tail
  have writeTargets := fixed_write_history writes fd ⟨object, description, newFileFlags, true⟩ live
    (acknowledged_write_calls _ _ _ written)
  have writesFresh : WritesWithin kernel (fun object => before.allocated object = false)
      created writing writtenWorld := writes_mono writeTargets (by
    intro selected same
    simpa only [same] using original)
  have closingRequests : ∀ event ∈ closing, event.1.op ≠ .write := by
    obtain ⟨_, reply, closeShape, _⟩ := Snapshot.closeResult_provenance _ _ closed
    rw [closeShape]
    intro event member
    have same : event = ({op := .close, first := fd}, reply) := by simpa using member
    subst event
    change Op.close ≠ Op.write
    decide
  have leadingSafe := nonwrite_history (allowed := fun object => before.allocated object = false)
    leading (by simp)
  rw [shape]
  exact writes_append leadingSafe (.cons operation (by intro impossible; cases impossible)
    (writes_append writesFresh (nonwrite_history closes closingRequests)))

end LeanCage.Host.Kernel
