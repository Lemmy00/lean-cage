import FilesystemGuardBorrowing
import FilesystemLoweringLaws
import FilesystemSourceFrames

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

theorem borrow_bind {kernel : Contract} {fd : UInt64} {handle : Handle} {α β : Type}
    {program : Filesystem.Program α} {next : α → Filesystem.Program β} {pre : α → Prop} {post : β → Prop}
    (first : BorrowPost kernel fd handle pre program.lower)
    (tail : ∀ value, pre value → BorrowPost kernel fd handle post (next value).lower) :
    BorrowPost kernel fd handle post (program.bind next).lower := by
  rw [Filesystem.Program.lower_bind]
  exact Kernel.borrow_bind first tail

theorem passive_call {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) {α : Type} {request : Request}
    {next : Reply → Filesystem.Program α} {post : α → Prop}
    (passive : RetainsDescriptors request.op)
    (following : ∀ reply, BorrowPost kernel held handle post (next reply).lower) :
    BorrowPost kernel held handle post (Filesystem.Program.call request next).lower := by
  exact Kernel.borrow_bind (guarded_passive_borrow laws held handle request passive) (fun reply _ => following reply)

theorem open_fresh_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (request : Request) (allocating : AllocatesDescriptor request.op) :
    BorrowPost kernel held handle (FreshReply held) (Filesystem.Program.effect request).lower := by
  exact Kernel.borrow_bind (guarded_open_fresh_borrow laws held handle request allocating) (fun _ fresh => .pure fresh)

-- §FS-host-boundary.ownership: A close has no path probes; all actual replies remain represented.
theorem close_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (fd held : UInt64) (handle : Handle) {α : Type} (value : Result α) (different : held ≠ fd) :
    BorrowPost kernel held handle (fun result => result = value ∨ ∃ error, result = .error error)
      (closeResult fd value).lower := by
  apply BorrowPost.call
  · intro before after observed operation live
    rw [laws.close_other _ _ _ _ _ operation rfl different]
    exact live
  · intro before after reply operation live
    cases value with
    | error error => exact .pure (.inl rfl)
    | ok value =>
      change BorrowPost kernel held handle _
        (if reply.1 == 0 && reply.2.isEmpty then
          Filesystem.Program.pure (Except.ok value : Result α)
        else Filesystem.Program.pure (Except.error (Filesystem.failure "close" reply))).lower
      split
      · exact .pure (.inl rfl)
      · exact .pure (.inr ⟨_, rfl⟩)

theorem passive_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (request : Request) (passive : RetainsDescriptors request.op) :
    BorrowPost kernel held handle (fun _ => True) (Filesystem.Program.effect request).lower := by
  exact passive_call laws held handle passive (fun _ => .pure True.intro)

-- §FS-host-boundary.snapshot: These are the actual lowered helpers, including every probe.
theorem readLoop_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (fuel : Nat) (fd : UInt64) (limit : Nat) (bytes : ByteArray) :
    BorrowPost kernel held handle (fun _ => True) (readLoop fuel fd limit bytes).lower := by
  induction fuel generalizing bytes with
  | zero => exact .pure True.intro
  | succ fuel ih =>
    unfold readLoop
    split
    · exact .pure True.intro
    · apply passive_call laws held handle (by simp [RetainsDescriptors])
      intro reply
      split
      · exact .pure True.intro
      · split
        · exact .pure True.intro
        · split
          · exact .pure True.intro
          · split
            · exact .pure True.intro
            · exact ih _

theorem copyOpened_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (fd : UInt64) (limit : Nat) :
    BorrowPost kernel held handle (fun _ => True) (copyOpened fd limit).lower := by
  unfold copyOpened
  apply passive_call laws held handle (by simp [RetainsDescriptors])
  intro reply
  split
  · exact .pure True.intro
  · split
    · exact .pure True.intro
    · apply borrow_bind (readLoop_borrow laws held handle _ _ _ _)
      intro result _
      cases result with
      | error => exact .pure True.intro
      | ok bytes =>
        apply passive_call laws held handle (by simp [RetainsDescriptors])
        intro finalReply
        split
        · exact .pure True.intro
        · split <;> exact .pure True.intro

theorem copyAt_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (parent : UInt64) (path : ByteArray) (limit : Nat) :
    BorrowPost kernel held handle (fun _ => True) (copyAt parent path limit).lower := by
  unfold copyAt
  split
  · exact .pure True.intro
  · apply borrow_bind (open_fresh_borrow laws held handle _ (.inl rfl))
    intro reply fresh
    split
    · exact .pure True.intro
    · rename_i fd recognized
      apply borrow_bind (copyOpened_borrow laws held handle fd limit)
      intro result _
      apply borrow_weaken (close_borrow laws fd held handle result (Ne.symm (fresh fd recognized)))
      intro _ _
      trivial

theorem hash_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (bytes : ByteArray) :
    BorrowPost kernel held handle (fun _ => True) (Filesystem.hash bytes).lower := by
  unfold Filesystem.hash
  apply passive_call laws held handle (by simp [RetainsDescriptors])
  intro reply
  split <;> exact .pure True.intro

end LeanCage.Host.Kernel.Lowered
