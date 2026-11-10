import FilesystemBorrowing
import FilesystemAccessProofs.Profiles

namespace LeanCage.Host.Kernel
open Filesystem

def FreshReply (held : UInt64) (reply : Reply) : Prop :=
  ∀ opened, descriptor reply = some opened → opened ≠ held

theorem denied_reply_fresh (held : UInt64) : FreshReply held Lookup.unsupported := by
  have rejected : descriptor Lookup.unsupported = none := by decide
  intro opened recognized
  rw [rejected] at recognized
  cases recognized

-- §FS-host-boundary.lookup: Every added query uses its own actual descriptor-retention law.
theorem lookup_check_borrow {kernel : Contract} (descriptors : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (fd : UInt64) :
    BorrowPost kernel held handle (fun _ => True) (Lookup.check fd) := by
  unfold Lookup.check
  apply BorrowPost.call
  · intro before after observed actual live
    rw [descriptors.retained _ _ _ _ actual (by simp [RetainsDescriptors])]
    exact live
  · intro before after reply actual live
    split
    · exact .pure True.intro
    · split
      · exact .pure True.intro
      · split
        · apply BorrowPost.call
          · intro before after observed actual live
            rw [descriptors.retained _ _ _ _ actual (by simp [RetainsDescriptors])]
            exact live
          · intro before after reply actual live
            exact .pure True.intro
        · exact .pure True.intro

theorem lookup_all_borrow {kernel : Contract} (descriptors : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (fds : List UInt64) :
    BorrowPost kernel held handle (fun _ => True) (Lookup.checkAll fds) := by
  induction fds with
  | nil => exact .pure True.intro
  | cons fd rest ih =>
    unfold Lookup.checkAll
    apply borrow_bind (lookup_check_borrow descriptors held handle fd)
    intro accepted property
    split
    · exact ih
    · exact .pure True.intro

-- §FS-host-boundary.ownership: Rejection closes only the newly returned open descriptor. Its
-- inequality with an existing borrowed descriptor comes from the actual successful open.
theorem lookup_opened_borrow {kernel : Contract} (descriptors : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (request : Request) (reply : Reply)
    (fresh : FreshReply held reply) :
    BorrowPost kernel held handle (FreshReply held) (Lookup.opened request reply) := by
  unfold Lookup.opened
  split
  · split
    · exact .pure fresh
    · rename_i fd recognized
      have actualDescriptor : descriptor reply = some fd := recognized
      have different := fresh fd actualDescriptor
      apply borrow_bind (lookup_check_borrow descriptors held handle fd)
      intro accepted property
      split
      · exact .pure fresh
      · apply BorrowPost.call
        · intro before after observed actual live
          rw [descriptors.close_other _ _ _ _ _ actual rfl (Ne.symm different)]
          exact live
        · intro before after reply actual live
          exact .pure (denied_reply_fresh held)
  · exact .pure fresh

theorem guarded_open_fresh_borrow {kernel : Contract} (descriptors : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (request : Request) (allocating : AllocatesDescriptor request.op) :
    BorrowPost kernel held handle (FreshReply held) (guardedCall request) := by
  unfold guardedCall
  apply borrow_bind (lookup_all_borrow descriptors held handle _)
  intro accepted property
  split
  · exact .pure (denied_reply_fresh held)
  · apply borrow_bind (open_fresh_borrow descriptors held handle request allocating)
    intro reply fresh
    exact lookup_opened_borrow descriptors held handle request reply fresh

theorem guarded_passive_borrow {kernel : Contract} (descriptors : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (request : Request) (passive : RetainsDescriptors request.op) :
    BorrowPost kernel held handle (fun _ => True) (guardedCall request) := by
  unfold guardedCall
  apply borrow_bind (lookup_all_borrow descriptors held handle _)
  intro accepted property
  split
  · exact .pure True.intro
  · apply borrow_bind (passive_borrow descriptors held handle request passive)
    intro reply property
    have notOpen : request.op ≠ .openAt := passive.1
    have same : Lookup.opened request reply = .pure reply := by
      simp only [Lookup.opened, Bool.and_eq_true, beq_iff_eq, notOpen, false_and, ite_false]
      rfl
    rw [same]
    exact .pure True.intro

-- §FS-host-boundary.acceptance: This lifts only a source-proved passive call profile. It makes
-- no claim that an entire guarded helper is one atomic original syscall.
theorem passive_lower_borrow {kernel : Contract} (descriptors : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) {α : Type} {program : Filesystem.Program α}
    (source : RequestProfile (fun request => RetainsDescriptors request.op) program) :
    BorrowPost kernel held handle (fun _ => True) program.lower := by
  induction source with
  | pure value => exact .pure True.intro
  | call request next passive following ih =>
    change BorrowPost kernel held handle (fun _ => True)
      ((guardedCall request).bind (fun reply => (next reply).lower))
    exact borrow_bind (guarded_passive_borrow descriptors held handle request passive) (fun reply _ => ih reply)

end LeanCage.Host.Kernel
