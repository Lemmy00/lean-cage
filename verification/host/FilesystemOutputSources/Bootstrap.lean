import FilesystemOutputBorrowing
import FilesystemLoweredPublicationBorrowing

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

theorem bootstrap_read_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (path : ByteArray) (limit : Nat) :
    BorrowPost kernel held handle (fun _ => True) (readBounded path limit).lower := by
  unfold readBounded
  apply borrow_bind (copyAt_borrow laws held handle _ _ _)
  intro copied _
  exact .pure True.intro

-- §FS-host-boundary.caller: Bootstrap reads retain each actual fresh FD and close only
-- that FD, including malformed manifests, late inventory failures and interrupted copies.
theorem load_bundle_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (root : ByteArray) :
    BorrowPost kernel held handle (fun _ => True) (Validation.loadBundle root).lower := by
  unfold Validation.loadBundle
  split
  · apply borrow_bind (bootstrap_read_borrow laws held handle _ _)
    intro raw _
    cases raw with
    | error => exact .pure True.intro
    | ok raw =>
      apply borrow_bind (hash_borrow laws held handle _)
      intro digest _
      cases digest with
      | error => exact .pure True.intro
      | ok digest =>
        dsimp only [Bind.bind, Pure.pure, Filesystem.Program.bind]
        split
        · split
          · exact .pure True.intro
          · split
            · apply borrow_bind (pre := fun _ => True)
              · apply borrow_forIn
                intro item state
                rcases item with ⟨name, value⟩
                dsimp only
                repeat' first | exact .pure True.intro | split
              · intro state _
                split <;> exact .pure True.intro
            · exact .pure True.intro
        · exact .pure True.intro
  · exact .pure True.intro

theorem identified_copy_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (bundle : Validation.Bundle) (name : String) (limit : Nat) :
    BorrowPost kernel held handle (fun _ => True) (Validation.copyIdentified bundle name limit).lower := by
  unfold Validation.copyIdentified
  split
  · split
    · apply borrow_bind (bootstrap_read_borrow laws held handle _ _)
      intro copied _
      cases copied with
      | error => exact .pure True.intro
      | ok copied =>
        apply borrow_bind (hash_borrow laws held handle _)
        intro digest _
        cases digest with
        | error => exact .pure True.intro
        | ok digest => dsimp only; split <;> exact .pure True.intro
    · exact .pure True.intro
  · exact .pure True.intro

theorem check_file_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (bundle : Validation.Bundle) (name : String) (limit : Nat) :
    BorrowPost kernel held handle (fun _ => True) (Validation.checkFile bundle name limit).lower := by
  unfold Validation.checkFile
  apply borrow_bind (identified_copy_borrow laws held handle _ _ _)
  intro copied _
  exact .pure True.intro

theorem check_bundle_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (bundle : Validation.Bundle) :
    BorrowPost kernel held handle (fun _ => True) (Validation.checkBundle bundle).lower := by
  unfold Validation.checkBundle
  split
  · apply borrow_bind (pre := fun _ => True)
    · apply borrow_forIn
      intro item state
      apply borrow_bind (check_file_borrow laws held handle _ _ _)
      intro checked _
      cases checked <;> exact .pure True.intro
    · intro state _
      dsimp only
      split <;> exact .pure True.intro
  · exact .pure True.intro

theorem running_image_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (bundle : Validation.Bundle) :
    BorrowPost kernel held handle (fun _ => True) (Validation.checkEngineIdentity bundle).lower := by
  unfold Validation.checkEngineIdentity
  split
  · split
    · apply borrow_bind (open_fresh_borrow laws held handle _ (.inr (.inr rfl)))
      intro reply fresh
      split
      · rename_i fd recognized
        apply borrow_bind (pre := fun _ => True)
        · apply borrow_bind (copyOpened_borrow laws held handle _ _)
          intro copied _
          apply borrow_weaken (close_borrow laws fd held handle copied (Ne.symm (fresh fd recognized)))
          intro _ _; trivial
        · intro copied _
          cases copied with
          | error => exact .pure True.intro
          | ok copied =>
            apply borrow_bind (hash_borrow laws held handle _)
            intro digest _
            cases digest with
            | error => exact .pure True.intro
            | ok digest => dsimp only; split <;> exact .pure True.intro
      · exact .pure True.intro
    · exact .pure True.intro
  · exact .pure True.intro

theorem policy_load_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (request : GatewayWire.Request) :
    BorrowPost kernel held handle (fun _ => True) (Validation.loadPolicy request).lower := by
  unfold Validation.loadPolicy
  dsimp only
  split
  · split <;> exact .pure True.intro
  · split
    · apply borrow_bind (sourceCopyFile_borrow laws held handle _ _)
      intro copied _
      exact .pure True.intro
    · exact .pure True.intro

theorem seal_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (fds : List UInt64) :
    BorrowPost kernel held handle (fun _ => True) (Startup.sealDescriptors fds).lower := by
  induction fds with
  | nil => exact .pure True.intro
  | cons fd rest ih =>
    unfold Startup.sealDescriptors
    apply passive_call laws held handle (by simp [RetainsDescriptors])
    intro reply
    split
    · exact .pure True.intro
    · exact ih

theorem packet_exact_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (fuel : Nat) (fd : UInt64) (amount : Nat) (bytes : ByteArray) :
    BorrowPost kernel held handle (fun _ => True) (Packet.readExact fuel fd amount bytes).lower := by
  induction fuel generalizing bytes with
  | zero => exact .pure True.intro
  | succ fuel ih =>
    unfold Packet.readExact
    split
    · exact .pure True.intro
    · split
      · exact .pure True.intro
      · apply passive_call laws held handle (by simp [RetainsDescriptors])
        intro reply
        repeat' first | exact .pure True.intro | exact ih _ | split

theorem packet_read_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (fd : UInt64) :
    BorrowPost kernel held handle (fun _ => True) (Packet.read fd).lower := by
  unfold Packet.read
  apply borrow_bind (packet_exact_borrow laws held handle _ _ _ _)
  intro header _
  cases header with
  | error => exact .pure True.intro
  | ok header =>
    dsimp only
    split
    · exact .pure True.intro
    · apply borrow_bind (packet_exact_borrow laws held handle _ _ _ _)
      intro payload _
      cases payload with
      | error => exact .pure True.intro
      | ok payload =>
        apply passive_call laws held handle (by simp [RetainsDescriptors])
        intro reply
        dsimp only [Filesystem.Program.bind]
        repeat' first | exact .pure True.intro | split

end LeanCage.Host.Kernel.Lowered
