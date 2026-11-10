import FilesystemBorrowedOccurrences
import FilesystemLoweredBorrowing

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

private theorem no_unlink_adapter {held : UInt64} {primary request : Request}
    (safe : ¬ UnlinksThrough held primary) (role : AdapterRequest primary request) : ¬ UnlinksThrough held request := by
  rcases role with same | magic | flags | close
  · exact same ▸ safe
  · simp [UnlinksThrough, magic]
  · simp [UnlinksThrough, flags]
  · simp [UnlinksThrough, close]

private theorem adapter_no_unlink {held : UInt64} {request : Request} {α : Type} {program : Filesystem.Program α}
    (safe : ¬ UnlinksThrough held request) (source : RequestProfile (AdapterRequest request) program) :
    RequestProgram (fun request => ¬ UnlinksThrough held request) program := by
  induction source with
  | pure => exact .pure _
  | call operation next allowed following ih => exact .call (no_unlink_adapter safe allowed) ih

private theorem lower_no_unlink {held : UInt64} {α : Type} {program : Filesystem.Program α}
    (source : RequestProgram (fun request => ¬ UnlinksThrough held request) program) :
    RequestProgram (fun request => ¬ UnlinksThrough held request) program.lower := by
  induction source with
  | pure => exact .pure _
  | @call request next allowed following ih =>
    exact request_bind (adapter_no_unlink allowed (guarded_call_profile request)) ih

private theorem script_no_unlink (held : UInt64) (requests : List Request)
    (source : ∀ request ∈ requests, ¬ UnlinksThrough held request) :
    RequestProgram (fun request => ¬ UnlinksThrough held request) (callScript requests) := by
  induction requests with
  | nil => exact .pure _
  | cons request rest ih => exact .call (source request (by simp)) (fun _ => ih (by
      intro query member; exact source query (List.mem_cons_of_mem _ member)))

private theorem script_borrow_prefix {kernel : Contract} (descriptors : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (request : Request) (rest : List Request)
    (retains : RetainsDescriptors request.op)
    (tail : BorrowUses kernel held handle (UnlinksThrough held) (callScript rest).lower) :
    BorrowUses kernel held handle (UnlinksThrough held) (callScript (request :: rest)).lower :=
  borrow_then_uses (guarded_passive_borrow descriptors held handle request retains) (fun _ _ => tail)

-- §FS-host-boundary.ownership: Every actual raw inner cleanup unlink uses
-- the retained directory, before its close. The later parent-name removal
-- and both close replies remain present but never regain that released FD.
theorem cleanup_directory_uses {kernel : Contract} (descriptors : DescriptorContract kernel)
    (run : RunDirectory.Owned) (handle : Handle) (distinct : run.directory.fd ≠ run.container.fd) :
    BorrowUses kernel run.directory.fd handle (UnlinksThrough run.directory.fd) (RunDirectory.cleanup run).lower := by
  rw [cleanup_script]
  unfold cleanupScript
  apply script_borrow_prefix descriptors _ _ _ _ (by simp [RetainsDescriptors])
  apply script_borrow_prefix descriptors _ _ _ _ (by simp [RetainsDescriptors])
  apply script_borrow_prefix descriptors _ _ _ _ (by simp [RetainsDescriptors])
  apply BorrowUses.unused
  apply lower_no_unlink
  apply script_no_unlink
  intro request member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [UnlinksThrough, Ne.symm distinct]

end LeanCage.Host.Kernel.Lowered
