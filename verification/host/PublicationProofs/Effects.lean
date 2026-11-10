import LeanCageHost.Publication
import RetrievalProofs

namespace LeanCage.Host.Publication

open Filesystem

-- §FS-host-boundary.publication: Every write uses an exclusive file open and a bounded chunk.
def SafeRequest (request : Request) : Prop :=
  match request.op with
  | .openAt => request.second = readFlags ∨ request.second = directoryFlags ∨ request.second = newFileFlags
  | .read => 1 ≤ request.second.toNat ∧ request.second.toNat ≤ chunkMax
  | .write => 1 ≤ request.left.size ∧ request.left.size ≤ chunkMax
  | .random => 1 ≤ request.first.toNat ∧ request.first.toNat ≤ 16
  | .mkdirAt => request.second = 448
  | .getAttribute => request.second.toNat ≤ 40
  | .setAttribute => request.left = attributeName ∧ request.right.size = 40
  | .unlinkAt => request.second = 0 ∨ request.second = 512
  | .close | .stat | .sha256 | .euid | .workingDirectory | .dirOpen | .dirNext | .dirClose
    | .authenticate | .equalSecret | .directoryIdentity => True
  | _ => False

inductive SafeProgram {α : Type} : Filesystem.Program α → Prop where
  | pure (value : α) : SafeProgram (.pure value)
  | call {request : Request} {next : Reply → Filesystem.Program α}
      (allowed : SafeRequest request) (tail : ∀ reply, SafeProgram (next reply)) :
      SafeProgram (.call request next)

theorem safe_bind {α β : Type} {program : Filesystem.Program α} {next : α → Filesystem.Program β}
    (first : SafeProgram program) (tail : ∀ value, SafeProgram (next value)) :
    SafeProgram (program.bind next) := by
  induction first with
  | pure => exact tail _
  | call allowed rest ih => exact .call allowed ih

theorem safe_bind_post {α β : Type} {program : Filesystem.Program α} {next : α → Filesystem.Program β}
    {post : α → Prop} (first : SafeProgram program) (observed : Snapshot.PostProgram post program)
    (tail : ∀ value, post value → SafeProgram (next value)) : SafeProgram (program.bind next) := by
  induction first with
  | pure value => cases observed with | pure property => exact tail value property
  | call allowed rest ih =>
    cases observed with
    | call valid => exact .call allowed (fun reply => ih reply (valid reply))

theorem safe_prefix {α : Type} {program : Filesystem.Program α}
    {events : List (Request × Option Reply)} (verified : SafeProgram program) (run : Prefix program events) :
    ∀ event ∈ events, SafeRequest event.1 := by
  induction run with
  | empty => simp
  | lost request next => cases verified with | call allowed => simpa using allowed
  | returned request next reply events run ih =>
    cases verified with
    | call allowed tail =>
      intro event member
      rcases List.mem_cons.mp member with rfl | member
      · exact allowed
      · exact ih (tail reply) event member

theorem readOnly_safe {α : Type} {program : Filesystem.Program α} (verified : Retrieval.ReadOnly program) :
    SafeProgram program := by
  induction verified with
  | pure => exact .pure _
  | @call request next allowed rest ih =>
    apply SafeProgram.call _ ih
    cases operation : request.op <;> simp_all [Retrieval.Allowed, SafeRequest]
    rcases allowed with read | directory
    · exact .inl read
    · exact .inr (.inl directory)

theorem write_part_bounds (bytes : ByteArray) (offset : Nat) (inside : offset < bytes.size) :
    1 ≤ (bytes.extract offset (min bytes.size (offset + chunkMax))).size ∧
      (bytes.extract offset (min bytes.size (offset + chunkMax))).size ≤ chunkMax := by
  rw [ByteArray.size_extract]
  have chunkPositive : 0 < chunkMax := by decide
  omega

theorem writeLoop_safe (fuel : Nat) (fd : UInt64) (bytes : ByteArray) (offset : Nat) :
    SafeProgram (writeLoop fuel fd bytes offset) := by
  induction fuel generalizing offset with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold writeLoop
    split
    · exact .pure _
    · apply SafeProgram.call
      · exact write_part_bounds bytes offset (by omega)
      · intro reply
        split
        · exact .pure _
        · split
          · exact .pure _
          · exact ih _

theorem writeNew_safe (parent : UInt64) (name bytes : ByteArray) (mode : UInt64) :
    SafeProgram (writeNew parent name bytes mode) := by
  unfold writeNew
  split
  · exact .pure _
  · apply SafeProgram.call (by exact .inr (.inr rfl))
    intro reply
    split
    · exact .pure _
    · exact safe_bind (writeLoop_safe _ _ _ _)
        (fun _ => readOnly_safe (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _)))

end LeanCage.Host.Publication
