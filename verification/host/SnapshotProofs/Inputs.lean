import SnapshotProofs.Effects

namespace LeanCage.Host.Snapshot

open Filesystem

-- §FS-host-boundary.snapshot: Input acquisition never requests host output mutation.
def InputRequest (request : Request) : Prop :=
  match request.op with
  | .openAt => request.second = readFlags ∨ request.second = directoryFlags
  | .read => 1 ≤ request.second.toNat ∧ request.second.toNat ≤ chunkMax
  | .getAttribute => request.left = PrivateNames.attributeName ∧ request.second = 1
  | .workingDirectory | .directoryIdentity => True
  | .close | .stat | .dirOpen | .dirNext | .dirClose | .sha256 => True
  | _ => False

inductive InputProgram {α : Type} : Program α → Prop where
  | pure (value : α) : InputProgram (.pure value)
  | call {request : Request} {next : Reply → Program α}
      (allowed : InputRequest request) (tail : ∀ reply, InputProgram (next reply)) :
      InputProgram (.call request next)

theorem input_bind {α β : Type} {program : Program α} {next : α → Program β}
    (first : InputProgram program) (tail : ∀ value, InputProgram (next value)) :
    InputProgram (program.bind next) := by
  induction first with
  | pure value => simpa only [Program.bind] using tail value
  | call allowed _ ih =>
    exact .call allowed (fun reply => ih reply)

theorem input_prefix {α : Type} {program : Program α} {events : List (Request × Option Reply)}
    (allowed : InputProgram program) (run : Prefix program events) :
    ∀ event ∈ events, InputRequest event.1 := by
  induction run with
  | empty => simp
  | lost request next =>
    cases allowed with
    | call first tail => simpa using first
  | returned request next reply events rest ih =>
    cases allowed with
    | call first tail =>
      intro event present
      simp only [List.mem_cons] at present
      rcases present with rfl | present
      · exact first
      · exact ih (tail reply) event present

private theorem boundedReadRequest (limit count : Nat) (within : count ≤ limit) :
    1 ≤ (min chunkMax (limit + 1 - count)).toUInt64.toNat ∧
      (min chunkMax (limit + 1 - count)).toUInt64.toNat ≤ chunkMax := by
  have upper : min chunkMax (limit + 1 - count) ≤ chunkMax := Nat.min_le_left _ _
  have positive : 1 ≤ min chunkMax (limit + 1 - count) := by
    apply Nat.le_min.mpr
    constructor
    · decide
    · omega
  have fits : min chunkMax (limit + 1 - count) < 2 ^ 64 := by
    have : chunkMax < 2 ^ 64 := by decide
    omega
  simpa only [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt fits] using ⟨positive, upper⟩

theorem readLoop_input (fuel : Nat) (fd : UInt64) (limit : Nat) (bytes : ByteArray) :
    InputProgram (readLoop fuel fd limit bytes) := by
  induction fuel generalizing bytes with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold readLoop
    split
    · exact .pure _
    · rename_i within
      have bounds : bytes.size ≤ limit ∧ bytes.size < 2 ^ 63 := by
        simpa only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt, Nat.not_le] using within
      apply InputProgram.call
      · exact boundedReadRequest limit bytes.size (by omega)
      · intro reply
        split
        · exact .pure _
        · split
          · exact .pure _
          · split
            · exact .pure _
            · split
              · exact .pure _
              · exact ih _

theorem closeResult_input {α : Type} (fd : UInt64) (result : Result α) :
    InputProgram (closeResult fd result) := by
  apply InputProgram.call (by trivial)
  intro reply
  cases result with
  | error => exact .pure _
  | ok => dsimp only; split <;> exact .pure _

theorem copyOpened_input (fd : UInt64) (limit : Nat) : InputProgram (copyOpened fd limit) := by
  unfold copyOpened
  apply InputProgram.call (by trivial)
  intro reply
  split
  · exact .pure _
  · split
    · exact .pure _
    · apply input_bind (readLoop_input _ _ _ _)
      intro result
      cases result with
      | error => exact .pure _
      | ok bytes =>
        apply InputProgram.call (by trivial)
        intro finalReply
        split
        · exact .pure _
        · split <;> exact .pure _

theorem copyAt_input (parent : UInt64) (path : ByteArray) (limit : Nat) :
    InputProgram (copyAt parent path limit) := by
  unfold copyAt
  split
  · exact .pure _
  · apply InputProgram.call (by exact .inl rfl)
    intro reply
    split
    · exact .pure _
    · exact input_bind (copyOpened_input _ _) (closeResult_input _)

theorem hash_input (bytes : ByteArray) : InputProgram (Filesystem.hash bytes) := by
  unfold Filesystem.hash
  apply InputProgram.call (by trivial)
  intro reply
  split <;> exact .pure _

theorem closeDirectory_input {α : Type} (fd cursor : UInt64) (result : Result α) :
    InputProgram (closeDirectory fd cursor result) := by
  apply InputProgram.call (by trivial)
  intro reply
  cases result with
  | error => exact .pure _
  | ok => dsimp only; split <;> exact .pure _

theorem enumerate_input (fuel : Nat) (cursor : UInt64) (remaining : Nat)
    (seen names : List String) : InputProgram (enumerate fuel cursor remaining seen names) := by
  induction fuel generalizing seen names with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold enumerate
    apply InputProgram.call (by trivial)
    intro reply
    split
    · exact .pure _
    · split
      · exact .pure _
      · split
        · exact .pure _
        · split
          · exact .pure _
          · split
            · exact ih _ _
            · split
              · exact .pure _
              · exact ih _ _


end LeanCage.Host.Snapshot
