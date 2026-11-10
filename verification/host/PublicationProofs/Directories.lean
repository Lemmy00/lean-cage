import PublicationProofs.Loops

namespace LeanCage.Host.Publication

open Filesystem

theorem ensureAt_safe (uid : Nat) (parent : UInt64) (name : ByteArray) :
    SafeProgram (Directories.ensureAt uid parent name) := by
  unfold Directories.ensureAt
  apply SafeProgram.call (by rfl)
  intro reply
  dsimp only [Filesystem.Program.bind]
  split
  · exact readOnly_safe (Retrieval.openAt_readOnly _ _ _)
  · split
    · exact readOnly_safe (Retrieval.openAt_readOnly _ _ _)
    · exact .pure _

theorem publicAt_safe (uid : Nat) (parent : UInt64) (name : ByteArray) (create : Bool) :
    SafeProgram (Directories.publicAt uid parent name create) := by
  cases create <;> unfold Directories.publicAt
  all_goals simp only [Bool.false_eq_true, ↓reduceIte]
  · apply safe_bind (readOnly_safe (Retrieval.openAt_readOnly _ _ _))
    intro result
    cases result with
    | error => exact .pure _
    | ok opened =>
      apply safe_bind (readOnly_safe (Retrieval.readOnly_snapshot (Snapshot.publicHandle_input _)))
      intro allowed
      exact .pure _
  · apply safe_bind (ensureAt_safe _ _ _)
    intro result
    cases result with
    | error => exact .pure _
    | ok opened =>
      apply safe_bind (readOnly_safe (Retrieval.readOnly_snapshot (Snapshot.publicHandle_input _)))
      intro allowed
      exact .pure _

theorem descend_safe (uid : Nat) (create : Bool) (current : Directories.Opened) (names : List ByteArray) :
    SafeProgram (Directories.descend uid create current names) := by
  induction names generalizing current with
  | nil => exact .pure _
  | cons name rest ih =>
    unfold Directories.descend
    apply safe_bind (publicAt_safe _ _ _ _)
    intro next
    apply safe_bind (readOnly_safe (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _)))
    intro closed
    cases closed with
    | error =>
      cases next with
      | error => exact .pure _
      | ok => exact readOnly_safe (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
    | ok => exact ih _

theorem parent_safe (path : ByteArray) (create : Bool) : SafeProgram (Directories.parent path create) := by
  unfold Directories.parent
  apply safe_bind (readOnly_safe (Retrieval.readOnly_snapshot (Snapshot.sourceStart_input _)))
  intro selected
  cases selected with
  | error => exact .pure _
  | ok selected =>
    dsimp only
    split
    · split
      · exact readOnly_safe (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
      · apply SafeProgram.call (by trivial)
        intro identity
        dsimp only [Filesystem.Program.bind]
        split
        · exact readOnly_safe (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
        · apply safe_bind (readOnly_safe (Retrieval.inspect_readOnly _ _))
          intro base
          cases base with
          | error => exact .pure _
          | ok base =>
            apply safe_bind (descend_safe _ _ _ _)
            intro result
            exact .pure _
    · exact readOnly_safe (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))

theorem randomBytes_safe (fuel count : Nat) (bytes : ByteArray) (bound : count ≤ 16) :
    SafeProgram (Directories.randomBytes fuel count bytes) := by
  induction fuel generalizing bytes with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold Directories.randomBytes
    split
    · exact .pure _
    · split
      · exact .pure _
      · apply SafeProgram.call
        · change 1 ≤ (count - bytes.size).toUInt64.toNat ∧
            (count - bytes.size).toUInt64.toNat ≤ 16
          have different : bytes.size ≠ count := by simpa using ‹¬(bytes.size == count) = true›
          have fits : count - bytes.size < 2 ^ 64 := by omega
          rw [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt fits]
          constructor <;> omega
        · intro reply
          split
          · exact .pure _
          · split
            · exact .pure _
            · exact ih _

theorem newChild_safe (uid : Nat) (parent : UInt64) (prefixName : String) :
    SafeProgram (Directories.newChild uid parent prefixName) := by
  unfold Directories.newChild
  apply safe_bind (randomBytes_safe _ _ _ (by decide))
  intro random
  cases random with
  | error => exact .pure _
  | ok bytes =>
    dsimp only
    split
    · exact .pure _
    · apply SafeProgram.call (by rfl)
      intro made
      dsimp only [Filesystem.Program.bind]
      split
      · exact .pure _
      · apply safe_bind (readOnly_safe (Retrieval.openAt_readOnly _ _ _))
        intro opened
        cases opened with
        | error => exact .pure _
        | ok directory =>
          dsimp only
          split
          · exact readOnly_safe (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
          · exact .pure _

theorem fresh_safe (parent : Directories.Parent) : SafeProgram (Directories.fresh parent) := by
  unfold Directories.fresh
  apply safe_bind (readOnly_safe (Retrieval.openAt_readOnly _ _ _))
  intro container
  cases container with
  | error => exact .pure _
  | ok container =>
    apply safe_bind (newChild_safe _ _ _)
    intro child
    cases child with
    | error => exact readOnly_safe (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
    | ok => exact .pure _

-- §FS-host-boundary.ownership: Checked components retain the exact parent until its action closes.
theorem under_safe {α : Type} (uid : Nat) (fd : UInt64) (names : List String) (create : Bool)
    (action : UInt64 → Filesystem.Program (Result α)) (allowed : ∀ fd, SafeProgram (action fd)) :
    SafeProgram (under uid fd names create action) := by
  induction names generalizing fd with
  | nil => exact allowed fd
  | cons name rest ih =>
    unfold under
    split
    · exact .pure _
    · cases create <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · apply safe_bind (readOnly_safe (Retrieval.openAt_readOnly _ _ _))
        intro opened
        cases opened with
        | error => exact .pure _
        | ok child =>
          exact safe_bind (ih child.fd)
            (fun _ => readOnly_safe (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _)))
      · apply safe_bind (ensureAt_safe _ _ _)
        intro opened
        cases opened with
        | error => exact .pure _
        | ok child =>
          exact safe_bind (ih child.fd)
            (fun _ => readOnly_safe (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _)))

end LeanCage.Host.Publication
