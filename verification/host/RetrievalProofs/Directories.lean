import RetrievalProofs.Effects

namespace LeanCage.Host.Retrieval

open Filesystem

theorem inspect_readOnly (uid : Nat) (fd : UInt64) : ReadOnly (Directories.inspect uid fd) := by
  unfold Directories.inspect
  apply ReadOnly.call (by trivial)
  intro reply
  split
  · exact readOnly_snapshot (Snapshot.closeResult_input _ _)
  · split
    · exact .pure _
    · exact readOnly_snapshot (Snapshot.closeResult_input _ _)

theorem openAt_readOnly (uid : Nat) (parent : UInt64) (name : ByteArray) :
    ReadOnly (Directories.openAt uid parent name) := by
  unfold Directories.openAt
  apply ReadOnly.call (by exact .inr rfl)
  intro reply
  split
  · exact .pure _
  · exact inspect_readOnly _ _

theorem publicAt_readOnly (uid : Nat) (parent : UInt64) (name : ByteArray) :
    ReadOnly (Directories.publicAt uid parent name false) := by
  unfold Directories.publicAt
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply readOnly_bind (openAt_readOnly _ _ _)
  intro result
  cases result with
  | error => exact .pure _
  | ok opened =>
    apply readOnly_bind (readOnly_snapshot (Snapshot.publicHandle_input _))
    intro allowed
    exact .pure _

theorem descend_readOnly (uid : Nat) (current : Directories.Opened) (names : List ByteArray) :
    ReadOnly (Directories.descend uid false current names) := by
  induction names generalizing current with
  | nil => exact .pure _
  | cons name rest ih =>
    simp only [Directories.descend]
    apply readOnly_bind (publicAt_readOnly _ _ _)
    intro next
    apply readOnly_bind (readOnly_snapshot (Snapshot.closeResult_input _ _))
    intro closed
    cases closed with
    | error =>
      cases next with
      | error => exact .pure _
      | ok => exact readOnly_snapshot (Snapshot.closeResult_input _ _)
    | ok => exact ih _

theorem parent_readOnly (path : ByteArray) : ReadOnly (Directories.parent path false) := by
  unfold Directories.parent
  apply readOnly_bind (readOnly_snapshot (Snapshot.sourceStart_input _))
  intro selected
  cases selected with
  | error => exact .pure _
  | ok selected =>
    dsimp only
    split
    · split
      · exact readOnly_snapshot (Snapshot.closeResult_input _ _)
      · apply ReadOnly.call (by trivial)
        intro identity
        dsimp only [Filesystem.Program.bind]
        split
        · exact readOnly_snapshot (Snapshot.closeResult_input _ _)
        · apply readOnly_bind (inspect_readOnly _ _)
          intro base
          cases base with
          | error => exact .pure _
          | ok base =>
            apply readOnly_bind (descend_readOnly _ _ _)
            intro result
            exact .pure _
    · exact readOnly_snapshot (Snapshot.closeResult_input _ _)

theorem under_readOnly {α : Type} (uid : Nat) (fd : UInt64) (names : List String)
    (action : UInt64 → Filesystem.Program (Result α)) (allowed : ∀ fd, ReadOnly (action fd)) :
    ReadOnly (Publication.under uid fd names false action) := by
  induction names generalizing fd with
  | nil => exact allowed fd
  | cons name rest ih =>
    simp only [Publication.under]
    split
    · exact .pure _
    · simp only [Bool.false_eq_true, ↓reduceIte]
      apply readOnly_bind (openAt_readOnly _ _ _)
      intro result
      cases result with
      | error => exact .pure _
      | ok child =>
        exact readOnly_bind (ih child.fd) (fun _ => readOnly_snapshot (Snapshot.closeResult_input _ _))

theorem absolute_readOnly (path : ByteArray) : ReadOnly (Publication.absolute path) := by
  unfold Publication.absolute
  split
  · exact .pure _
  · split
    · exact .pure _
    · apply ReadOnly.call (by trivial)
      intro reply
      dsimp only [Filesystem.Program.bind]
      split
      · exact .pure _
      · split <;> exact .pure _

theorem publicationDestination_readOnly (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (identity : String) : ReadOnly (Publication.destination request bundle identity) := by
  unfold Publication.destination
  dsimp only
  split <;> exact .pure _

theorem key_readOnly (bundle : Validation.Bundle) : ReadOnly (Publication.authenticationKey bundle) := by
  unfold Publication.authenticationKey
  split
  · split
    · apply ReadOnly.call (by trivial)
      intro reply
      dsimp only [Filesystem.Program.bind]
      split
      · exact .pure _
      · apply ReadOnly.call (by exact .inl rfl)
        intro opened
        dsimp only [Filesystem.Program.bind]
        split
        · apply ReadOnly.call (by change (1 : UInt64).toNat ≤ 40; decide)
          intro privateReply
          dsimp only [Filesystem.Program.bind]
          split
          · exact readOnly_snapshot (Snapshot.closeResult_input _ _)
          · apply readOnly_bind (readOnly_snapshot (Snapshot.input_bind
              (Snapshot.copyOpened_input _ _) (Snapshot.closeResult_input _)))
            intro copied
            cases copied with
            | error => exact .pure _
            | ok copied =>
              dsimp only
              split
              · exact .pure _
              · apply readOnly_bind (readOnly_snapshot (Snapshot.hash_input _))
                intro hashed
                cases hashed with
                | error => exact .pure _
                | ok digest => dsimp only; split <;> exact .pure _
        · exact .pure _
    · exact .pure _
  · exact .pure _

theorem authenticate_readOnly (bundle : Validation.Bundle) (wire : ByteArray) :
    ReadOnly (Publication.authenticate bundle wire) := by
  unfold Publication.authenticate
  split
  · exact .pure _
  · apply readOnly_bind (key_readOnly _)
    intro key
    cases key with
    | error => exact .pure _
    | ok key =>
      apply ReadOnly.call (by trivial)
      intro reply
      dsimp only [Filesystem.Program.bind]
      split <;> exact .pure _

theorem verify_readOnly (bundle : Validation.Bundle) (wire supplied : ByteArray) :
    ReadOnly (Publication.verify bundle wire supplied) := by
  unfold Publication.verify
  split
  · exact .pure _
  · apply readOnly_bind (authenticate_readOnly _ _)
    intro expected
    cases expected with
    | error => exact .pure _
    | ok expected =>
      apply ReadOnly.call (by trivial)
      intro reply
      dsimp only [Filesystem.Program.bind]
      split
      · exact .pure _
      · split <;> exact .pure _

end LeanCage.Host.Retrieval
