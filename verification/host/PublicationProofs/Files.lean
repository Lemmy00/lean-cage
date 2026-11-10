import PublicationProofs.Directories
import PublicationProofs.Writes

namespace LeanCage.Host.Publication

open Filesystem

theorem writeRelative_safe (uid : Nat) (root : UInt64) (file : Artifacts.ValidatedFile) :
    SafeProgram (writeRelative uid root file) := by
  unfold writeRelative
  dsimp only
  split
  · exact under_safe _ _ _ _ _ (fun _ => writeNew_safe _ _ _ _)
  · exact .pure _

theorem directories_safe (uid : Nat) (root : UInt64) (paths : List Artifacts.ExportPath) :
    SafeProgram (directories uid root paths) := by
  unfold directories
  apply safe_bind
  · apply forIn_safe
    intro path state
    apply safe_bind (under_safe _ _ _ _ _ (fun _ => .pure _))
    intro made
    cases made <;> exact .pure _
  · intro state
    dsimp only
    split <;> exact .pure _

theorem exports_safe (uid : Nat) (stage : UInt64) (input : Input) :
    SafeProgram (exports uid stage input) := by
  unfold exports
  apply SafeProgram.call (by rfl)
  intro made
  dsimp only [Filesystem.Program.bind]
  split
  · exact .pure _
  · apply safe_bind (readOnly_safe (Retrieval.openAt_readOnly _ _ _))
    intro opened
    cases opened with
    | error => exact .pure _
    | ok root =>
      apply safe_bind
      · apply safe_bind (directories_safe _ _ _)
        intro made
        cases made with
        | error => exact .pure _
        | ok made =>
          apply safe_bind
          · apply forIn_safe
            intro file state
            apply safe_bind (writeRelative_safe _ _ _)
            intro written
            cases written <;> exact .pure _
          · intro state
            split <;> exact .pure _
      · intro filled
        exact readOnly_safe (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))

theorem fill_safe (uid : Nat) (stage : UInt64) (input : Input) (json wire : ByteArray) :
    SafeProgram (fill uid stage input json wire) := by
  unfold fill
  repeat' first
    | exact .pure _
    | (dsimp only; split)
    | split
  all_goals
    apply safe_bind
    · apply forIn_safe
      intro pair state
      apply safe_bind (writeNew_safe _ _ _ _)
      intro written
      cases written <;> exact .pure _
    · intro state
      split
      · exact .pure _
      · exact exports_safe _ _ _

theorem unlinkRelative_safe (uid : Nat) (root : UInt64) (parts : List String) (directory : Bool) :
    SafeProgram (unlinkRelative uid root parts directory) := by
  unfold unlinkRelative
  split
  · apply safe_bind (under_safe _ _ _ _ _ (fun _ => by
      apply SafeProgram.call
      · cases directory; exact .inl rfl; exact .inr rfl
      · intro reply
        dsimp only [Filesystem.Program.bind]
        split <;> exact .pure _))
    intro ignored
    exact .pure _
  · exact .pure _

end LeanCage.Host.Publication
