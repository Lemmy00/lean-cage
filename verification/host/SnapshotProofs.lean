import LeanCageHost.Snapshot
import BytesProofs
import SnapshotProofs.Effects
import SnapshotProofs.Copy
import SnapshotProofs.State
import SnapshotProofs.Enumeration
import SnapshotProofs.Preservation
import SnapshotProofs.Freeze
import SnapshotProofs.Blobs
import SnapshotProofs.Acquisition
import SnapshotProofs.Budget
import SnapshotProofs.Catalog
import SnapshotProofs.Origins
import SnapshotProofs.Format
import SnapshotProofs.Useful
import SnapshotProofs.SourcePaths
import SnapshotProofs.Private

namespace LeanCage.Host.Snapshot

open Filesystem

private theorem walk_input_pair (fuel : Nat) :
    (∀ limits fd name state, InputProgram (walk fuel limits fd name state)) ∧
    (∀ limits fd name names state, InputProgram (walkChildren fuel limits fd name names state)) := by
  induction fuel with
  | zero =>
    constructor
    · intro limits fd name state
      simpa only [walk] using closeResult_input fd (.error "snapshot traversal made no bounded progress" : Result State)
    · intro limits fd name names state
      cases names <;> exact .pure _
  | succ fuel ih =>
    constructor
    · intro limits fd name state
      unfold walk
      apply InputProgram.call (by trivial)
      intro initialReply
      split
      · exact closeResult_input _ _
      · split
        · exact closeResult_input _ _
        · apply InputProgram.call (by trivial)
          intro opened
          split
          · exact closeResult_input _ _
          · split
            · exact .pure _
            · dsimp only
              split
              · exact .pure _
              · apply input_bind (enumerate_input _ _ _ _ _)
                intro listing
                cases listing with
                | error => exact closeDirectory_input _ _
                | ok names =>
                  apply input_bind (ih.2 _ _ _ _ _)
                  intro result
                  cases result with
                  | error => exact closeDirectory_input _ _
                  | ok after =>
                    apply InputProgram.call (by trivial)
                    intro finalReply
                    split
                    · exact closeDirectory_input _ _
                    · exact closeDirectory_input _ _
    · intro limits fd name names state
      cases names with
      | nil => exact .pure _
      | cons child rest =>
        unfold walkChildren
        split
        · exact .pure _
        · split
          · exact .pure _
          · split
            · exact .pure _
            · dsimp only
              split
              · apply input_bind (sourceOpenAt_input _ _ _)
                intro opened
                cases opened with
                | error => exact .pure _
                | ok child =>
                  apply InputProgram.call (by trivial)
                  intro information
                  split
                  · exact closeResult_input _ _
                  · split
                    · split
                      · exact closeResult_input _ _
                      · apply input_bind (ih.1 _ _ _ _)
                        intro result
                        cases result with
                        | error => exact .pure _
                        | ok after => exact ih.2 _ _ _ _ _
                    · split
                      · apply input_bind (input_bind (copyOpened_input _ _) (closeResult_input _))
                        intro result
                        cases result with
                        | error => exact .pure _
                        | ok copied =>
                          apply input_bind (hash_input _)
                          intro hashed
                          cases hashed with
                          | error => exact .pure _
                          | ok digest =>
                            split
                            · exact .pure _
                            · split
                              · exact .pure _
                              · split
                                · exact .pure _
                                · exact ih.2 _ _ _ _ _
                      · exact closeResult_input _ _
              · exact .pure _

theorem walk_input (fuel : Nat) (limits : Limits) (fd : UInt64) (name : String) (state : State) :
    InputProgram (walk fuel limits fd name state) := (walk_input_pair fuel).1 _ _ _ _

theorem walkChildren_input (fuel : Nat) (limits : Limits) (fd : UInt64) (name : String)
    (names : List String) (state : State) : InputProgram (walkChildren fuel limits fd name names state) :=
  (walk_input_pair fuel).2 _ _ _ _ _

theorem copyWorkspace_input (workspace : Option ByteArray) (limits : Limits) :
    InputProgram (copyWorkspace workspace limits) := by
  cases workspace with
  | none => exact .pure _
  | some path =>
    simp only [copyWorkspace]
    apply input_bind (sourceOpen_input _ _)
    intro opened
    cases opened with
    | error => exact .pure _
    | ok fd => exact walk_input _ _ _ _ _

theorem copyStdin_input (stdin : Stdin) (limit : Nat) : InputProgram (copyStdin stdin limit) := by
  cases stdin with
  | absent => exact .pure _
  | bytes bytes => simp only [copyStdin]; split <;> exact .pure _
  | file path => exact input_bind (sourceCopyFile_input _ _) (fun _ => .pure _)

theorem freeze_input (workspace : Option ByteArray) (stdin : Stdin) (limits : Limits) :
    InputProgram (freeze workspace stdin limits) := by
  unfold freeze
  split
  · exact .pure _
  · apply input_bind (copyWorkspace_input _ _)
    intro copied
    cases copied with
    | error => exact .pure _
    | ok state =>
      apply input_bind (copyStdin_input _ _)
      intro input
      cases input with
      | error => exact .pure _
      | ok input =>
        apply input_bind
        · cases workspace with
          | none => exact .pure _
          | some path => exact input_bind (hash_input _) (fun _ => .pure _)
        · intro treeHash
          cases treeHash with
          | error => exact .pure _
          | ok digest =>
            apply input_bind
            · cases input with
              | none => exact .pure _
              | some bytes => exact input_bind (hash_input _) (fun _ => .pure _)
            · intro inputHash
              cases inputHash <;> exact .pure _

-- §FS-host-boundary.snapshot: Arbitrary failures and a lost call still cannot request host writes.
theorem freeze_no_write_prefix (workspace : Option ByteArray) (stdin : Stdin) (limits : Limits)
    (events : List (Request × Option Reply)) (run : Prefix (freeze workspace stdin limits) events) :
    ∀ event ∈ events, InputRequest event.1 := input_prefix (freeze_input _ _ _) run

end LeanCage.Host.Snapshot
