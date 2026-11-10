import FilesystemReadSources.Source
import FilesystemWriteSources.ReadOnly

namespace LeanCage.Host.PrivateStreams
open Filesystem Kernel

-- §AR-host-boundary.primitives: A positive third word selects pread in the
-- actual op1 adapter. Positional file copies cannot consume an IPC stream.
def PositionedReads (request : Request) : Prop := request.op = .read → request.third ≠ 0

theorem no_read_positioned {α : Type} {program : Filesystem.Program α}
    (source : RequestProgram NoRead program) : RequestProgram PositionedReads program := by
  apply request_weaken source
  intro request source reading
  exact False.elim (source reading)

-- §FS-host-boundary.snapshot: The actual guard keeps offset+1 within UInt64;
-- arbitrary replies/loss do not turn a copied-file read into a stream read.
theorem read_loop_positioned (fuel : Nat) (fd : UInt64) (limit : Nat) (bytes : ByteArray) :
    RequestProgram PositionedReads (readLoop fuel fd limit bytes) := by
  induction fuel generalizing bytes with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold readLoop
    split
    · exact .pure _
    · rename_i within
      have offset : bytes.size < 2 ^ 63 := by simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at within; omega
      apply RequestProgram.call
      · intro reading absent
        have width : bytes.size + 1 < 2 ^ 64 := by omega
        have count := congrArg UInt64.toNat absent
        simp only [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt width, UInt64.toNat_zero] at count
        omega
      · intro reply
        repeat' first | exact .pure _ | exact ih _ | split

theorem close_positioned {α : Type} (fd : UInt64) (result : Result α) :
    RequestProgram PositionedReads (closeResult fd result) :=
  no_read_positioned (closeResult_noRead fd result)

theorem hash_positioned (bytes : ByteArray) : RequestProgram PositionedReads (Filesystem.hash bytes) :=
  no_read_positioned (hash_noRead bytes)

theorem copy_opened_positioned (fd : UInt64) (limit : Nat) :
    RequestProgram PositionedReads (copyOpened fd limit) := by
  unfold copyOpened
  apply RequestProgram.call (by intro impossible; cases impossible)
  intro reply
  split
  · exact .pure _
  · split
    · exact .pure _
    · apply request_bind (read_loop_positioned _ _ _ _)
      intro result
      cases result with
      | error => exact .pure _
      | ok bytes =>
        apply RequestProgram.call (by intro impossible; cases impossible)
        intro reply
        repeat' first | exact .pure _ | split

theorem copy_at_positioned (parent : UInt64) (path : ByteArray) (limit : Nat) :
    RequestProgram PositionedReads (copyAt parent path limit) := by
  unfold copyAt
  split
  · exact .pure _
  · apply RequestProgram.call (by intro impossible; cases impossible)
    intro reply
    split
    · exact .pure _
    · exact request_bind (copy_opened_positioned _ _) (close_positioned _)

theorem bounded_positioned (path : ByteArray) (limit : Nat) :
    RequestProgram PositionedReads (readBounded path limit) := by
  unfold readBounded
  exact request_bind (copy_at_positioned _ _ _) (fun _ => .pure _)

theorem source_file_positioned (path : ByteArray) (limit : Nat) :
    RequestProgram PositionedReads (SourcePaths.copyFile path limit) := by
  unfold SourcePaths.copyFile
  apply request_bind (no_read_positioned (sourceOpen_noRead path false))
  intro opened
  cases opened with
  | error => exact .pure _
  | ok fd => exact request_bind (copy_opened_positioned _ _) (close_positioned _)

theorem write_loop_positioned (fuel : Nat) (fd : UInt64) (bytes : ByteArray) (offset : Nat) :
    RequestProgram PositionedReads (writeLoop fuel fd bytes offset) := by
  induction fuel generalizing offset with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold writeLoop
    split
    · exact .pure _
    · apply RequestProgram.call (by intro impossible; cases impossible)
      intro reply
      repeat' first | exact .pure _ | exact ih _ | split

theorem write_new_positioned (parent : UInt64) (name bytes : ByteArray) (mode : UInt64 := 384) :
    RequestProgram PositionedReads (writeNew parent name bytes mode) := by
  unfold writeNew
  split
  · exact .pure _
  · apply RequestProgram.call (by intro impossible; cases impossible)
    intro reply
    split
    · exact .pure _
    · exact request_bind (write_loop_positioned _ _ _ _) (close_positioned _)

theorem load_bundle_positioned (root : ByteArray) :
    RequestProgram PositionedReads (Validation.loadBundle root) := by
  unfold Validation.loadBundle
  split
  · apply request_bind (bounded_positioned _ _)
    intro raw
    cases raw with
    | error => exact .pure _
    | ok raw =>
      dsimp only
      apply request_bind (hash_positioned _)
      intro digest
      cases digest with
      | error => exact .pure _
      | ok digest =>
        apply request_bind (.pure _)
        intro parsed
        cases parsed with
        | error => exact .pure _
        | ok manifest =>
          dsimp only
          split
          · exact .pure _
          · split
            · apply request_bind (request_forIn _ _ _ _ ?_)
              · intro result
                rcases result with ⟨stopped, directories⟩
                cases stopped <;> exact .pure _
              · intro item member state
                rcases item with ⟨name, value⟩
                dsimp only
                repeat' first | exact .pure _ | split
            · exact .pure _
  · exact .pure _

theorem copy_identified_positioned (bundle : Validation.Bundle) (name : String) (limit : Nat) :
    RequestProgram PositionedReads (Validation.copyIdentified bundle name limit) := by
  unfold Validation.copyIdentified
  repeat' first | exact .pure _ | split
  all_goals
    apply request_bind (bounded_positioned _ _)
    intro copied
    cases copied with
    | error => exact .pure _
    | ok bytes =>
      apply request_bind (hash_positioned _)
      intro digest
      cases digest with
      | error => exact .pure _
      | ok digest => dsimp only; split <;> exact .pure _

theorem check_file_positioned (bundle : Validation.Bundle) (name : String) (limit : Nat) :
    RequestProgram PositionedReads (Validation.checkFile bundle name limit) := by
  unfold Validation.checkFile
  exact request_bind (copy_identified_positioned _ _ _) (fun _ => .pure _)

theorem check_bundle_positioned (bundle : Validation.Bundle) :
    RequestProgram PositionedReads (Validation.checkBundle bundle) := by
  unfold Validation.checkBundle
  split
  · apply request_bind (request_forIn _ _ _ _ ?_)
    · intro result
      rcases result with ⟨stopped, state⟩
      cases stopped <;> exact .pure _
    · intro item member state
      apply request_bind (check_file_positioned _ _ _)
      intro result
      cases result <;> exact .pure _
  · exact .pure _

theorem engine_identity_positioned (bundle : Validation.Bundle) :
    RequestProgram PositionedReads (Validation.checkEngineIdentity bundle) := by
  unfold Validation.checkEngineIdentity
  repeat' first | exact .pure _ | split
  all_goals
    apply RequestProgram.call (by intro impossible; cases impossible)
    intro reply
    dsimp only [Filesystem.Program.bind]
    split
    · apply request_bind (request_bind (copy_opened_positioned _ _) (close_positioned _))
      intro copied
      cases copied with
      | error => exact .pure _
      | ok copied =>
        apply request_bind (hash_positioned _)
        intro digest
        cases digest with
        | error => exact .pure _
        | ok digest => dsimp only; split <;> exact .pure _
    · exact .pure _

theorem load_policy_positioned (request : GatewayWire.Request) :
    RequestProgram PositionedReads (Validation.loadPolicy request) := by
  unfold Validation.loadPolicy
  dsimp only
  split
  · split <;> exact .pure _
  · split
    · exact request_bind (source_file_positioned _ _) (fun _ => .pure _)
    · exact .pure _

-- Every guarded copy selected by the existing actual source taxonomy uses
-- the positional primitive. No replacement physical history is selected.
theorem guarded_copy_positioned {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : GuardedCopyCall before request observed) : PositionedReads request :=
  request_prefix (copy_opened_positioned source.fd source.limit) source.active (request, observed) (by simp)

theorem freeze_positioned (workspace : Option ByteArray) (stdin : Snapshot.Stdin) (limits : Snapshot.Limits)
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix (Program.liftFilesystem (Snapshot.freeze workspace stdin limits))
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) : PositionedReads request := by
  intro reading
  obtain ⟨events, actual, _⟩ := selected_filesystem_source active
  obtain ⟨source⟩ := freeze_read_sources workspace stdin limits events request observed actual reading
  exact guarded_copy_positioned source reading

end LeanCage.Host.PrivateStreams
