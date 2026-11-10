import FilesystemMarkerSources
import FilesystemCwdFrames

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.snapshot: Lookup/audit does not read caller file contents.
def NoRead (request : Request) : Prop := request.op ≠ .read

theorem closeResult_noRead {α : Type} (fd : UInt64) (result : Result α) :
    RequestProgram NoRead (closeResult fd result) := by
  apply RequestProgram.call (by change Op.close ≠ Op.read; decide)
  intro reply
  cases result with
  | error => exact .pure _
  | ok => dsimp only; split <;> exact .pure _

theorem publicHandle_noRead (fd : UInt64) : RequestProgram NoRead (SourcePaths.publicHandle fd) := by
  unfold SourcePaths.publicHandle
  apply RequestProgram.call (by change Op.getAttribute ≠ Op.read; decide)
  intro reply
  split
  · exact .pure _
  · exact closeResult_noRead _ _

theorem sourceOpenAt_noRead (parent : UInt64) (name : ByteArray) (directory : Bool) :
    RequestProgram NoRead (SourcePaths.openAt parent name directory) := by
  unfold SourcePaths.openAt
  apply RequestProgram.call (by change Op.openAt ≠ Op.read; decide)
  intro opened
  split
  · exact .pure _
  · exact publicHandle_noRead _

theorem releaseParent_noRead (parent : UInt64) (child : Result UInt64) :
    RequestProgram NoRead (SourcePaths.releaseParent parent child) := by
  unfold SourcePaths.releaseParent
  apply request_bind (closeResult_noRead _ _)
  intro result
  cases result with
  | ok => exact .pure _
  | error =>
    cases child with
    | error => exact .pure _
    | ok => exact closeResult_noRead _ _

theorem sourceWalk_noRead (parent : UInt64) (parts : List ByteArray) (directory : Bool) :
    RequestProgram NoRead (SourcePaths.walk parent parts directory) := by
  induction parts generalizing parent with
  | nil => exact .pure _
  | cons name rest ih =>
    unfold SourcePaths.walk
    apply request_bind (sourceOpenAt_noRead _ _ _)
    intro opened
    apply request_bind (releaseParent_noRead _ _)
    intro released
    cases released with
    | error => exact .pure _
    | ok child => exact ih child

theorem sourceAbsolute_noRead (path : ByteArray) : RequestProgram NoRead (SourcePaths.absolute path) := by
  unfold SourcePaths.absolute
  split
  · exact .pure _
  · split
    · exact .pure _
    · apply RequestProgram.call (by change Op.workingDirectory ≠ Op.read; decide)
      intro current
      dsimp only [Filesystem.Program.bind]
      split
      · exact .pure _
      · split <;> exact .pure _

theorem sourceIdentity_noRead (fd : UInt64) : RequestProgram NoRead (SourcePaths.identity fd) := by
  unfold SourcePaths.identity
  apply RequestProgram.call (by change Op.directoryIdentity ≠ Op.read; decide)
  intro reply
  split <;> exact .pure _

theorem sourceAncestry_noRead (fuel : Nat) (current : UInt64) (root : ByteArray) :
    RequestProgram NoRead (SourcePaths.ancestry fuel current root) := by
  induction fuel generalizing current with
  | zero => exact closeResult_noRead _ _
  | succ fuel ih =>
    unfold SourcePaths.ancestry
    apply request_bind (sourceIdentity_noRead _)
    intro observed
    cases observed with
    | error => exact closeResult_noRead _ _
    | ok observed =>
      dsimp only
      split
      · exact closeResult_noRead _ _
      · apply request_bind (sourceOpenAt_noRead _ _ _)
        intro parent
        apply request_bind (releaseParent_noRead _ _)
        intro released
        cases released with
        | error => exact .pure _
        | ok parent => exact ih _

theorem sourceCheckAncestry_noRead (base : UInt64) : RequestProgram NoRead (SourcePaths.checkAncestry base) := by
  unfold SourcePaths.checkAncestry
  apply request_bind (sourceOpenAt_noRead _ _ _)
  intro root
  cases root with
  | error => exact .pure _
  | ok root =>
    apply request_bind (request_bind (sourceIdentity_noRead _) (closeResult_noRead _))
    intro observed
    cases observed with
    | error => exact .pure _
    | ok identity =>
      apply request_bind (sourceOpenAt_noRead _ _ _)
      intro duplicate
      cases duplicate with
      | error => exact .pure _
      | ok duplicate => exact sourceAncestry_noRead _ _ _

theorem sourceStart_noRead (path : ByteArray) : RequestProgram NoRead (SourcePaths.start path) := by
  unfold SourcePaths.start
  split
  · exact .pure _
  · split
    · apply request_bind (sourceOpenAt_noRead _ _ _)
      intro root
      exact .pure _
    · apply request_bind (sourceOpenAt_noRead _ _ _)
      intro base
      cases base with
      | error => exact .pure _
      | ok base =>
        apply RequestProgram.call (by change Op.workingDirectory ≠ Op.read; decide)
        intro spelling
        dsimp only [Filesystem.Program.bind]
        split
        · exact closeResult_noRead _ _
        · apply request_bind (sourceCheckAncestry_noRead _)
          intro checked
          cases checked with
          | error => exact closeResult_noRead _ _
          | ok checkedUnit => cases checkedUnit; exact .pure _

theorem sourceOpen_noRead (path : ByteArray) (directory : Bool) :
    RequestProgram NoRead (SourcePaths.open path directory) := by
  unfold SourcePaths.open
  apply request_bind (sourceStart_noRead _)
  intro selected
  cases selected with
  | error => exact .pure _
  | ok selected => exact sourceWalk_noRead _ _ _

theorem hash_noRead (bytes : ByteArray) : RequestProgram NoRead (Filesystem.hash bytes) := by
  unfold Filesystem.hash
  apply RequestProgram.call (by change Op.sha256 ≠ Op.read; decide)
  intro reply
  split <;> exact .pure _

theorem identify_noRead (bytes : Option ByteArray) : RequestProgram NoRead (Snapshot.identify bytes) := by
  cases bytes with
  | none => exact .pure _
  | some bytes => exact request_bind (hash_noRead _) (fun _ => .pure _)

theorem closeDirectory_noRead {α : Type} (fd cursor : UInt64) (result : Result α) :
    RequestProgram NoRead (Snapshot.closeDirectory fd cursor result) := by
  apply RequestProgram.call (by change Op.dirClose ≠ Op.read; decide)
  intro reply
  cases result with
  | error => exact .pure _
  | ok => dsimp only; split <;> exact .pure _

theorem enumerate_noRead (fuel : Nat) (cursor : UInt64) (remaining : Nat) (seen names : List String) :
    RequestProgram NoRead (Snapshot.enumerate fuel cursor remaining seen names) := by
  induction fuel generalizing seen names with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold Snapshot.enumerate
    apply RequestProgram.call (by change Op.dirNext ≠ Op.read; decide)
    intro reply
    repeat' first | exact .pure _ | exact ih _ _ | split

end LeanCage.Host.Kernel
