import FilesystemSourceOrigins

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.caller: These actual source phases cannot send caller-channel bytes.
def NoWrite (request : Request) : Prop := request.op ≠ .write

theorem input_no_write {α : Type} {program : Filesystem.Program α}
    (input : Snapshot.InputProgram program) : RequestProgram NoWrite program := by
  induction input with
  | pure => exact .pure _
  | @call request next allowed rest ih =>
    apply RequestProgram.call _ ih
    cases operation : request.op <;> simp_all [Snapshot.InputRequest, NoWrite]

theorem read_only_no_write {α : Type} {program : Filesystem.Program α}
    (input : Retrieval.ReadOnly program) : RequestProgram NoWrite program := by
  induction input with
  | pure => exact .pure _
  | @call request next allowed rest ih =>
    apply RequestProgram.call _ ih
    cases operation : request.op <;> simp_all [Retrieval.Allowed, NoWrite]

theorem read_bounded_no_write (path : ByteArray) (limit : Nat) :
    RequestProgram NoWrite (readBounded path limit) := by
  unfold readBounded
  exact request_bind (input_no_write (Snapshot.copyAt_input _ _ _)) (fun _ => .pure _)

theorem load_bundle_no_write (root : ByteArray) :
    RequestProgram NoWrite (Validation.loadBundle root) := by
  unfold Validation.loadBundle
  split
  · apply request_bind (read_bounded_no_write _ _)
    intro raw
    cases raw with
    | error => exact .pure _
    | ok raw =>
      dsimp only
      apply request_bind (input_no_write (Snapshot.hash_input _))
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

theorem check_file_no_write (bundle : Validation.Bundle) (name : String) (limit : Nat) :
    RequestProgram NoWrite (Validation.checkFile bundle name limit) := by
  unfold Validation.checkFile
  exact request_bind (read_only_no_write (Image.copyIdentified_readOnly _ _ _)) (fun _ => .pure _)

theorem check_bundle_no_write (bundle : Validation.Bundle) :
    RequestProgram NoWrite (Validation.checkBundle bundle) := by
  unfold Validation.checkBundle
  split
  · apply request_bind (request_forIn _ _ _ _ ?_)
    · intro result
      rcases result with ⟨stopped, state⟩
      cases stopped <;> exact .pure _
    · intro item member state
      apply request_bind (check_file_no_write _ _ _)
      intro result
      cases result <;> exact .pure _
  · exact .pure _

theorem engine_identity_no_write (bundle : Validation.Bundle) :
    RequestProgram NoWrite (Validation.checkEngineIdentity bundle) := by
  unfold Validation.checkEngineIdentity
  split
  · split
    · apply RequestProgram.call (by intro wrong; cases wrong)
      intro reply
      dsimp only [Filesystem.Program.bind]
      split
      · apply request_bind
          (request_bind (input_no_write (Snapshot.copyOpened_input _ _))
            (fun _ => input_no_write (Snapshot.closeResult_input _ _)))
        intro copied
        cases copied with
        | error => exact .pure _
        | ok copied =>
          apply request_bind (input_no_write (Snapshot.hash_input _))
          intro digest
          cases digest with
          | error => exact .pure _
          | ok digest => dsimp only; split <;> exact .pure _
      · exact .pure _
    · exact .pure _
  · exact .pure _

theorem load_policy_no_write (request : GatewayWire.Request) :
    RequestProgram NoWrite (Validation.loadPolicy request) := by
  unfold Validation.loadPolicy
  dsimp only
  split
  · split <;> exact .pure _
  · split
    · exact request_bind (input_no_write (Snapshot.sourceCopyFile_input _ _)) (fun _ => .pure _)
    · exact .pure _

theorem key_gate_no_write (bundle : Validation.Bundle) :
    RequestProgram NoWrite (CallerPrefixCuts.keyGate bundle) := by
  unfold CallerPrefixCuts.keyGate
  exact request_bind (read_only_no_write (Retrieval.key_readOnly _)) (fun _ => .pure _)

theorem create_directory_no_write : RequestProgram NoWrite RunDirectory.create := by
  apply request_weaken RunDirectory.create_requests
  intro request role writing
  simp only [RunDirectory.DirectoryRequest, writing] at role

theorem cleanup_directory_no_write (directory : RunDirectory.Owned) :
    RequestProgram NoWrite (RunDirectory.cleanup directory) := by
  apply request_weaken (RunDirectory.cleanup_requests directory)
  intro request role writing
  simp only [RunDirectory.CleanupRequest, writing] at role

theorem random_no_write : RequestProgram NoWrite (Directories.randomBytes 17 16 .empty) := by
  apply request_weaken (RunDirectory.directoryRandom_requests 17 16 .empty (by decide))
  intro request role writing
  simp only [RunDirectory.BeforeMarkRequest, RunDirectory.DirectoryRequest, writing] at role
  exact role.1

theorem validator_release_no_write (directory : RunDirectory.Owned) :
    RequestProgram NoWrite (Validation.releaseDirectory directory) := by
  unfold Validation.releaseDirectory
  apply RequestProgram.call (by intro wrong; cases wrong)
  intro first
  dsimp only [Filesystem.Program.bind]
  apply RequestProgram.call (by intro wrong; cases wrong)
  intro second
  exact .pure _

end LeanCage.Host.Kernel
