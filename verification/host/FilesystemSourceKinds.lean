import FilesystemChanges
import EntrypointPrefixCuts
import CallerPrefixCuts
import RunPrefixCuts
import PreparationPrefixCuts
import ValidatorPrefixCuts
import RuntimeEffects
import ImageProofs.Prefix
import VirtualMachineProofs.Prefix

namespace LeanCage.Host.Kernel
open Filesystem

def NamespacePassive (request : Request) : Prop :=
  match request.op with
  | .openAt => request.second = readFlags ∨ request.second = directoryFlags
  | .mkdirAt | .unlinkAt | .renameNew | .temporary | .setAttribute => False
  | _ => True

theorem input_namespace_passive {α : Type} {program : Filesystem.Program α}
    (input : Snapshot.InputProgram program) : RequestProgram NamespacePassive program := by
  induction input with
  | pure => exact .pure _
  | @call request next allowed rest ih =>
    apply RequestProgram.call _ ih
    cases operation : request.op <;> simp_all [Snapshot.InputRequest, NamespacePassive]

theorem read_only_namespace_passive {α : Type} {program : Filesystem.Program α}
    (input : Retrieval.ReadOnly program) : RequestProgram NamespacePassive program := by
  induction input with
  | pure => exact .pure _
  | @call request next allowed rest ih =>
    apply RequestProgram.call _ ih
    cases operation : request.op <;> simp_all [Retrieval.Allowed, NamespacePassive]

theorem read_bounded_namespace_passive (path : ByteArray) (limit : Nat) :
    RequestProgram NamespacePassive (readBounded path limit) := by
  unfold readBounded
  exact request_bind (input_namespace_passive (Snapshot.copyAt_input _ _ _)) (fun _ => .pure _)

theorem load_bundle_namespace_passive (root : ByteArray) :
    RequestProgram NamespacePassive (Validation.loadBundle root) := by
  unfold Validation.loadBundle
  split
  · apply request_bind (read_bounded_namespace_passive _ _)
    intro raw
    cases raw with
    | error => exact .pure _
    | ok raw =>
      dsimp only
      apply request_bind (input_namespace_passive (Snapshot.hash_input _))
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

theorem check_file_namespace_passive (bundle : Validation.Bundle) (name : String) (limit : Nat) :
    RequestProgram NamespacePassive (Validation.checkFile bundle name limit) := by
  unfold Validation.checkFile
  exact request_bind (read_only_namespace_passive (Image.copyIdentified_readOnly _ _ _)) (fun _ => .pure _)

theorem check_bundle_namespace_passive (bundle : Validation.Bundle) :
    RequestProgram NamespacePassive (Validation.checkBundle bundle) := by
  unfold Validation.checkBundle
  split
  · apply request_bind (request_forIn _ _ _ _ ?_)
    · intro result
      rcases result with ⟨stopped, state⟩
      cases stopped <;> exact .pure _
    · intro item member state
      apply request_bind (check_file_namespace_passive _ _ _)
      intro result
      cases result <;> exact .pure _
  · exact .pure _

theorem engine_identity_namespace_passive (bundle : Validation.Bundle) :
    RequestProgram NamespacePassive (Validation.checkEngineIdentity bundle) := by
  unfold Validation.checkEngineIdentity
  split
  · split
    · apply RequestProgram.call (by trivial)
      intro reply
      dsimp only [Filesystem.Program.bind]
      split
      · apply request_bind
          (request_bind (input_namespace_passive (Snapshot.copyOpened_input _ _))
            (fun _ => input_namespace_passive (Snapshot.closeResult_input _ _)))
        intro copied
        cases copied with
        | error => exact .pure _
        | ok copied =>
          apply request_bind (input_namespace_passive (Snapshot.hash_input _))
          intro digest
          cases digest with
          | error => exact .pure _
          | ok digest => dsimp only; split <;> exact .pure _
      · exact .pure _
    · exact .pure _
  · exact .pure _

theorem load_policy_namespace_passive (request : GatewayWire.Request) :
    RequestProgram NamespacePassive (Validation.loadPolicy request) := by
  unfold Validation.loadPolicy
  dsimp only
  split
  · split <;> exact .pure _
  · split
    · exact request_bind (input_namespace_passive (Snapshot.sourceCopyFile_input _ _)) (fun _ => .pure _)
    · exact .pure _

theorem key_gate_namespace_passive (bundle : Validation.Bundle) :
    RequestProgram NamespacePassive (CallerPrefixCuts.keyGate bundle) := by
  unfold CallerPrefixCuts.keyGate
  exact request_bind (read_only_namespace_passive (Retrieval.key_readOnly _)) (fun _ => .pure _)

theorem seal_namespace_passive (descriptors : List UInt64) :
    RequestProgram NamespacePassive (Startup.sealDescriptors descriptors) := by
  induction descriptors with
  | nil => exact .pure _
  | cons head rest ih =>
    unfold Startup.sealDescriptors
    apply RequestProgram.call (by trivial)
    intro reply
    split
    · exact .pure _
    · exact ih

theorem packet_exact_namespace_passive (fuel : Nat) (fd : UInt64) (amount : Nat) (bytes : ByteArray) :
    RequestProgram NamespacePassive (Packet.readExact fuel fd amount bytes) := by
  induction fuel generalizing bytes with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold Packet.readExact
    split
    · exact .pure _
    · split
      · exact .pure _
      · apply RequestProgram.call (by trivial)
        intro reply
        repeat' first | exact .pure _ | exact ih _ | split

theorem packet_namespace_passive (fd : UInt64) : RequestProgram NamespacePassive (Packet.read fd) := by
  unfold Packet.read
  apply request_bind (packet_exact_namespace_passive _ _ _ _)
  intro header
  cases header with
  | error => exact .pure _
  | ok header =>
    dsimp only
    split
    · exact .pure _
    · apply request_bind (packet_exact_namespace_passive _ _ _ _)
      intro payload
      cases payload with
      | error => exact .pure _
      | ok payload =>
        dsimp only
        apply RequestProgram.call (by trivial)
        intro reply
        dsimp only [Filesystem.Program.bind]
        split
        · exact .pure _
        · split <;> exact .pure _

theorem write_loop_namespace_passive (fuel : Nat) (fd : UInt64) (bytes : ByteArray) (offset : Nat) :
    RequestProgram NamespacePassive (writeLoop fuel fd bytes offset) := by
  induction fuel generalizing offset with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold writeLoop
    split
    · exact .pure _
    · apply RequestProgram.call (by trivial)
      intro reply
      repeat' first | exact .pure _ | exact ih _ | split

theorem random_namespace_passive (fuel count : Nat) (bytes : ByteArray) :
    RequestProgram NamespacePassive (Directories.randomBytes fuel count bytes) := by
  induction fuel generalizing bytes with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold Directories.randomBytes
    split
    · exact .pure _
    · split
      · exact .pure _
      · apply RequestProgram.call (by trivial)
        intro reply
        repeat' first | exact .pure _ | exact ih _ | split

theorem namespace_passive_no_rename (request : Request) (passive : NamespacePassive request) :
    request.op ≠ .renameNew := by
  intro rename
  unfold NamespacePassive at passive
  rw [rename] at passive
  exact passive

theorem safe_program_no_rename {α : Type} {program : Filesystem.Program α}
    (safe : Publication.SafeProgram program) : RequestProgram (fun request => request.op ≠ .renameNew) program := by
  induction safe with
  | pure => exact .pure _
  | call permitted following ih => exact .call (Publication.safe_no_rename permitted) ih

theorem image_no_rename (runFd : UInt64) (bundle : Validation.Bundle) (overlay : List Image.Entry) :
    RequestProgram (fun request => request.op ≠ .renameNew) (Image.create runFd bundle overlay) := by
  unfold Image.create
  split
  · exact .pure _
  · apply request_bind (request_weaken
      (read_only_namespace_passive (Image.copyIdentified_readOnly _ _ _)) namespace_passive_no_rename)
    intro base
    cases base with
    | error => exact .pure _
    | ok base =>
      apply RequestProgram.call (by change Op.openAt ≠ Op.renameNew; decide)
      intro reply
      dsimp only [Filesystem.Program.bind]
      split
      · exact .pure _
      · apply request_weaken (Image.contentClose_requests _ _ _)
        intro request role rename
        rcases role with writing | closing
        · rw [writing.1] at rename; cases rename
        · rw [closing] at rename; cases rename

theorem run_create_no_rename :
    RequestProgram (fun request => request.op ≠ .renameNew) RunDirectory.create := by
  apply request_weaken RunDirectory.create_requests
  intro request role rename
  unfold RunDirectory.DirectoryRequest at role
  rw [rename] at role
  exact role

theorem run_cleanup_no_rename (run : RunDirectory.Owned) :
    RequestProgram (fun request => request.op ≠ .renameNew) (RunDirectory.cleanup run) := by
  apply request_weaken (RunDirectory.cleanup_requests run)
  intro request role rename
  unfold RunDirectory.CleanupRequest at role
  rw [rename] at role
  exact role

theorem validator_release_passive (run : RunDirectory.Owned) :
    RequestProgram NamespacePassive (Validation.releaseDirectory run) := by
  unfold Validation.releaseDirectory
  apply RequestProgram.call (by trivial)
  intro first
  dsimp only [Filesystem.Program.bind]
  apply RequestProgram.call (by trivial)
  intro second
  exact .pure _

end LeanCage.Host.Kernel
