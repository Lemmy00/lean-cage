import FilesystemSourceFrames
import PublicationProofs.Creation
import RetrievalProofs.Directories
import RunDirectoryProofs.Requests

namespace LeanCage.Host.Kernel
open Filesystem

private theorem list_prefix_append (first last : List UInt8) : first.isPrefixOf (first ++ last) = true := by
  induction first with
  | nil => rfl
  | cons head tail ih => simp

theorem private_prefix_reserved (suffix : String) :
    PrivateNames.reservedBytes (PrivateNames.prefixText ++ suffix).toUTF8 = true := by
  change PrivateNames.prefixText.toByteArray.data.toList.isPrefixOf
    (PrivateNames.prefixText ++ suffix).toByteArray.data.toList = true
  rw [String.toByteArray_append, ByteArray.data_append, Array.toList_append]
  exact list_prefix_append _ _

theorem created_child_reserved (uid : Nat) (parent : UInt64) {events : List (Request × Reply)}
    {child : Directories.NewDirectory}
    (source : Returns (Directories.newChild uid parent PrivateNames.prefixText) events (.ok child)) :
    PrivateNames.reservedBytes child.name = true := by
  obtain ⟨random, _, _, _, _, _, _, name, _⟩ := Publication.newChild_source _ _ _ source
  rw [name]
  exact private_prefix_reserved _

def PrivateMkdirRole (parent : UInt64) (request : Request) : Prop :=
  request.op = .mkdirAt → request.first = parent ∧ request.second = 448 ∧
    Directories.component request.left = true ∧ PrivateNames.reservedBytes request.left = true

private theorem random_creation_role (parent : UInt64) (fuel count : Nat) (bytes : ByteArray) :
    RequestProgram (PrivateMkdirRole parent) (Directories.randomBytes fuel count bytes) := by
  induction fuel generalizing bytes with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold Directories.randomBytes
    split
    · exact .pure _
    · split
      · exact .pure _
      · apply RequestProgram.call (by intro impossible; cases impossible)
        intro reply
        split
        · exact .pure _
        · split
          · exact .pure _
          · exact ih _

private theorem readonly_creation_role {α : Type} (parent : UInt64) {program : Filesystem.Program α}
    (source : Retrieval.ReadOnly program) : RequestProgram (PrivateMkdirRole parent) program := by
  induction source with
  | pure => exact .pure _
  | @call request next allowed rest ih =>
    apply RequestProgram.call _ ih
    intro mkdir
    unfold Retrieval.Allowed at allowed
    rw [mkdir] at allowed
    exact False.elim allowed

-- §FS-host-boundary.ownership: Every partial creation path uses the actual reserved child argument.
theorem private_child_creation_role (uid : Nat) (parent : UInt64) :
    RequestProgram (PrivateMkdirRole parent) (Directories.newChild uid parent PrivateNames.prefixText) := by
  unfold Directories.newChild
  apply request_bind (random_creation_role parent _ _ _)
  intro random
  cases random with
  | error => exact .pure _
  | ok bytes =>
    dsimp only
    split
    · exact .pure _
    · rename_i checked
      apply RequestProgram.call
      · intro mkdir
        refine ⟨rfl, rfl, ?_, private_prefix_reserved _⟩
        simpa using checked
      · intro reply
        dsimp only [Filesystem.Program.bind]
        split
        · exact .pure _
        · apply request_bind (readonly_creation_role parent (Retrieval.openAt_readOnly _ _ _))
          intro opened
          cases opened with
          | error => exact .pure _
          | ok directory =>
            dsimp only
            split
            · exact readonly_creation_role parent
                (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
            · exact .pure _

theorem actual_private_child_mkdir (uid : Nat) (parent : UInt64)
    {events : List (Request × Option Reply)}
    (source : Prefix (Directories.newChild uid parent PrivateNames.prefixText) events)
    (event : Request × Option Reply) (member : event ∈ events) (mkdir : event.1.op = .mkdirAt) :
    event.1.first = parent ∧ event.1.second = 448 ∧ Directories.component event.1.left = true ∧
      PrivateNames.reservedBytes event.1.left = true :=
  request_prefix (private_child_creation_role uid parent) source event member mkdir

end LeanCage.Host.Kernel
