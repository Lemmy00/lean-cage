import LeanCageHost.RunDirectory
import PublicationProofs

namespace LeanCage.Host.RunDirectory
open Filesystem

def TemporaryParent (events : List (Request × Reply)) (container : Directories.Opened) (uid : Nat) : Prop :=
  ∃ reply opening, events = ({op := .euid}, reply) :: opening ∧
    nativeError reply = false ∧ reply.2 = .empty ∧ uid = reply.1.toNat ∧ uid ≤ 2 ^ 32 - 1 ∧
    Retrieval.DirectoryOpening uid cwd "/tmp".toUTF8 opening container

theorem temporaryParent_source {events : List (Request × Reply)} {answer : Directories.Opened × String × Nat}
    (run : Returns Directories.temporaryParent events (.ok answer)) :
    answer.2.1 = "/tmp" ∧ TemporaryParent events answer.1 answer.2.2 := by
  unfold Directories.temporaryParent at run
  obtain ⟨reply, rest, rfl, afterUid⟩ := Snapshot.returns_call_split run
  dsimp only [Filesystem.Program.bind] at afterUid
  split at afterUid
  · cases afterUid
  · rename_i valid
    obtain ⟨opening, result, last, opened, final, shape⟩ := Snapshot.returns_bind_split _ _ afterUid
    cases result with
    | error => cases final
    | ok container =>
      obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
      cases same
      have fields : nativeError reply = false ∧ reply.2.isEmpty = true ∧ reply.1.toNat ≤ 2 ^ 32 - 1 := by
        simpa [Bool.or_eq_true, and_assoc] using valid
      refine ⟨rfl, reply, opening, ?_, fields.1, ?_, rfl, fields.2.2,
        Retrieval.directoryOpening_source _ _ _ opened⟩
      · simp only [shape, List.append_nil]
      · exact ByteArray.size_eq_zero_iff.mp
          (by simpa only [ByteArray.isEmpty, beq_iff_eq] using fields.2.1)

def Creation (events : List (Request × Reply)) (owned : Owned) : Prop :=
  ∃ uid child selected creating marked name,
    events = selected ++ creating ++ [({
      op := .setAttribute
      first := owned.directory.fd
      left := PrivateNames.attributeName
      right := PrivateNames.attributeValue }, marked)] ∧
    TemporaryParent selected owned.container uid ∧
    Publication.CreatedObservation uid owned.container.fd PrivateNames.prefixText creating child ∧
    owned.directory = child.directory ∧ owned.name = child.name ∧
    marked.1 = 0 ∧ marked.2 = .empty ∧ String.fromUTF8? child.name = some name ∧
    owned.path = "/tmp" ++ "/" ++ name ∧ owned.path.toUTF8.size + "/control.sock".toUTF8.size ≤ 107

-- §FS-host-boundary.ownership: Actual exclusive creation and private marking precede run exposure.
theorem create_source {events : List (Request × Reply)} {owned : Owned}
    (run : Returns create events (.ok owned)) : Creation events owned := by
  unfold create at run
  obtain ⟨selected, result, rest, selectedRun, afterSelect, shape⟩ := Snapshot.returns_bind_split _ _ run
  cases result with
  | error => cases afterSelect
  | ok area =>
    rcases area with ⟨container, areaPath, uid⟩
    obtain ⟨creating, result, later, created, afterCreate, createShape⟩ :=
      Snapshot.returns_bind_split _ _ afterSelect
    cases result with
    | error => have impossible := (Snapshot.closeResult_provenance _ _ afterCreate).1; cases impossible
    | ok child =>
      obtain ⟨marked, last, rfl, afterMarked⟩ := Snapshot.returns_call_split afterCreate
      dsimp only [Filesystem.Program.bind] at afterMarked
      split at afterMarked
      · obtain ⟨_, rest, rfl, afterClose⟩ := Snapshot.returns_call_split afterMarked
        dsimp only [Filesystem.Program.bind] at afterClose
        obtain ⟨_, rest, rfl, afterUnlink⟩ := Snapshot.returns_call_split afterClose
        dsimp only [Filesystem.Program.bind] at afterUnlink
        have impossible := (Snapshot.closeResult_provenance _ _ afterUnlink).1
        cases impossible
      · rename_i markedGood
        split at afterMarked
        · obtain ⟨_, rest, rfl, afterClose⟩ := Snapshot.returns_call_split afterMarked
          dsimp only [Filesystem.Program.bind] at afterClose
          have impossible := (Snapshot.closeResult_provenance _ _ afterClose).1
          cases impossible
        · rename_i name decoded
          split at afterMarked
          · obtain ⟨_, rest, rfl, afterClose⟩ := Snapshot.returns_call_split afterMarked
            dsimp only [Filesystem.Program.bind] at afterClose
            have impossible := (Snapshot.closeResult_provenance _ _ afterClose).1
            cases impossible
          · rename_i bounded
            obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq afterMarked
            cases same
            obtain ⟨areaRoot, selected⟩ := temporaryParent_source selectedRun
            dsimp only at areaRoot selected
            subst areaPath
            have fields : marked.1 = 0 ∧ marked.2.isEmpty = true := by
              simpa [Bool.or_eq_true] using markedGood
            refine ⟨uid, child, _, creating, marked, name, ?_, selected,
              Publication.newChild_source _ _ _ created, rfl, rfl, fields.1, ?_, decoded, rfl, ?_⟩
            · simpa only [createShape, List.append_assoc, List.singleton_append, List.cons_append,
                List.nil_append] using shape
            · exact ByteArray.size_eq_zero_iff.mp
                (by simpa only [ByteArray.isEmpty, beq_iff_eq] using fields.2)
            · dsimp only
              omega

end LeanCage.Host.RunDirectory
