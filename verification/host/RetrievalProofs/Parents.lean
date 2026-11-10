import RetrievalProofs.Traversal

namespace LeanCage.Host.Retrieval

open Filesystem

def DirectoryInspection (uid : Nat) (fd : UInt64) (events : List (Request × Reply))
    (opened : Directories.Opened) : Prop :=
  opened.fd = fd ∧ ∃ reply, events = [({ op := .stat, first := fd }, reply)] ∧
    parseStat reply = some opened.information ∧ Directories.trusted uid opened.information = true

theorem directoryInspection_source (uid : Nat) (fd : UInt64)
    {events : List (Request × Reply)} {opened : Directories.Opened}
    (run : Returns (Directories.inspect uid fd) events (.ok opened)) :
    DirectoryInspection uid fd events opened := by
  unfold Directories.inspect at run
  obtain ⟨reply, rest, rfl, tail⟩ := Snapshot.returns_call_split run
  split at tail
  · have impossible := (Snapshot.closeResult_provenance _ _ tail).1; cases impossible
  · rename_i information parsed
    split at tail
    · rename_i trusted
      obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq tail
      cases same
      exact ⟨rfl, reply, rfl, parsed, trusted⟩
    · have impossible := (Snapshot.closeResult_provenance _ _ tail).1; cases impossible

def ParentObservation (path : ByteArray) (create : Bool) (events : List (Request × Reply))
    (parent : Directories.Parent) : Prop :=
  ∃ selected identity base selecting inspecting descending,
    events = selecting ++ [({ op := .euid }, identity)] ++ inspecting ++ descending ∧
    Snapshot.StartObservation path selected selecting ∧ selected.parts.getLast? = some parent.name ∧
    parent.name ≠ ".".toUTF8 ∧ parent.name ≠ "..".toUTF8 ∧
    nativeError identity = false ∧ identity.2 = .empty ∧ identity.1.toNat ≤ 2 ^ 32 - 1 ∧
    parent.uid = identity.1.toNat ∧ DirectoryInspection parent.uid selected.base inspecting base ∧
    Returns (Directories.descend parent.uid create base selected.parts.dropLast)
      descending (.ok parent.directory)

-- §FS-host-boundary.ownership: Parent selection retains the same raw CWD/root and checked FD.
theorem parent_source (path : ByteArray) (create : Bool)
    {events : List (Request × Reply)} {parent : Directories.Parent}
    (run : Returns (Directories.parent path create) events (.ok parent)) :
    ParentObservation path create events parent := by
  unfold Directories.parent at run
  obtain ⟨selecting, result, rest, selectedRun, afterSelect, shape⟩ := Snapshot.returns_bind_split _ _ run
  cases result with
  | error => cases afterSelect
  | ok selected =>
    dsimp only at afterSelect
    split at afterSelect
    · rename_i name named
      split at afterSelect
      · have impossible := (Snapshot.closeResult_provenance _ _ afterSelect).1; cases impossible
      · rename_i fresh
        obtain ⟨identity, later, rfl, afterIdentity⟩ := Snapshot.returns_call_split afterSelect
        dsimp only [Filesystem.Program.bind] at afterIdentity
        split at afterIdentity
        · have impossible := (Snapshot.closeResult_provenance _ _ afterIdentity).1; cases impossible
        · rename_i valid
          obtain ⟨inspecting, result, descendingEvents, inspected, afterInspect, inspectShape⟩ :=
            Snapshot.returns_bind_split _ _ afterIdentity
          cases result with
          | error => cases afterInspect
          | ok base =>
            obtain ⟨descending, result, last, descended, final, descendShape⟩ :=
              Snapshot.returns_bind_split _ _ afterInspect
            obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
            cases result with
            | error => cases same
            | ok directory =>
              cases same
              have freshFields : name ≠ ".".toUTF8 ∧ name ≠ "..".toUTF8 := by
                simpa [Bool.or_eq_true] using fresh
              have fields : nativeError identity = false ∧ identity.2.isEmpty = true ∧
                  identity.1.toNat ≤ 2 ^ 32 - 1 := by
                simpa [Bool.or_eq_true, and_assoc] using valid
              refine ⟨selected, identity, base, selecting, inspecting, descending, ?_,
                Snapshot.sourceStart_source _ selectedRun, named, freshFields.1, freshFields.2,
                fields.1, ?_, fields.2.2, rfl, directoryInspection_source _ _ inspected, descended⟩
              · simpa only [inspectShape, descendShape, List.append_nil, List.append_assoc,
                  List.singleton_append, List.cons_append, List.nil_append] using shape
              · exact ByteArray.size_eq_zero_iff.mp
                  (by simpa only [ByteArray.isEmpty, beq_iff_eq] using fields.2.1)
    · have impossible := (Snapshot.closeResult_provenance _ _ afterSelect).1; cases impossible

end LeanCage.Host.Retrieval
