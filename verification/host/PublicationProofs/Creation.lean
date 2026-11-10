import PublicationProofs.Directories

namespace LeanCage.Host.Publication

open Filesystem

theorem randomBytes_size (fuel count : Nat) (bytes : ByteArray)
    {events : List (Request × Reply)} {random : ByteArray}
    (run : Returns (Directories.randomBytes fuel count bytes) events (.ok random)) : random.size = count := by
  induction fuel generalizing bytes events with
  | zero => cases run
  | succ fuel ih =>
    unfold Directories.randomBytes at run
    split at run
    · cases run
    · split at run
      · rename_i exactSize
        obtain ⟨_, same⟩ := Snapshot.returns_pure_eq run
        cases same
        simpa using exactSize
      · obtain ⟨reply, rest, rfl, tail⟩ := Snapshot.returns_call_split run
        split at tail
        · cases tail
        · split at tail
          · cases tail
          · exact ih _ tail

def CreatedObservation (uid : Nat) (parent : UInt64) (prefixName : String)
    (events : List (Request × Reply)) (child : Directories.NewDirectory) : Prop :=
  ∃ random randomEvents made opening,
    events = randomEvents ++ [({op := .mkdirAt, first := parent, second := 448, left := child.name}, made)] ++ opening ∧
    Returns (Directories.randomBytes 17 16 .empty) randomEvents (.ok random) ∧ random.size = 16 ∧
    child.name = (prefixName ++ Snapshot.hex random).toUTF8 ∧ Directories.component child.name = true ∧
    made.1 = 0 ∧ made.2 = .empty ∧ Retrieval.DirectoryOpening uid parent child.name opening child.directory ∧
    child.directory.information.uid = uid ∧ (child.directory.information.mode &&& 511) = 448

-- §FS-host-boundary.ownership: Freshness requires acknowledged mkdir, never probabilistic names.
theorem newChild_source (uid : Nat) (parent : UInt64) (prefixName : String)
    {events : List (Request × Reply)} {child : Directories.NewDirectory}
    (run : Returns (Directories.newChild uid parent prefixName) events (.ok child)) :
    CreatedObservation uid parent prefixName events child := by
  unfold Directories.newChild at run
  obtain ⟨randomEvents, result, rest, randomRun, afterRandom, shape⟩ := Snapshot.returns_bind_split _ _ run
  cases result with
  | error => cases afterRandom
  | ok random =>
    dsimp only at afterRandom
    split at afterRandom
    · cases afterRandom
    · rename_i checked
      obtain ⟨made, openingEvents, rfl, afterMkdir⟩ := Snapshot.returns_call_split afterRandom
      dsimp only [Filesystem.Program.bind] at afterMkdir
      split at afterMkdir
      · cases afterMkdir
      · rename_i madeGood
        obtain ⟨opening, result, last, opened, final, openShape⟩ := Snapshot.returns_bind_split _ _ afterMkdir
        cases result with
        | error => cases final
        | ok directory =>
          dsimp only at final
          split at final
          · have impossible := (Snapshot.closeResult_provenance _ _ final).1; cases impossible
          · rename_i owned
            obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
            cases same
            have madeFields : made.1 = 0 ∧ made.2.isEmpty = true := by
              simpa [Bool.or_eq_true] using madeGood
            have ownedFields : directory.information.uid = uid ∧
                directory.information.mode &&& 511 = 448 := by simpa [Bool.or_eq_true] using owned
            refine ⟨random, randomEvents, made, opening, ?_, randomRun, randomBytes_size _ _ _ randomRun,
              rfl, by simpa using checked, madeFields.1, ?_, Retrieval.directoryOpening_source _ _ _ opened,
              ownedFields.1, ownedFields.2⟩
            · simpa only [openShape, List.append_nil, List.append_assoc, List.singleton_append,
                List.cons_append, List.nil_append] using shape
            · exact ByteArray.size_eq_zero_iff.mp
                (by simpa only [ByteArray.isEmpty, beq_iff_eq] using madeFields.2)

def FreshObservation (parent : Directories.Parent) (events : List (Request × Reply))
    (stage : Directories.Fresh) : Prop :=
  ∃ opening creation,
    events = opening ++ creation ∧
    Retrieval.DirectoryOpening parent.uid parent.directory.fd ".".toUTF8 opening stage.container ∧
    CreatedObservation parent.uid stage.container.fd PrivateNames.prefixText creation stage.toNewDirectory

theorem fresh_source (parent : Directories.Parent) {events : List (Request × Reply)}
    {stage : Directories.Fresh} (run : Returns (Directories.fresh parent) events (.ok stage)) :
    FreshObservation parent events stage := by
  unfold Directories.fresh at run
  obtain ⟨opening, result, rest, opened, afterOpen, shape⟩ := Snapshot.returns_bind_split _ _ run
  cases result with
  | error => cases afterOpen
  | ok container =>
    obtain ⟨creation, result, last, created, final, createShape⟩ := Snapshot.returns_bind_split _ _ afterOpen
    cases result with
    | error => have impossible := (Snapshot.closeResult_provenance _ _ final).1; cases impossible
    | ok child =>
      obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
      cases same
      exact ⟨opening, creation, by simpa only [createShape, List.append_nil] using shape,
        Retrieval.directoryOpening_source _ _ _ opened, newChild_source _ _ _ created⟩

end LeanCage.Host.Publication
