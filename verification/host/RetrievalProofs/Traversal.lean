import RetrievalProofs.Effects

namespace LeanCage.Host.Retrieval

open Filesystem

def DirectoryOpening (uid : Nat) (parent : UInt64) (name : ByteArray)
    (events : List (Request × Reply)) (opened : Directories.Opened) : Prop :=
  ∃ reply information,
    events = [({ op := .openAt, first := parent, second := directoryFlags, left := name }, reply),
      ({ op := .stat, first := opened.fd }, information)] ∧
    descriptor reply = some opened.fd ∧ parseStat information = some opened.information ∧
    Directories.trusted uid opened.information = true

theorem directoryOpening_source (uid : Nat) (parent : UInt64) (name : ByteArray)
    {events : List (Request × Reply)} {opened : Directories.Opened}
    (run : Returns (Directories.openAt uid parent name) events (.ok opened)) :
    DirectoryOpening uid parent name events opened := by
  unfold Directories.openAt at run
  obtain ⟨reply, middle, rfl, tail⟩ := Snapshot.returns_call_split run
  split at tail
  · cases tail
  · rename_i fd recognized
    unfold Directories.inspect at tail
    obtain ⟨information, last, rfl, final⟩ := Snapshot.returns_call_split tail
    split at final
    · have impossible := (Snapshot.closeResult_provenance _ _ final).1
      cases impossible
    · rename_i stat statRead
      split at final
      · rename_i trusted
        obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
        cases same
        exact ⟨reply, information, rfl, recognized, statRead, trusted⟩
      · have impossible := (Snapshot.closeResult_provenance _ _ final).1
        cases impossible

inductive Traversal {α : Type} (uid : Nat) (action : UInt64 → Filesystem.Program (Result α)) :
    UInt64 → List String → List (Request × Reply) → α → Prop where
  | root (parent : UInt64) (events : List (Request × Reply)) (value : α)
      (called : Returns (action parent) events (.ok value)) : Traversal uid action parent [] events value
  | child (parent : UInt64) (name : String) (rest : List String) (opened : Directories.Opened)
      (opening middle closing : List (Request × Reply)) (value : α)
      (component : Snapshot.ValidComponent name)
      (openedSource : DirectoryOpening uid parent name.toUTF8 opening opened)
      (below : Traversal uid action opened.fd rest middle value)
      (closed : Returns (closeResult opened.fd (.ok value)) closing (.ok value)) :
      Traversal uid action parent (name :: rest) (opening ++ middle ++ closing) value

-- §FS-host-boundary.ownership: Each descendant action runs while its actual ancestors remain held.
theorem under_source {α : Type} (uid : Nat) (parent : UInt64) (parts : List String)
    (action : UInt64 → Filesystem.Program (Result α))
    {events : List (Request × Reply)} {value : α}
    (run : Returns (Publication.under uid parent parts false action) events (.ok value)) :
    Traversal uid action parent parts events value := by
  induction parts generalizing parent events with
  | nil => exact .root _ _ _ run
  | cons name rest ih =>
    simp only [Publication.under] at run
    split at run
    · cases run
    · rename_i component
      simp only [Bool.false_eq_true, ↓reduceIte] at run
      obtain ⟨opening, result, tail, openedRun, afterOpen, shape⟩ := Snapshot.returns_bind_split _ _ run
      cases result with
      | error => cases afterOpen
      | ok opened =>
        obtain ⟨middle, result, closing, called, closed, closeShape⟩ :=
          Snapshot.returns_bind_split _ _ afterOpen
        have same := (Snapshot.closeResult_provenance _ _ closed).1
        cases same
        have observed := Traversal.child parent name rest opened opening middle closing value
          (by simpa using component) (directoryOpening_source _ _ _ openedRun) (ih _ called) closed
        simpa only [shape, closeShape, List.append_assoc] using observed

-- §FS-host-boundary.ownership: The exact leaf descriptor comes from the retained traversal chain.
theorem traversal_leaf {α : Type} {uid : Nat} {action : UInt64 → Filesystem.Program (Result α)}
    {root : UInt64} {parts : List String} {events : List (Request × Reply)} {value : α}
    (observed : Traversal uid action root parts events value) :
    ∃ parent leaf, Returns (action parent) leaf (.ok value) ∧ ∀ event ∈ leaf, event ∈ events := by
  induction observed with
  | root parent events value called => exact ⟨parent, events, called, fun _ member => member⟩
  | child parent name rest opened opening middle closing value component openedSource below closed ih =>
    obtain ⟨parent, leaf, called, subset⟩ := ih
    exact ⟨parent, leaf, called, by intro event member; simp [subset event member]⟩

end LeanCage.Host.Retrieval
