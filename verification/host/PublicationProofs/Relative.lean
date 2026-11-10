import PublicationProofs.Creation
import PublicationProofs.Writes

namespace LeanCage.Host.Publication

open Filesystem

def EnsuredOpening (uid : Nat) (parent : UInt64) (name : ByteArray)
    (events : List (Request × Reply)) (child : Directories.Opened) : Prop :=
  ∃ made opening,
    events = ({op := .mkdirAt, first := parent, second := 448, left := name}, made) :: opening ∧
    ((made.1 = 0 ∧ made.2 = .empty) ∨ (nativeError made = true ∧ errorNumber made = 17)) ∧
    Retrieval.DirectoryOpening uid parent name opening child

theorem ensureAt_source (uid : Nat) (parent : UInt64) (name : ByteArray)
    {events : List (Request × Reply)} {child : Directories.Opened}
    (run : Returns (Directories.ensureAt uid parent name) events (.ok child)) :
    EnsuredOpening uid parent name events child := by
  unfold Directories.ensureAt at run
  obtain ⟨made, opening, rfl, tail⟩ := Snapshot.returns_call_split run
  dsimp only [Filesystem.Program.bind] at tail
  split at tail
  · rename_i madeGood
    have fields : made.1 = 0 ∧ made.2.isEmpty = true := by simpa using madeGood
    exact ⟨made, opening, rfl, .inl ⟨fields.1, ByteArray.size_eq_zero_iff.mp
      (by simpa only [ByteArray.isEmpty, beq_iff_eq] using fields.2)⟩,
      Retrieval.directoryOpening_source _ _ _ tail⟩
  · split at tail
    · rename_i existsAlready
      have fields : nativeError made = true ∧ errorNumber made = 17 := by simpa using existsAlready
      exact ⟨made, opening, rfl, .inr fields, Retrieval.directoryOpening_source _ _ _ tail⟩
    · cases tail

def DescendantOpening (uid : Nat) (parent : UInt64) (name : ByteArray) (create : Bool)
    (events : List (Request × Reply)) (child : Directories.Opened) : Prop :=
  if create then EnsuredOpening uid parent name events child
  else Retrieval.DirectoryOpening uid parent name events child

inductive RelativeTraversal {α : Type} (uid : Nat) (create : Bool)
    (action : UInt64 → Filesystem.Program (Result α)) :
    UInt64 → List String → List (Request × Reply) → α → Prop where
  | root (parent : UInt64) (events : List (Request × Reply)) (value : α)
      (called : Returns (action parent) events (.ok value)) :
      RelativeTraversal uid create action parent [] events value
  | child (parent : UInt64) (name : String) (rest : List String) (opened : Directories.Opened)
      (opening middle closing : List (Request × Reply)) (value : α)
      (component : Snapshot.ValidComponent name)
      (openedSource : DescendantOpening uid parent name.toUTF8 create opening opened)
      (below : RelativeTraversal uid create action opened.fd rest middle value)
      (closed : Returns (closeResult opened.fd (.ok value)) closing (.ok value)) :
      RelativeTraversal uid create action parent (name :: rest) (opening ++ middle ++ closing) value

-- §FS-host-boundary.ownership: Creation and use retain each actual relative directory until close.
theorem under_source {α : Type} (uid : Nat) (parent : UInt64) (parts : List String) (create : Bool)
    (action : UInt64 → Filesystem.Program (Result α))
    {events : List (Request × Reply)} {value : α}
    (run : Returns (under uid parent parts create action) events (.ok value)) :
    RelativeTraversal uid create action parent parts events value := by
  induction parts generalizing parent events with
  | nil => exact .root _ _ _ run
  | cons name rest ih =>
    unfold under at run
    split at run
    · cases run
    · rename_i valid
      cases create <;> simp only [Bool.false_eq_true, ↓reduceIte] at run
      all_goals
        obtain ⟨opening, result, restEvents, opened, afterOpen, shape⟩ := Snapshot.returns_bind_split _ _ run
        cases result with
        | error => cases afterOpen
        | ok child =>
          obtain ⟨middle, result, closing, called, closed, closeShape⟩ :=
            Snapshot.returns_bind_split _ _ afterOpen
          have same := (Snapshot.closeResult_provenance _ _ closed).1
          cases same
          rw [shape, closeShape, ← List.append_assoc]
          apply RelativeTraversal.child parent name rest child opening middle closing value
          · simpa using valid
          · first | exact Retrieval.directoryOpening_source _ _ _ opened | exact ensureAt_source _ _ _ opened
          · exact ih _ called
          · exact closed

def RelativeWrite (uid : Nat) (root : UInt64) (file : Artifacts.ValidatedFile)
    (events : List (Request × Reply)) : Prop :=
  ∃ name, file.path.components.getLast? = some name ∧ Snapshot.ValidComponent name ∧
    RelativeTraversal uid false
      (fun parent => writeNew parent name.toUTF8 file.bytes (if file.executable then 448 else 384))
      root file.path.components.dropLast events ()

theorem writeRelative_source (uid : Nat) (root : UInt64) (file : Artifacts.ValidatedFile)
    {events : List (Request × Reply)} (run : Returns (writeRelative uid root file) events (.ok ())) :
    RelativeWrite uid root file events := by
  unfold writeRelative at run
  dsimp only at run
  split at run
  · rename_i name named
    have member : name ∈ file.path.components := List.mem_of_getLast? named
    have component : Snapshot.ValidComponent name := file.path.valid.2.2.2 name member
    exact ⟨name, named, component, under_source _ _ _ _ _ run⟩
  · cases run

theorem relativeTraversal_leaf {α : Type} {uid : Nat} {create : Bool}
    {action : UInt64 → Filesystem.Program (Result α)} {root : UInt64} {parts : List String}
    {events : List (Request × Reply)} {value : α}
    (observed : RelativeTraversal uid create action root parts events value) :
    ∃ parent leaf, Returns (action parent) leaf (.ok value) ∧ ∀ event ∈ leaf, event ∈ events := by
  induction observed with
  | root parent events value called => exact ⟨parent, events, called, fun _ member => member⟩
  | child parent name rest opened opening middle closing value component openedSource below closed ih =>
    obtain ⟨parent, leaf, called, subset⟩ := ih
    exact ⟨parent, leaf, called, by intro event member; simp [subset event member]⟩

-- §FS-host-boundary.publication: The final new file receives the validated bytes and mode.
theorem relativeWrite_leaf {uid : Nat} {root : UInt64} {file : Artifacts.ValidatedFile}
    {events : List (Request × Reply)} (observed : RelativeWrite uid root file events) :
    ∃ name parent writing,
      file.path.components.getLast? = some name ∧ Snapshot.ValidComponent name ∧
      NewFileWrite parent name.toUTF8 file.bytes (if file.executable then 448 else 384) writing ∧
      ∀ event ∈ writing, event ∈ events := by
  obtain ⟨name, named, component, traversed⟩ := observed
  obtain ⟨parent, writing, written, included⟩ := relativeTraversal_leaf traversed
  exact ⟨name, parent, writing, named, component, writeNew_source _ _ _ _ written, included⟩

end LeanCage.Host.Publication
