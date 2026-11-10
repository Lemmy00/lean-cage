import PublicationProofs.Relative

namespace LeanCage.Host.Publication
open Filesystem

def PlannedDirectories (uid : Nat) (root : UInt64) (paths : List Artifacts.ExportPath)
    (events : List (Request × Reply)) : Prop :=
  ActionTrace (fun path => under uid root path.components true (fun _ => pure (.ok ())))
    (paths.mergeSort (fun a b => a.components.length ≤ b.components.length)) events

theorem directories_source (uid : Nat) (root : UInt64) (paths : List Artifacts.ExportPath)
    {events : List (Request × Reply)} (run : Returns (directories uid root paths) events (.ok ())) :
    PlannedDirectories uid root paths events := by
  change Returns (checkedActions (fun path => under uid root path.components true (fun _ => pure (.ok ())))
    (paths.mergeSort (fun a b => a.components.length ≤ b.components.length)) (pure (.ok ()))) events (.ok ()) at run
  obtain ⟨first, last, shape, traced, final⟩ := checkedActions_source _ _ _ run
  obtain ⟨rfl, _⟩ := Snapshot.returns_pure_eq final
  unfold PlannedDirectories
  rw [shape, List.append_nil]
  exact traced

def ExportsObservation (uid : Nat) (stage : UInt64) (input : Input) (events : List (Request × Reply)) : Prop :=
  ∃ made root opening making writing closing,
    events = [({op := .mkdirAt, first := stage, second := 448, left := "export".toUTF8}, made)] ++
      opening ++ making ++ writing ++ closing ∧
    made.1 = 0 ∧ made.2 = .empty ∧ Retrieval.DirectoryOpening uid stage "export".toUTF8 opening root ∧
    PlannedDirectories uid root.fd (input.validated.map (·.dirs) |>.getD []) making ∧
    ActionTrace (writeRelative uid root.fd) input.outcome.files writing ∧
    Returns (closeResult root.fd (.ok ())) closing (.ok ())

-- §FS-host-boundary.publication: Export creation and writes use the actual opened stage child.
theorem exports_source (uid : Nat) (stage : UInt64) (input : Input)
    {events : List (Request × Reply)} (run : Returns (exports uid stage input) events (.ok ())) :
    ExportsObservation uid stage input events := by
  unfold exports at run
  obtain ⟨made, rest, rfl, afterMkdir⟩ := Snapshot.returns_call_split run
  dsimp only [Filesystem.Program.bind] at afterMkdir
  split at afterMkdir
  · cases afterMkdir
  · rename_i madeGood
    obtain ⟨opening, result, later, opened, afterOpen, shape⟩ := Snapshot.returns_bind_split _ _ afterMkdir
    cases result with
    | error => cases afterOpen
    | ok root =>
      obtain ⟨filling, result, closing, filled, closed, closeShape⟩ := Snapshot.returns_bind_split _ _ afterOpen
      have same := (Snapshot.closeResult_provenance _ _ closed).1
      cases same
      obtain ⟨making, result, writingEvents, madeDirs, afterDirs, dirsShape⟩ :=
        Snapshot.returns_bind_split _ _ filled
      cases result with
      | error => cases afterDirs
      | ok madeUnit =>
        change Returns (checkedActions (writeRelative uid root.fd) input.outcome.files (pure (.ok ())))
          writingEvents (.ok ()) at afterDirs
        obtain ⟨writing, last, fileShape, written, final⟩ := checkedActions_source _ _ _ afterDirs
        obtain ⟨rfl, _⟩ := Snapshot.returns_pure_eq final
        have madeFields : made.1 = 0 ∧ made.2.isEmpty = true := by simpa [Bool.or_eq_true] using madeGood
        refine ⟨made, root, opening, making, writing, closing, ?_, madeFields.1, ?_,
          Retrieval.directoryOpening_source _ _ _ opened, directories_source _ _ _ madeDirs, written, closed⟩
        · simp only [shape, closeShape, dirsShape, fileShape, List.append_nil, List.append_assoc,
            List.cons_append, List.nil_append]
        · exact ByteArray.size_eq_zero_iff.mp
            (by simpa only [ByteArray.isEmpty, beq_iff_eq] using madeFields.2)

end LeanCage.Host.Publication
