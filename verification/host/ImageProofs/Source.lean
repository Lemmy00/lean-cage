import ImageProofs.Writes

namespace LeanCage.Host.Image
open Filesystem

def BaseObservation (bundle : Validation.Bundle) (events : List (Request × Reply)) (bytes : ByteArray) : Prop :=
  ∃ files name expected copied reading hashing digest,
    Validation.bundleFiles bundle.manifest = some files ∧
    files.find? (fun field => field.1 == "profile/runtime.cpio.gz") = some (name, .string expected) ∧
    events = reading ++ hashing ∧ copied.bytes = bytes ∧ bytes.size ≤ workspaceMax ∧
    Snapshot.OpenedCopy cwd (bundle.root ++ "/" ++ "profile/runtime.cpio.gz").toUTF8 reading copied ∧
    Returns (Filesystem.hash bytes) hashing (.ok digest) ∧ Snapshot.hex digest = expected

-- §FS-host-boundary.snapshot: The base archive comes from the same identified bootstrap copy/hash.
theorem base_source (bundle : Validation.Bundle) {events : List (Request × Reply)} {bytes : ByteArray}
    (run : Returns (Validation.copyIdentified bundle "profile/runtime.cpio.gz" workspaceMax) events (.ok bytes)) :
    BaseObservation bundle events bytes := by
  unfold Validation.copyIdentified at run
  split at run
  · rename_i files inventory
    split at run
    · rename_i name expected identified
      obtain ⟨reading, result, rest, readRun, afterRead, shape⟩ := Snapshot.returns_bind_split _ _ run
      cases result with
      | error => cases afterRead
      | ok data =>
        obtain ⟨hashing, result, last, hashed, final, hashShape⟩ := Snapshot.returns_bind_split _ _ afterRead
        cases result with
        | error => cases final
        | ok digest =>
          dsimp only at final
          split at final
          · rename_i matched
            obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
            cases same
            unfold readBounded at readRun
            obtain ⟨copies, result, last, copiedRun, finalRead, readShape⟩ := Snapshot.returns_bind_split _ _ readRun
            obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq finalRead
            cases result with
            | error => cases same
            | ok copied =>
              cases same
              obtain ⟨bounded, copiedFrom⟩ := Snapshot.copyAt_provenance _ _ _ copiedRun
              refine ⟨files, name, expected, copied, copies, hashing, digest, inventory, identified,
                ?_, rfl, bounded, copiedFrom, hashed, by simpa using matched⟩
              simpa only [readShape, hashShape, List.append_nil] using shape
          · cases final
    · cases run
  · cases run

def Creation (run : UInt64) (bundle : Validation.Bundle) (overlay : List Entry)
    (events : List (Request × Reply)) : Prop :=
  overlayValid overlay = true ∧ ∃ base fd copied opened writing closing,
    events = copied ++ [({
      op := .openAt
      first := run
      second := newFileFlags
      third := 384
      left := "request.cpio".toUTF8 }, opened)] ++ writing ++ closing ∧
    BaseObservation bundle copied base ∧ descriptor opened = some fd ∧
    ContentObservation fd base overlay writing ∧ Returns (closeResult fd (.ok ())) closing (.ok ())

-- §FS-host-boundary.ownership: Actual archive content uses the same exclusive-open run descriptor.
theorem create_source (runFd : UInt64) (bundle : Validation.Bundle) (overlay : List Entry)
    {events : List (Request × Reply)} (run : Returns (create runFd bundle overlay) events (.ok ())) :
    Creation runFd bundle overlay events := by
  unfold create at run
  split at run
  · cases run
  · rename_i bounded
    obtain ⟨copied, result, rest, copiedRun, afterCopy, shape⟩ := Snapshot.returns_bind_split _ _ run
    cases result with
    | error => cases afterCopy
    | ok base =>
      obtain ⟨opened, later, rfl, afterOpen⟩ := Snapshot.returns_call_split afterCopy
      dsimp only [Filesystem.Program.bind] at afterOpen
      split at afterOpen
      · cases afterOpen
      · rename_i fd recognized
        obtain ⟨writing, result, closing, written, closed, writeShape⟩ := Snapshot.returns_bind_split _ _ afterOpen
        have same := (Snapshot.closeResult_provenance _ _ closed).1
        cases same
        refine ⟨by simpa using bounded, base, fd, copied, opened, writing, closing, ?_,
          base_source _ copiedRun, recognized, content_source _ _ _ written, closed⟩
        simpa only [writeShape, List.append_assoc, List.singleton_append, List.cons_append,
          List.nil_append] using shape

end LeanCage.Host.Image
