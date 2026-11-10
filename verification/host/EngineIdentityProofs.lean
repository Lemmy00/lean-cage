import LeanCageHost.Validation
import SnapshotProofs.Copy

namespace LeanCage.Host.Validation
open Filesystem

structure EngineIdentity (bundle : Bundle) (events : List (Request × Reply)) where
  files : List (String × Json.Value)
  name : String
  expected : String
  fd : UInt64
  opened : Reply
  copied : CopiedFile
  digest : ByteArray
  copying : List (Request × Reply)
  closing : List (Request × Reply)
  hashing : List (Request × Reply)
  inventory : bundleFiles bundle.manifest = some files
  identified : files.find? (fun field => field.1 == "bin/leancage-host") = some (name, .string expected)
  descriptor : Filesystem.descriptor opened = some fd
  copy : Returns (copyOpened fd workspaceMax) copying (.ok copied)
  close : Returns (closeResult fd (.ok copied)) closing (.ok copied)
  hash : Returns (Filesystem.hash copied.bytes) hashing (.ok digest)
  identity : Snapshot.hex digest = expected
  trace : events = ({op := .selfExecutable}, opened) :: (copying ++ closing ++ hashing)

-- §FS-host-boundary.caller: Actual self-executable bytes, not an unused manifest path, are bound.
theorem check_engine_source (bundle : Bundle) {events : List (Request × Reply)}
    (run : Returns (checkEngineIdentity bundle) events (.ok ())) : Nonempty (EngineIdentity bundle events) := by
  unfold checkEngineIdentity at run
  split at run
  · rename_i files inventory
    split at run
    · rename_i name expected identified
      obtain ⟨opened, later, rfl, afterOpen⟩ := Snapshot.returns_call_split run
      dsimp only [Filesystem.Program.bind] at afterOpen
      split at afterOpen
      · rename_i fd descriptor
        obtain ⟨copying, result, last, copiedRun, afterCopy, copyShape⟩ :=
          Snapshot.returns_bind_split _ _ afterOpen
        obtain ⟨reading, original, closing, readRun, closeRun, readShape⟩ :=
          Snapshot.returns_bind_split _ _ copiedRun
        cases result with
        | error error => cases afterCopy
        | ok copied =>
          have same := (Snapshot.closeResult_provenance _ _ closeRun).1
          cases same
          obtain ⟨hashing, result, ending, hashed, final, hashShape⟩ :=
            Snapshot.returns_bind_split _ _ afterCopy
          cases result with
          | error error => cases final
          | ok digest =>
            dsimp only at final
            split at final
            · rename_i identity
              obtain ⟨rfl, _⟩ := Snapshot.returns_pure_eq final
              refine ⟨⟨files, name, expected, fd, opened, copied, digest, reading, closing, hashing,
                inventory, identified, descriptor, readRun, closeRun, hashed,
                by simpa using identity, ?_⟩⟩
              simp only [copyShape, readShape, hashShape, List.append_nil, List.append_assoc]
            · cases final
      · cases afterOpen
    · cases run
  · cases run

end LeanCage.Host.Validation
