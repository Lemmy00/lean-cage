import PrefixOrigins
import RunDirectoryProofs

namespace LeanCage.Host.ValidatorPrefixCuts
open Filesystem

structure Allocated where
  directory : RunDirectory.Owned
  allocating : List (Request × Reply)
  allocate : Returns RunDirectory.create allocating (.ok directory)

def Allocated.events (context : Allocated) := context.allocating.map Program.filesystemEvent
def Allocated.writeProgram (context : Allocated) (raw : ByteArray) :=
  writeNew context.directory.directory.fd "policy.json".toUTF8 raw
def Allocated.spawnProgram (context : Allocated) (bundle : Validation.Bundle) :=
  Program.effect (.spawn (Validation.validatorArguments bundle (context.directory.path ++ "/policy.json")))

structure Written (raw : ByteArray) where
  allocated : Allocated
  writing : List (Request × Reply)
  write : Returns (allocated.writeProgram raw) writing (.ok ())

def Written.events {raw} (context : Written raw) :=
  context.allocated.events ++ context.writing.map Program.filesystemEvent

structure Spawned (bundle : Validation.Bundle) (raw : ByteArray) where
  written : Written raw
  child : Except String Validation.ValidatorChild
  spawning : List Program.Event
  spawn : Program.Returns (written.allocated.spawnProgram bundle) spawning child

def Spawned.events {bundle raw} (context : Spawned bundle raw) :=
  context.written.events ++ context.spawning

structure Observed (bundle : Validation.Bundle) (raw : ByteArray) where
  spawned : Spawned bundle raw
  result : Validation.ChildObservation
  observing : List Program.Event
  observe : Program.Returns (Validation.observeChild raw spawned.child) observing result

def Observed.events {bundle raw} (context : Observed bundle raw) :=
  context.spawned.events ++ context.observing

-- §FS-host-boundary.ownership: Validator mutations retain their actual fresh-directory producer.
inductive Cut (bundle : Validation.Bundle) (raw : ByteArray)
    (before : List Program.Event) (event : Program.Event) : Type 1 where
  | allocating (active : Program.Prefix (Program.liftFilesystem RunDirectory.create) (before ++ [event]))
  | writing (context : Allocated) (inside : List Program.Event)
      (active : Program.Prefix (Program.liftFilesystem (context.writeProgram raw)) (inside ++ [event]))
      (trace : before = context.events ++ inside)
  | spawning (context : Written raw) (inside : List Program.Event)
      (active : Program.Prefix (context.allocated.spawnProgram bundle) (inside ++ [event]))
      (trace : before = context.events ++ inside)
  | observing (context : Spawned bundle raw) (inside : List Program.Event)
      (active : Program.Prefix (Validation.observeChild raw context.child) (inside ++ [event]))
      (trace : before = context.events ++ inside)
  | cleaningFailedWrite (context : Allocated) (writing : List (Request × Reply)) (error : Failure)
      (written : Returns (context.writeProgram raw) writing (.error error))
      (inside : List Program.Event)
      (active : Program.Prefix (Program.liftFilesystem (RunDirectory.cleanup context.directory))
        (inside ++ [event]))
      (trace : before = context.events ++ writing.map Program.filesystemEvent ++ inside)
  | cleaningObserved (context : Observed bundle raw) (inside : List Program.Event)
      (reaped : context.result.reaped = true)
      (active : Program.Prefix (Program.liftFilesystem
        (RunDirectory.cleanup context.spawned.written.allocated.directory)) (inside ++ [event]))
      (trace : before = context.events ++ inside)
  | releasingUnknown (context : Observed bundle raw) (inside : List Program.Event)
      (unknown : context.result.reaped = false)
      (active : Program.Prefix (Program.liftFilesystem
        (Validation.releaseDirectory context.spawned.written.allocated.directory)) (inside ++ [event]))
      (trace : before = context.events ++ inside)

-- §FS-host-boundary.acceptance: Actual validator prefixes include failed writes and lost effects.
theorem validate_copied_cut (bundle : Validation.Bundle) (raw : ByteArray)
    {before : List Program.Event} {event : Program.Event}
    (active : Program.Prefix (Validation.validateCopied bundle raw) (before ++ [event])) :
    Nonempty (Cut bundle raw before event) := by
  unfold Validation.validateCopied at active
  rcases Program.last_bind_split _ _ active with allocating |
      ⟨allocating, temporary, afterAllocate, allocate, rest, allocateShape⟩
  · exact ⟨.allocating allocating⟩
  · cases temporary with
    | error error => exact False.elim (Program.pure_has_no_last _ _ _ rest)
    | ok directory =>
      obtain ⟨allocateSource, allocateRun, allocateEvents⟩ := Program.lift_filesystem_source _ allocate
      let allocated : Allocated := ⟨directory, allocateSource, allocateRun⟩
      have allocatedShape : before = allocated.events ++ afterAllocate := by
        simpa only [Allocated.events, allocated, allocateEvents] using allocateShape
      rcases Program.last_bind_split _ _ rest with writing |
          ⟨writing, written, afterWrite, write, rest, writeShape⟩
      · exact ⟨.writing allocated afterAllocate writing allocatedShape⟩
      · obtain ⟨writeSource, writeRun, writeEvents⟩ := Program.lift_filesystem_source _ write
        cases written with
        | error error =>
          rcases Program.last_bind_split _ _ rest with cleaning |
              ⟨cleaning, result, afterClean, cleanup, last, cleanShape⟩
          · exact ⟨.cleaningFailedWrite allocated writeSource error writeRun afterWrite cleaning (by
              simp only [allocatedShape, writeShape, writeEvents, List.append_assoc])⟩
          · exact False.elim (Program.pure_has_no_last _ _ _ last)
        | ok writtenUnit =>
          cases writtenUnit
          let written : Written raw := ⟨allocated, writeSource, writeRun⟩
          have writtenShape : before = written.events ++ afterWrite := by
            simp only [Written.events, written, allocatedShape, writeShape, writeEvents, List.append_assoc]
          rcases Program.last_bind_split _ _ rest with spawning |
              ⟨spawning, child, afterSpawn, spawn, rest, spawnShape⟩
          · exact ⟨.spawning written afterWrite spawning writtenShape⟩
          · let spawned : Spawned bundle raw := ⟨written, child, spawning, spawn⟩
            have spawnedShape : before = spawned.events ++ afterSpawn := by
              simp only [Spawned.events, spawned, writtenShape, spawnShape, List.append_assoc]
            rcases Program.last_bind_split _ _ rest with observing |
                ⟨observing, result, afterObserve, observe, rest, observeShape⟩
            · exact ⟨.observing spawned afterSpawn observing spawnedShape⟩
            · let observed : Observed bundle raw := ⟨spawned, result, observing, observe⟩
              have observedShape : before = observed.events ++ afterObserve := by
                simp only [Observed.events, observed, spawnedShape, observeShape, List.append_assoc]
              unfold Validation.finishValidation at rest
              cases reaped : result.reaped with
              | true =>
                simp only [reaped, ↓reduceIte] at rest
                rcases Program.last_bind_split _ _ rest with cleaning |
                    ⟨cleaning, cleaned, afterClean, cleanup, last, cleanShape⟩
                · exact ⟨.cleaningObserved observed afterObserve reaped cleaning observedShape⟩
                · exact False.elim (Program.pure_has_no_last _ _ _ last)
              | false =>
                simp only [reaped, Bool.false_eq_true, ↓reduceIte] at rest
                rcases Program.last_bind_split _ _ rest with releasing |
                    ⟨releasing, released, afterRelease, release, last, releaseShape⟩
                · exact ⟨.releasingUnknown observed afterObserve reaped releasing observedShape⟩
                · exact False.elim (Program.pure_has_no_last _ _ _ last)

end LeanCage.Host.ValidatorPrefixCuts
