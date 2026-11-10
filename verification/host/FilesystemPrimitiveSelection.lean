import FilesystemRecording

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.acceptance: The source event identifies that same actual raw primitive call.
theorem selected_filesystem_step {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (tick : ActorTick runtime) {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) :
    kernel.step (tick.before.project engine) request observed tick.after.shared := by
  rcases tick with ⟨kind, before, after, operation⟩
  cases operation with
  | launch => cases action
  | @returned β population owner current effect next reply world ownerPresent alive head actual =>
    dsimp only [ActorAction.eventFor] at action
    split at action
    · rename_i same
      subst owner
      have engines := Option.some.inj (present.symm.trans ownerPresent)
      subst engine
      cases observed <;> cases action
      exact actual
    · cases action
  | @lost β population owner current effect next world ownerPresent alive head actual =>
    dsimp only [ActorAction.eventFor] at action
    split at action
    · rename_i same
      subst owner
      have engines := Option.some.inj (present.symm.trans ownerPresent)
      subst engine
      cases observed <;> cases action
      exact actual
    · cases action
  | foreign | retire | nativeRetire => cases action

end LeanCage.Host.Kernel
