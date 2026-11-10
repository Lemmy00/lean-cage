import FilesystemActors

namespace LeanCage.Host.Kernel

variable {sourceProgram : Program UInt32}

-- §AR-host-boundary.primitives: These are one actual kernel teardown point's remaining
-- resource projections. A blocked/lost application call never supplies this observation.
structure RetirementContract {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) : Prop where
  engine_entries : ∀ actor observation directory before after,
    runtime.retire actor observation directory before after → after.entries = before.entries
  native_entries : ∀ actor observation beforeResources afterResources before after,
    runtime.nativeRetire actor observation beforeResources afterResources before after → after.entries = before.entries
  engine_subset : ∀ actor observation directory before after fd handle,
    runtime.retire actor observation directory before after → after.handles fd = some handle →
    before.handles fd = some handle
  engine_directory : ∀ actor observation directory before after,
    runtime.retire actor observation directory before after →
    after.workingDirectory = before.workingDirectory ∧
      (∀ object, observation.directory = some object → directory = some object ∧ object = before.workingDirectory)
  engine_complete : ∀ actor observation directory before after,
    runtime.retire actor observation directory before after → observation.finished = true →
    after.handles = (fun _ => none) ∧ observation.directory = none
  native_subset : ∀ actor observation beforeResources afterResources before after fd handle,
    runtime.nativeRetire actor observation beforeResources afterResources before after →
    afterResources.handles fd = some handle → beforeResources.handles fd = some handle
  native_directory : ∀ actor observation beforeResources afterResources before after,
    runtime.nativeRetire actor observation beforeResources afterResources before after →
    afterResources.directory = observation.directory ∧ afterResources.lastDirectory = beforeResources.lastDirectory ∧
      (∀ object, afterResources.directory = some object → beforeResources.directory = some object)
  native_complete : ∀ actor observation beforeResources afterResources before after,
    runtime.nativeRetire actor observation beforeResources afterResources before after → observation.finished = true →
    afterResources.handles = (fun _ => none) ∧ afterResources.directory = none

-- §FS-host-boundary.ownership: An actual retirement stops the source immediately, including
-- a partial teardown; remaining resources and their later release remain explicit.
theorem retired_source_not_running (engine : EngineState) (observation : EngineRetirement) (world : World) :
    (engine.retired observation world).running = false := rfl

end LeanCage.Host.Kernel
