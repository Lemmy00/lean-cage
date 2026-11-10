import EntrypointPendingWriter
import FilesystemWriteSources

namespace LeanCage.Host.EntrypointWriterPrefix
open Filesystem Kernel

-- §FS-host-boundary.caller: Dispatch writes retain their real allocated validator/image,
-- VM controller or publisher source. The final response retains its exact packet producer.
inductive Origin (before : List Program.Event) (request : Request) (observed : Option Reply) : Type 1 where
  | application (source : WriteSources.Call before (Program.filesystemPrefixEvent (request, observed)))
  | response (source : ResponseFrontier before request observed)

theorem Cut.origin {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : Cut before request observed) (writing : request.op = .write) :
    Nonempty (Origin before request observed) := by
  cases source with
  | application context input packet inside active trace =>
    obtain ⟨phase⟩ := WriteSources.command_call input active writing
    exact ⟨.application (phase.outer context.events trace)⟩
  | response frontier => exact ⟨.response frontier⟩

-- §FS-host-boundary.acceptance: Pending/partial kernel progress has no future ACK or return.
theorem PendingCut.origin_source {engine : EngineState} {request : Request}
    (source : PendingCut engine request) (writing : request.op = .write) :
    Nonempty (Origin source.occurrence.logicalBefore request none) := source.origin.origin writing

theorem PrimitiveCut.origin_source {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed}
    (source : PrimitiveCut adapter) (writing : request.op = .write) :
    Nonempty (Origin adapter.occurrence.logicalBefore request none) := source.origin.origin writing

end LeanCage.Host.EntrypointWriterPrefix
