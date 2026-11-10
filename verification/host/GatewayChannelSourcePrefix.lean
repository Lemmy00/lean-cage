import GatewayChannelSourceJournal

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
  {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

-- §FS-host-boundary.caller: Per-operation source data now supplies the
-- previously free reader/discard conditions. The result is the actual writer
-- prefix consumed by canonical typed framing, with pending ACK/loss intact.
theorem actual_response_prefix_from_operations {ipc : ObjectId → Prop}
    (sockets : SocketPairContract native ipc) (descriptions : NativeDescriptionContract native)
    (raw : RawReferenceLifetimeContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (descriptors : DescriptorContract kernel) (directories : DirectoryRetirementContract kernel)
    (introductions : DescriptionIntroductionContract kernel) (retirement : DescriptorRetirementContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (namespaceLaws : NativeNamespaceContract native) (environment : InterferenceContract kernel)
    {initialWorld : World} {population : Population}
    (source : ActorJournal runtime (Population.empty initialWorld) ticks population)
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (channels : EngineChannelRows journal)
    (birth : PairBirthEntry process child native hostUid before after callers next ticks pair)
    (actualBirth : ActualPairBirth journal birth)
    (referenceRuntime : SocketReferenceRuntime process child native hostUid)
    {first last : SocketReferenceSnapshot} (recording : SocketReferenceRecording referenceRuntime journal first last)
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {additional : Nat → SocketLifetime → Prop}
    (effects : SocketResidualRuntime journal primitive referenceRuntime recording birth.callerSocket additional)
    (nativeSources : NativeSocketRowSources journal birth.callerSocket)
    (otherSources : ∀ position, ¬ additional position birth.callerSocket)
    (nativeDescriptors : NativeReferenceContract native)
    (received : NativeReadEntry process child native hostUid before after callers next ticks pair)
    (actualReceive : ActualNativeRead journal received) (terminal : received.position + 1 = ticks.length)
    (receiver : received.receiver = .caller) (description : received.handle.description = birth.firstHandle.description)
    {final : PhysicalState} {records : List Record}
    (physical : SourceChannelJournal journal primitive 0 ticks .unborn records final)
    (actor : ActorId) (handle : Handle) (writers : ChannelWriteSources primitive actor handle.description)
    (tick : ActorTick runtime) (engine : EngineState)
    (history : SelectedActorHistory runtime initialWorld ticks tick actor engine)
    (inherited : history.launch.references 1 = some handle) (endpoint : handle.object = pair.engine)
    (nonempty : (List.range' 0 ticks.length).flatMap (nativeCallerBytesAt (pair := pair) journal) ≠ []) :
    ∃ entry token, primitive.enteredEngine token entry ∧ entry.actor = actor ∧
      ∃ response : EngineResponse entry, ∃ pending,
        response.source.context.bytes.data.toList =
          (List.range' 0 ticks.length).flatMap (nativeCallerBytesAt (pair := pair) journal) ++ pending := by
  let channel := SourceChannelJournal.channel sockets descriptions raw sdk descriptors lifetimes references namespaceLaws
    source journal channels birth actualBirth referenceRuntime recording effects nativeSources otherSources physical
  have retained := SourceChannelJournal.preserves_received sockets descriptions raw sdk descriptors lifetimes references namespaceLaws
    source journal channels birth actualBirth referenceRuntime recording effects nativeSources otherSources
    nativeDescriptors received actualReceive terminal receiver description physical
  have actualBytes : (records.flatMap Record.actions).flatMap (PrivateStreams.received .caller) ≠ [] := by
    rw [channel.caller_bytes]
    exact nonempty
  exact response_prefix_of_source_rows descriptors directories introductions retirement sdk lifetimes references environment
    source journal channel actor handle writers tick engine history inherited endpoint retained actualBytes

end LeanCage.Host.PrivateStreams
