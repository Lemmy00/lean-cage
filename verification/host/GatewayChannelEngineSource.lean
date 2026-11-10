import GatewayChannelEngineFamily
import GatewayChannelPendingBirth

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)}

-- §AR-host-boundary.interfaces.gateway: The real C pair-use receipts and
-- exec equations feed the same handoff. No initial table absence or trusted
-- reader/owner label is accepted by this source-data consumer.
theorem engine_channels_from_source_pairs {ipc : ObjectId → Prop} (sockets : SocketPairContract native ipc)
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {tick : ActorTick runtime} {current : NativeProcesses} (handoff : NativeHandoffAt tick current)
    (dataUse controlUse : ChannelCode.PairUse) (dataSource : dataUse.Consistent) (controlSource : controlUse.Consistent)
    (dataPoint : SelectedNativeCut process child native hostUid before after callers next ticks dataUse.position)
    (dataSelected : selectNativeCut journal dataUse.position = some dataPoint)
    (dataCall : NativeCallAt native dataPoint.tick dataPoint.cut.priorNative dataPoint.cut.nextNative)
    (dataStored : embeddedNative dataPoint.cut.current = some dataCall)
    (dataInterpreted : NativeCode.Interprets dataUse.row dataCall)
    (controlPoint : SelectedNativeCut process child native hostUid before after callers next ticks controlUse.position)
    (controlSelected : selectNativeCut journal controlUse.position = some controlPoint)
    (controlCall : NativeCallAt native controlPoint.tick controlPoint.cut.priorNative controlPoint.cut.nextNative)
    (controlStored : embeddedNative controlPoint.cut.current = some controlCall)
    (controlInterpreted : NativeCode.Interprets controlUse.row controlCall)
    (evidence : NativeChannels.Evidence (NativeCode.encodeReferences handoff.execution.references)
      dataUse.rightObject controlUse.rightObject) : Nonempty (EngineSourceChannels journal handoff) := by
  obtain ⟨data, dataBirth, actualData, dataPosition, dataProcess, dataLeft, dataRight,
    dataLeftDescription, dataRightDescription, dataLeftIpc, dataRightIpc⟩ :=
    actual_pending_source_pair_birth sockets journal dataUse dataSource dataPoint dataSelected dataCall dataStored dataInterpreted
  obtain ⟨control, controlBirth, actualControl, controlPosition, controlProcess, controlLeft, controlRight,
    controlLeftDescription, controlRightDescription, controlLeftIpc, controlRightIpc⟩ :=
    actual_pending_source_pair_birth sockets journal controlUse controlSource controlPoint controlSelected controlCall controlStored controlInterpreted
  exact ⟨{
    data
    control
    dataBirth
    controlBirth
    actualData
    actualControl
    evidence := by simpa only [dataRight, controlRight] using evidence }⟩

end LeanCage.Host.PrivateStreams
