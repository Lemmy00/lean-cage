import GatewayEntrypointReadSources
import FilesystemOutputSources
import GatewayStreamSources

namespace LeanCage.Host.PrivateStreams
open Filesystem Kernel

-- §AR-host-boundary.primitives: A pending read captures its real source
-- lifetime/ordinal and input OFD. Kernel progress can use this receipt after
-- the source loses its reply; no later running table or ACK is required.
structure EngineReadEntry {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (ticks : List (ActorTick runtime)) (pair : Pair) where
  position : Nat
  tick : ActorTick runtime
  selected : ticks[position]? = some tick
  actor : ActorId
  engine : EngineState
  present : tick.before.actors actor = some engine
  running : engine.running = true
  request : Request
  next : Reply → Program UInt32
  head : engine.current = .call (.filesystem request) next
  reading : request.op = .read
  stream : request.third = 0
  receiver : Side
  handle : Handle
  input : engine.references request.first = some handle
  endpoint : handle.object = pair.endpoint receiver

def EngineReadEntry.key {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {ticks : List (ActorTick runtime)} {pair : Pair} (entry : EngineReadEntry ticks pair) : CallKey :=
  .engine entry.actor entry.engine.events.length

inductive EngineReadSource {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {ticks : List (ActorTick runtime)} {pair : Pair} (entry : EngineReadEntry ticks pair) : Type 1 where
  | packet (source : EntrypointReadSources.PendingCut entry.engine entry.request)
      (ready : EntrypointPrefixCuts.Ready) (inside : List Program.Event)
      (active : Program.Prefix (Program.liftFilesystem (Packet.read 0))
        (inside ++ [Program.filesystemPrefixEvent (entry.request, none)]))
      (trace : source.occurrence.logicalBefore = ready.events ++ inside)
      (descriptor : entry.request.first = 0) : EngineReadSource entry
  | machine (source : EntrypointReadSources.PendingCut entry.engine entry.request)
      (actual : EntrypointReadSources.MachineCut source.occurrence.logicalBefore entry.request none) :
      EngineReadSource entry

-- The real source removes the positional branch before any physical read
-- observation. Packet and VM slices retain their exact original occurrences.
theorem engine_read_source {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)} {pair : Pair}
    (journal : ActorJournal runtime (Population.empty initial) ticks final) (entry : EngineReadEntry ticks pair) :
    Nonempty (EngineReadSource entry) := by
  obtain ⟨source⟩ := EntrypointReadSources.pending_read_at journal entry.selected entry.present entry.running entry.head entry.reading
  cases source.origin with
  | positioned offset => exact False.elim (offset entry.stream)
  | packet ready inside active trace descriptor stream => exact ⟨.packet source ready inside active trace descriptor⟩
  | machine actual stream => exact ⟨.machine source actual⟩

-- §FS-host-boundary.caller: A packet's current input handle is DERIVED from
-- its actual inherited fd0. An arbitrary caller-selected descriptor or a
-- later reused number cannot replace that same launch observation.
theorem packet_read_inherited_handle {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (directories : DirectoryRetirementContract kernel)
    (sdk : RuntimeDescriptorContract runtime)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)} {pair : Pair}
    (journal : ActorJournal runtime (Population.empty initial) ticks final) (entry : EngineReadEntry ticks pair)
    (history : SelectedActorHistory runtime initial ticks entry.tick entry.actor entry.engine)
    (handle : Handle) (inherited : history.launch.references 0 = some handle)
    (packet : entry.request.first = 0) : entry.handle = handle := by
  have live := actual_live_inherited_reference descriptors directories sdk journal history entry.present entry.running inherited
  have selected := entry.input
  rw [packet] at selected
  exact Option.some.inj (selected.symm.trans live)

-- The full exec/source producer supplies the inherited object observation;
-- this theorem supplies its current read connection, without a reader label.
theorem actual_packet_read_not_caller {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (directories : DirectoryRetirementContract kernel)
    (sdk : RuntimeDescriptorContract runtime)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)} {pair : Pair}
    (journal : ActorJournal runtime (Population.empty initial) ticks final) (entry : EngineReadEntry ticks pair)
    (history : SelectedActorHistory runtime initial ticks entry.tick entry.actor entry.engine)
    (handle : Handle) (inherited : history.launch.references 0 = some handle)
    (different : handle.object ≠ pair.caller) (packet : entry.request.first = 0) : entry.receiver ≠ .caller := by
  have actual := packet_read_inherited_handle descriptors directories sdk journal entry history handle inherited packet
  intro receiver
  apply different
  rw [← actual, entry.endpoint, receiver]
  rfl

end LeanCage.Host.PrivateStreams
