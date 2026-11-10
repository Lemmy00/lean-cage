import GatewayResponseWriterPrefix
import GatewayChannelReadJournal
import GatewayChannelDiscards

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

-- §AR-host-boundary.interfaces.gateway: This is the exact byte interface for
-- typed framing. Write placement, read-row coverage and nonempty-discard
-- exclusions remain source-producer obligations, not platform safe-queue laws.
theorem response_prefix_of_source_rows
    (descriptors : DescriptorContract kernel) (directories : DirectoryRetirementContract kernel)
    (introductions : DescriptionIntroductionContract kernel) (retirement : DescriptorRetirementContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initialWorld : World} {population : Population}
    (source : ActorJournal runtime (Population.empty initialWorld) ticks population)
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {final : PhysicalState} {records : List Record}
    (physical : ChannelJournal journal primitive 0 ticks .unborn records final)
    (actor : ActorId) (handle : Handle) (sources : ChannelWriteSources primitive actor handle.description)
    (tick : ActorTick runtime) (engine : EngineState)
    (history : SelectedActorHistory runtime initialWorld ticks tick actor engine)
    (inherited : history.launch.references 1 = some handle) (endpoint : handle.object = pair.engine)
    (retained : ∀ action ∈ records.flatMap Record.actions, preservesReceivedBytes .caller action)
    (nonempty : (records.flatMap Record.actions).flatMap (received .caller) ≠ []) :
    ∃ entry token, primitive.enteredEngine token entry ∧ entry.actor = actor ∧
      ∃ response : EngineResponse entry, ∃ pending,
        response.source.context.bytes.data.toList =
          (List.range' 0 ticks.length).flatMap (nativeCallerBytesAt (pair := pair) journal) ++ pending := by
  have balance := physical_received_prefix_allow_empty physical.erase.erase.stream .caller retained
  simp only [PhysicalState.unborn, incomingOrEmpty, List.nil_append] at balance
  have writtenNonempty : (records.flatMap Record.actions).flatMap (written .caller) ≠ [] := by
    intro empty
    rw [empty] at balance
    have noRead := (List.append_eq_nil_iff.mp balance.symm).1
    exact nonempty noRead
  obtain ⟨entry, token, entered, actor, response, current, stored, bounded, writtenPrefix⟩ :=
    actual_response_written_prefix descriptors directories introductions retirement sdk lifetimes references environment
      source physical.erase actor handle sources tick engine history inherited endpoint writtenNonempty
  let bytes := response.source.context.bytes
  let extent := response.source.writer.offset + current.committed
  have split : (bytes.extract 0 extent).data.toList ++ (bytes.extract extent bytes.size).data.toList = bytes.data.toList := by
    rw [← ByteArray.toList_data_append, ByteArray.extract_append_extract,
      Nat.min_eq_left (by omega), Nat.max_eq_right bounded, ByteArray.extract_zero_size]
  refine ⟨entry, token, entered, actor, response,
    incomingOrEmpty final.stream .caller ++ (bytes.extract extent bytes.size).data.toList, ?_⟩
  rw [← split, ← writtenPrefix, balance, List.append_assoc, physical.caller_bytes]
  rfl

end LeanCage.Host.PrivateStreams
