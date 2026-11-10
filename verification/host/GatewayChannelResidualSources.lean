import GatewayChannelOFDResidual
import GatewayChannelSocketSurvival

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
  {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

-- These receipts retain concrete opcodes or exact resolved operands for
-- each stored native call. External authority is applied only to its own
-- permitted call, never inferred from UID equality or a callback label.
def NativeSocketRowSources
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (socket : SocketLifetime) : Prop :=
  ∀ position (point : SelectedNativeCut process child native hostUid before after callers next ticks position),
    selectNativeCut journal position = some point → ∀ call, embeddedNative point.cut.current = some call →
    Nonempty (NativeResidualSource call socket × NativeShutdownSource call socket)

private theorem socket_read_origin_excluded {position : Nat} {first last : Processes}
    {current following : NativeProcesses} {tick : ActorTick runtime}
    {row : NativeExternalStep process child native hostUid first current tick last following}
    {socket : SocketLifetime} {additional : Prop}
    (actual : SocketResidualReadOrigin (ticks := ticks) (pair := pair) position row socket additional)
    (nativeSource : ∀ call, embeddedNative row = some call → Nonempty (NativeResidualSource call socket))
    (engineSource : ∀ entry : EngineReadEntry ticks pair, ¬ socket.matches entry.handle)
    (otherSource : ¬ additional) : False := by
  cases actual with
  | native call stored read description =>
    obtain ⟨source⟩ := nativeSource call stored
    exact native_residual_source_excludes source read description
  | engine entry began identity => exact engineSource entry identity
  | additional observed => exact otherSource observed

section ActualSources
variable {ipc : ObjectId → Prop}
  (sockets : SocketPairContract native ipc) (descriptions : NativeDescriptionContract native)
  (raw : RawReferenceLifetimeContract kernel) (sdk : RuntimeDescriptorContract runtime)
  (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
  (references : ReferenceContract runtime) (namespaceLaws : NativeNamespaceContract native)
  {initial : World} {final : Population} (source : ActorJournal runtime (Population.empty initial) ticks final)
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

include sockets descriptions raw sdk descriptors lifetimes references namespaceLaws source channels actualBirth effects nativeSources

-- §FS-host-boundary.caller: Raw engine read exclusion is DERIVED here from
-- the source-built handoffs and actual fresh OFD history. Only the separately
-- enumerated SDK/child/foreign read-source producer remains as an input.
theorem actual_residual_step_no_caller_read
    {position : Nat} (point : SelectedNativeCut process child native hostUid before after callers next ticks position)
    (selected : selectNativeCut journal position = some point) (current following : SocketReferenceSnapshot)
    (sampled : SocketReferenceRecording.at referenceRuntime recording position = some (current, following))
    (otherSource : ¬ additional position birth.callerSocket)
    {input output : PhysicalState} {record : Record} (step : ObservedStep primitive input record output)
    (residual : ResidualStep step) (atPosition : record.position = position) :
    ∀ bytes, Action.read .caller bytes ∉ record.actions := by
  cases step with
  | engine | native | observation => simp
  | commit | birth => simp
  | read => exact False.elim residual
  | other actualPosition inside state action final actual =>
    have atRow : actualPosition = position := atPosition
    subst actualPosition
    intro bytes member
    have identity : action = .read .caller bytes := (List.mem_singleton.mp member).symm
    subst action
    obtain ⟨held, ⟨cause⟩⟩ := effects.read position point selected current following sampled bytes _ final actual
    apply socket_read_origin_excluded cause
    · intro call stored
      obtain ⟨read, shutdown⟩ := nativeSources position point selected call stored
      exact ⟨read⟩
    · intro entry
      exact actual_engine_read_not_original_socket sockets descriptions raw sdk descriptors lifetimes references
        namespaceLaws source journal channels birth actualBirth entry
    · exact otherSource

-- §FS-host-boundary.ownership: All nonempty-discard branches are accounted
-- by the SAME actual operation: classified reads, read shutdown, or the last
-- original OFD reference. The final branch is refuted by an actual receive.
theorem actual_residual_step_preserves_received
    (nativeDescriptors : NativeReferenceContract native)
    (received : NativeReadEntry process child native hostUid before after callers next ticks pair)
    (actualReceive : ActualNativeRead journal received) (terminal : received.position + 1 = ticks.length)
    (receiver : received.receiver = .caller) (description : received.handle.description = birth.firstHandle.description)
    {position : Nat} (point : SelectedNativeCut process child native hostUid before after callers next ticks position)
    (selected : selectNativeCut journal position = some point) (current following : SocketReferenceSnapshot)
    (sampled : SocketReferenceRecording.at referenceRuntime recording position = some (current, following))
    (otherSource : ¬ additional position birth.callerSocket)
    {input output : PhysicalState} {record : Record} (step : ObservedStep primitive input record output)
    (atPosition : record.position = position) : ∀ action ∈ record.actions, preservesReceivedBytes .caller action := by
  cases step with
  | engine | native | observation => simp
  | commit | birth | read => simp [preservesReceivedBytes]
  | other actualPosition inside state action final actual =>
    have atRow : actualPosition = position := atPosition
    subst actualPosition
    intro chosen member
    cases List.mem_singleton.mp member
    cases action with
    | discard side bytes =>
      cases side with
      | engine => exact .inl (by intro impossible; cases impossible)
      | caller =>
        obtain ⟨held, ⟨cause⟩⟩ := effects.discard position point selected current following sampled bytes _ final actual
        have allocated := SocketReferenceRecording.selected_input_lifetime referenceRuntime recording point selected
          current following sampled birth.callerSocket held
        have order := actual_old_ofd_after_birth sockets references source birth point allocated
        have live := actual_receive_excludes_postbirth_last_drop referenceRuntime references descriptions nativeDescriptors
          recording birth actualBirth received actualReceive terminal receiver description position (Nat.le_of_lt order)
          current following sampled
        exact False.elim (by
          cases cause with
          | read read =>
            apply socket_read_origin_excluded read
            · intro call stored
              obtain ⟨source, shutdown⟩ := nativeSources position point selected call stored
              exact ⟨source⟩
            · intro entry
              exact actual_engine_read_not_original_socket sockets descriptions raw sdk descriptors lifetimes references
                namespaceLaws source journal channels birth actualBirth entry
            · exact otherSource
          | shutdown call stored shutdown =>
            obtain ⟨read, source⟩ := nativeSources position point selected call stored
            exact socket_shutdown_excluded source shutdown
          | lastReference released => exact live released)
    | born | write | read | closeWrite | eof | quiet => trivial

end ActualSources
end LeanCage.Host.PrivateStreams
