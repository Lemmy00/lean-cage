import GatewayChannelReferenceHistory
import GatewayChannelDescriptorEffects

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
  {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)} {pair : Pair}

-- §FS-host-boundary.caller: The lifetime anchor is one actual selected
-- receive of the original socket, not a promised future response or reply.
-- Its raw input/output tables are the same stored call's tables.
theorem actual_recorded_receive_lifetime
    (references : SocketReferenceRuntime process child native hostUid)
    (descriptors : NativeReferenceContract native)
    {journal : NativeExternalJournal process child native hostUid before callers ticks after next}
    {first last : SocketReferenceSnapshot} (recording : SocketReferenceRecording references journal first last)
    (entry : NativeReadEntry process child native hostUid before after callers next ticks pair)
    (actual : ActualNativeRead journal entry) (socket : SocketLifetime) (identity : socket.matches entry.handle) :
    ∃ current following,
      SocketReferenceRecording.at references recording entry.position = some (current, following) ∧
      current.held socket ∧ following.held socket := by
  let point : SelectedNativeCut process child native hostUid before after callers next ticks entry.position := ⟨entry.tick, entry.cut⟩
  obtain ⟨current, following, preceding, suffix, sampled, operation, suffixAt⟩ :=
    SocketReferenceRecording.selected_cut references recording point actual
  have inputNative := (references.input operation).2.1
  have outputNative := (references.output operation).2.1
  have held := actual_call_retains_descriptor descriptors entry.call entry.descriptor entry.handle entry.input (by
    change ¬ NativeReferenceReplacement entry.call.operation entry.call.product entry.descriptor
    rw [entry.operation]
    exact receive_retains_descriptor entry.descriptor entry.extent entry.flags entry.descriptor entry.call.product)
  refine ⟨current, following, sampled, ?_, ?_⟩
  · refine ⟨.native entry.call.token entry.descriptor, entry.handle, ?_, identity⟩
    simp only [SocketReferenceSnapshot.at, inputNative, point, entry.call.inputTable, Option.bind_some, entry.input]
  · refine ⟨.native entry.call.token entry.descriptor, entry.handle, ?_, identity⟩
    simp only [SocketReferenceSnapshot.at, outputNative, point, entry.call.outputTable, Option.bind_some, held]

-- The actual finite prefix may end at that kernel receive while its SDK
-- call is still pending. Destruction or a lost observation after it is not
-- substituted for the real lifetime observation.
theorem actual_receive_prefix_no_last_drop
    (references : SocketReferenceRuntime process child native hostUid)
    (lifetimes : ReferenceContract runtime)
    {journal : NativeExternalJournal process child native hostUid before callers ticks after next}
    {first last : SocketReferenceSnapshot} (recording : SocketReferenceRecording references journal first last)
    (socket : SocketLifetime) (old : first.population.shared.descriptionAllocated socket.description = true)
    (held : last.held socket)
    {position : Nat} (point : SelectedNativeCut process child native hostUid before after callers next ticks position)
    (selected : selectNativeCut journal position = some point)
    (current following : SocketReferenceSnapshot)
    (sampled : SocketReferenceRecording.at references recording position = some (current, following)) :
    ¬ following.released socket := by
  obtain ⟨before, after, actual, beforeHeld, afterHeld⟩ :=
    SocketReferenceRecording.selected_held references lifetimes recording socket old held point selected
  have same := Prod.mk.inj (Option.some.inj (actual.symm.trans sampled))
  have retained : following.held socket := same.2 ▸ afterHeld
  exact following.held_not_released socket retained

theorem actual_terminal_receive_holds_socket
    (references : SocketReferenceRuntime process child native hostUid)
    (descriptors : NativeReferenceContract native)
    {journal : NativeExternalJournal process child native hostUid before callers ticks after next}
    {first last : SocketReferenceSnapshot} (recording : SocketReferenceRecording references journal first last)
    (entry : NativeReadEntry process child native hostUid before after callers next ticks pair)
    (actual : ActualNativeRead journal entry) (terminal : entry.position + 1 = ticks.length)
    (socket : SocketLifetime) (identity : socket.matches entry.handle) : last.held socket := by
  obtain ⟨current, following, sampled, beforeHeld, afterHeld⟩ :=
    actual_recorded_receive_lifetime references descriptors recording entry actual socket identity
  let point : SelectedNativeCut process child native hostUid before after callers next ticks entry.position := ⟨entry.tick, entry.cut⟩
  obtain ⟨before, after, preceding, suffix, actualSample, operation, suffixAt⟩ :=
    SocketReferenceRecording.selected_cut references recording point actual
  have same := Prod.mk.inj (Option.some.inj (actualSample.symm.trans sampled))
  have empty : entry.cut.trailing = [] := by
    apply List.length_eq_zero_iff.mp
    have count := congrArg List.length entry.cut.shape
    simp only [List.length_append, List.length_cons, ← entry.cut.count] at count
    omega
  have final := SocketReferenceRecording.empty_identity references suffix empty
  exact (same.2.symm.trans final) ▸ afterHeld

end LeanCage.Host.PrivateStreams
