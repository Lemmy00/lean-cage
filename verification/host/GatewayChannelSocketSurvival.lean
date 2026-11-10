import GatewayChannelReceiveLifetime
import GatewayChannelEngineAbsence

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
  {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)} {pair : Pair}

theorem actual_old_ofd_after_birth {ipc : ObjectId → Prop} (sockets : SocketPairContract native ipc)
    (lifetimes : ReferenceContract runtime) {initial : World} {final : Population}
    (source : ActorJournal runtime (Population.empty initial) ticks final)
    (birth : PairBirthEntry process child native hostUid before after callers next ticks pair)
    {position : Nat} (point : SelectedNativeCut process child native hostUid before after callers next ticks position)
    (old : point.tick.before.shared.descriptionAllocated birth.firstHandle.description = true) :
    birth.position < position := by
  have atPoint : ticks[position]? = some point.tick := by
    have shape := congrArg (fun items : List (ActorTick runtime) => items[position]?) point.cut.shape
    exact shape.trans (by simp only [point.cut.count, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero])
  have fresh := pair_birth_description_fresh sockets birth
  rcases Nat.lt_trichotomy position birth.position with earlier | same | later
  · have allocated := actor_step_description_allocated lifetimes point.tick.operation _ old
    have impossible := selected_description_before lifetimes source earlier atPoint (pair_birth_selected birth) _ allocated
    rw [fresh] at impossible
    cases impossible
  · have atBirth := pair_birth_selected birth
    have atPoint' := (congrArg (fun index : Nat => ticks[index]?) same).symm.trans atPoint
    have equal := Option.some.inj (atPoint'.symm.trans atBirth)
    have impossible : birth.tick.before.shared.descriptionAllocated birth.firstHandle.description = true := equal ▸ old
    rw [fresh] at impossible
    cases impossible
  · exact later

-- §FS-host-boundary.ownership: The actual birth anchors this old OFD only
-- AFTER creation. In particular no "already allocated" premise is imposed
-- on the global pre-birth boundary where freshness proves the opposite.
theorem actual_socket_held_after_birth
    (references : SocketReferenceRuntime process child native hostUid)
    (lifetimes : ReferenceContract runtime) (descriptions : NativeDescriptionContract native)
    {journal : NativeExternalJournal process child native hostUid before callers ticks after next}
    {first last : SocketReferenceSnapshot} (recording : SocketReferenceRecording references journal first last)
    (birth : PairBirthEntry process child native hostUid before after callers next ticks pair)
    (actual : ActualPairBirth journal birth) (terminal : last.held birth.callerSocket)
    (position : Nat) (order : birth.position ≤ position)
    (current following : SocketReferenceSnapshot)
    (sampled : SocketReferenceRecording.at references recording position = some (current, following)) :
    following.held birth.callerSocket := by
  let point : SelectedNativeCut process child native hostUid before after callers next ticks birth.position := ⟨birth.tick, birth.cut⟩
  obtain ⟨initial, allocated, preceding, suffix, atBirth, operation, suffixAt⟩ :=
    SocketReferenceRecording.selected_cut references recording point actual
  have population := (references.output operation).1
  have nativeState := (references.output operation).2.1
  have old : allocated.population.shared.descriptionAllocated birth.callerSocket.description = true := by
    simpa only [population, point, PairBirthEntry.callerSocket, PairBirthEntry.endpointHandle] using
      pair_birth_description_allocated descriptions birth .caller
  by_cases same : position = birth.position
  · have selected := sampled
    rw [same] at selected
    have state := Prod.mk.inj (Option.some.inj (atBirth.symm.trans selected))
    have retained : allocated.held birth.callerSocket := by
      refine ⟨.native birth.call.token birth.first, birth.firstHandle, ?_, birth.callerObject, rfl⟩
      simp only [SocketReferenceSnapshot.at, nativeState, point, birth.call.outputTable, Option.bind_some, birth.firstInput]
    exact state.2 ▸ retained
  · let offset := position - (birth.position + 1)
    have index : birth.position + 1 + offset = position := by dsimp only [offset]; omega
    have selected : SocketReferenceRecording.at references suffix offset = some (current, following) := by
      rw [suffixAt offset, index]
      exact sampled
    obtain ⟨tick, atTick⟩ := SocketReferenceRecording.at_has_tick references suffix selected
    obtain ⟨cut, atCut⟩ := selectNativeCut_exists birth.cut.last atTick
    let later : SelectedNativeCut process child native hostUid birth.cut.nextProcesses after birth.cut.nextNative next birth.cut.trailing offset :=
      ⟨tick, cut⟩
    obtain ⟨before, after, selectedStates, beforeHeld, afterHeld⟩ :=
      SocketReferenceRecording.selected_held references lifetimes suffix birth.callerSocket old terminal later atCut
    have states := Prod.mk.inj (Option.some.inj (selectedStates.symm.trans selected))
    exact states.2 ▸ afterHeld

-- The actual caller receive supplies the terminal reference in this finite
-- prefix, even if its SDK reply is subsequently lost. It is never replaced
-- by an engine-return, response-completion or eventual-reap assumption.
theorem actual_receive_excludes_postbirth_last_drop
    (references : SocketReferenceRuntime process child native hostUid)
    (lifetimes : ReferenceContract runtime) (descriptions : NativeDescriptionContract native)
    (descriptors : NativeReferenceContract native)
    {journal : NativeExternalJournal process child native hostUid before callers ticks after next}
    {first last : SocketReferenceSnapshot} (recording : SocketReferenceRecording references journal first last)
    (birth : PairBirthEntry process child native hostUid before after callers next ticks pair)
    (actual : ActualPairBirth journal birth)
    (entry : NativeReadEntry process child native hostUid before after callers next ticks pair)
    (received : ActualNativeRead journal entry) (terminal : entry.position + 1 = ticks.length)
    (receiver : entry.receiver = .caller) (description : entry.handle.description = birth.firstHandle.description)
    (position : Nat) (order : birth.position ≤ position)
    (current following : SocketReferenceSnapshot)
    (sampled : SocketReferenceRecording.at references recording position = some (current, following)) :
    ¬ following.released birth.callerSocket := by
  have identity : birth.callerSocket.matches entry.handle :=
    ⟨by simpa only [receiver, Pair.endpoint, PairBirthEntry.callerSocket] using entry.endpoint, description⟩
  have held := actual_terminal_receive_holds_socket references descriptors recording entry received terminal birth.callerSocket identity
  exact following.held_not_released birth.callerSocket
    (actual_socket_held_after_birth references lifetimes descriptions recording birth actual held position order current following sampled)

end LeanCage.Host.PrivateStreams
