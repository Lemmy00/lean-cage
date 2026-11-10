import GatewayChannelEngineSource
import GatewayStreamReadSources

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem
universe u

private theorem selected_after_head_member {α : Type u} {all leading trailing : List α} {head item : α} {position : Nat}
    (shape : all = leading ++ head :: trailing) (selected : all[position]? = some item)
    (later : leading.length < position) : item ∈ trailing := by
  have atItem := selected
  rw [shape, List.getElem?_append_right (by omega)] at atItem
  generalize offset : position - leading.length = index at atItem
  cases index with
  | zero => omega
  | succ index => exact List.mem_of_getElem? atItem

-- §FS-host-boundary.ownership: Every actual raw engine read is excluded
-- from the original caller OFD. Source entries before its birth contradict
-- real freshness; later entries consume the cumulative same-history fold.
theorem actual_engine_read_not_original_socket {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
    {ticks : List (ActorTick runtime)} {pair : Pair} {ipc : ObjectId → Prop}
    (sockets : SocketPairContract native ipc) (descriptions : NativeDescriptionContract native)
    (raw : RawReferenceLifetimeContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (namespaceLaws : NativeNamespaceContract native)
    {initial : World} {final : Population} (source : ActorJournal runtime (Population.empty initial) ticks final)
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (channels : EngineChannelRows journal)
    (birth : PairBirthEntry process child native hostUid before after callers next ticks pair)
    (actual : ActualPairBirth journal birth) (entry : EngineReadEntry ticks pair) :
    ¬ birth.callerSocket.matches entry.handle := by
  intro identity
  have fresh := pair_birth_description_fresh sockets birth
  have consistent := (actor_journal_consistent descriptors lifetimes references source
    (empty_population_consistent initial)).2 entry.tick (List.mem_of_getElem? entry.selected) |>.1
  have allocated := (consistent entry.actor entry.engine entry.present entry.request.first entry.handle entry.input).2.1
  change entry.handle.object = pair.caller ∧ entry.handle.description = birth.firstHandle.description at identity
  rw [identity.2] at allocated
  rcases Nat.lt_trichotomy entry.position birth.position with earlier | same | later
  · have afterEntry := actor_step_description_allocated references entry.tick.operation _ allocated
    have impossible := selected_description_before references source earlier entry.selected (pair_birth_selected birth) _ afterEntry
    rw [fresh] at impossible
    cases impossible
  · have atBirth := pair_birth_selected birth
    have atEntry := entry.selected
    rw [same] at atEntry
    have ticksSame := Option.some.inj (atEntry.symm.trans atBirth)
    have impossible : birth.tick.before.shared.descriptionAllocated birth.firstHandle.description = true := ticksSame ▸ allocated
    rw [fresh] at impossible
    cases impossible
  · have families := (actual_engine_family_excludes_caller_ofd sockets descriptions raw sdk descriptors lifetimes
      references namespaceLaws source journal channels birth actual).2
    have member := selected_after_head_member birth.cut.shape entry.selected (by simpa only [birth.cut.count] using later)
    exact (families entry.tick member).1 entry.actor entry.engine entry.present entry.request.first entry.handle entry.input identity

end LeanCage.Host.PrivateStreams
