import FilesystemCleanupFinalHistory
import FilesystemRunBoundary

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: The final stage removal still names its
-- original lifetime. The joint prefix supplies every actual ownership row;
-- earlier owner removals are derived from this same cleanup's source.
theorem actual_publication_cleanup_root_bound {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (frames : UnlinkDirectoryFrameContract kernel)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (targets : OpenTargetContract kernel semantics initial.allocated dataObjects)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {native : NativeProcesses}
    (state : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before native)
    (joint : JointPublicationPrefix state)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ tick :: trailing)
    {actor : ActorId} {engine : EngineState} (present : tick.before.actors actor = some engine)
    {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {call : PublicationCleanup.Host adapter.occurrence.logicalBefore request}
    (source : CleanupStageContinuation runtime initial all call processed.length (tick.before.project engine))
    (sameActor : source.earlier.source.inputActor = actor)
    (guards : source.earlier.guards = adapter.occurrence.inside.map Program.filesystemPrefixEvent)
    (eventTrace : engine.events = source.earlier.source.input.events ++
      .returned (.filesystem source.opening.request) source.opening.reply ::
        (source.earlier.post.map Program.filesystemEvent ++ source.earlier.remaining ++ source.earlier.guards))
    (segment : CleanupStageSegment source)
    (root : CleanupStageRootAt runtime source actor state.custody.current.source.custody.caps.family
      state.custody.current.source.custody.catalogue)
    (finalSource : Lowered.FinalCleanupFrontier call.source.attempt.context.parent call.source.attempt.context.stage
      call.source.effective call.source.attempt.inside request)
    (unlink : request.op = .unlinkAt) :
    tick.before.shared.entries root.root.parent root.root.name = some root.root.object := by
  have selected : all[processed.length]? = some tick := by
    rw [whole, List.getElem?_append_right (by omega)]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  have birthBefore : root.birth.position < processed.length := by
    rw [root.sourcePosition]
    exact Nat.lt_trans source.root.earlier source.earlier.source.earlier
  have birthAt : processed[root.birth.position]? = some root.birth.tick := by
    simpa only [whole, List.getElem?_append_left birthBefore] using root.birth.selected
  obtain ⟨cut⟩ := joint.history.selected_cut birthAt
  obtain ⟨birthScope⟩ := state.custody.current.births (Sigma.mk root.root root.birth) root.member
  have currentOpens := actual_private_directory_opens descriptors lifetimes targets journal selected present whole rfl
    state.custody.current.source.custody.history
  have opens : PrivateDirectoryOpens kernel (fun ordinal query reply before after =>
      SourceReturnAt runtime all source.earlier.source.inputActor ordinal Reply (.filesystem query) reply before after ∧
        ordinal < engine.events.length) state.custody.current.source.custody.caps.family := by
    simpa only [sameActor] using currentOpens
  have rootPrivate : state.custody.current.source.custody.caps.family source.earlier.source.opening.handle.object =
      some root.root.object := by rw [root.directory]; exact root.privateRoot
  have useActor : source.root.use.actor = actor := source.root.sameActor.trans sameActor
  obtain ⟨born, bornPresent, appended⟩ := source_event_after source.root.birthTick source.root.use.action source.root.use.present
  have bornAt : root.birth.tick.after.actors actor = some born := by
    exact (congrArg (fun birth : ActorTick runtime => birth.after.actors actor) root.sourceBirth).trans
      ((congrArg source.root.birthTick.after.actors useActor).symm.trans bornPresent)
  have bornCount : born.events.length = source.root.use.engine.events.length + 1 := by
    simp only [appended, List.length_append, List.length_singleton]
  have noPublication := actor_interval_request_profile (fun query => query.op ≠ .renameNew)
    cut.remaining.ownership.actual bornAt present (by
      rw [bornCount]
      exact source.no_publication engine.events eventTrace (by
        rw [guards]
        exact adapter_namespace_prefix_nondestructive adapter (.inr (.inr (.inl unlink)))))
  apply cut.remaining.private_binding lifetimes state.custody.current.source.custody.valid root.owned
    root.birth.fresh.2 root.privateRoot root.birth.bound
  intro earlier member query answer action destructive binding
  rcases destructive with removing | moving
  · obtain ⟨offset, bounded, atOffset⟩ := List.mem_iff_getElem.mp member
    have inTail : cut.trailing[offset]? = some earlier := List.getElem?_eq_some_iff.mpr ⟨bounded, atOffset⟩
    let earlierPosition := cut.leading.length + 1 + offset
    have atEarlier : all[earlierPosition]? = some earlier := by
      rw [whole, cut.trace]
      have baseBound : cut.leading.length ≤ earlierPosition := by dsimp only [earlierPosition]; omega
      rw [List.getElem?_append_left (by
        simp only [List.length_append, List.length_cons]
        dsimp only [earlierPosition]
        omega), List.getElem?_append_right baseBound]
      have count : earlierPosition - cut.leading.length = offset + 1 := by dsimp only [earlierPosition]; omega
      rw [count]
      exact inTail
    have afterBirth : source.root.birthPosition < earlierPosition := by
      have position := cut.count.trans root.sourcePosition
      dsimp only [earlierPosition]
      omega
    have beforeCurrent : earlierPosition < processed.length := by
      have length := congrArg List.length cut.trace
      simp only [List.length_append, List.length_cons] at length
      dsimp only [earlierPosition]
      omega
    obtain ⟨input, inputPresent⟩ := tick_event_engine earlier action
    have atEvent := prior_source_event_index journal atEarlier selected beforeCurrent action inputPresent present
    cases answer with
    | none =>
      exact False.elim (actor_history_excludes_lost adapter.source.history (.filesystem query)
        (List.mem_of_getElem? atEvent))
    | some reply =>
      have returned := filesystem_event_returned_action action
      obtain ⟨output, sample⟩ := selected_source_return atEarlier inputPresent returned
      have birthAction : source.root.birthTick.action = .returned actor (.filesystem source.root.use.request) source.root.use.reply := by
        apply filesystem_event_returned_action
        exact Eq.mp (congrArg (fun who => source.root.birthTick.action.eventFor who =
          some (.returned (.filesystem source.root.use.request) source.root.use.reply)) useActor) source.root.use.action
      have birthPresent : source.root.birthTick.before.actors actor = some source.root.use.engine := by
        exact (congrArg source.root.birthTick.before.actors useActor).symm.trans source.root.use.present
      have sourceOrder := returned_positions_order_source_ordinals journal source.root.birthAt atEarlier afterBirth
        birthAction birthPresent inputPresent
      obtain ⟨parent, live, privateParent, component⟩ := segment.captured_previous_unlink descriptors journal adapter
        sameActor guards eventTrace unlink opens rootPrivate finalSource sample atEvent (by omega) removing
      apply frames.otherDirectory (earlier.before.project input) earlier.after.shared query (some reply)
        parent root.root.parent root.root.name root.root.object
        (selected_filesystem_step earlier action inputPresent) removing component live ?_ binding
      intro equalParent
      rw [equalParent, birthScope.parentPublic] at privateParent
      cases privateParent
  · exact False.elim (noPublication earlier member query answer action moving)

end LeanCage.Host.Kernel
