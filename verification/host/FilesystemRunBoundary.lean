import FilesystemRunCustody
import FilesystemCleanupHistory
import FilesystemOwnershipRetention

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: A single-component unlink in one resolved
-- directory does not change another directory's stored bindings. This law
-- needs no byte-exact comparison inside the selected directory.
structure UnlinkDirectoryFrameContract (kernel : Contract) : Prop where
  otherDirectory : ∀ before after request observed parent target name object,
    kernel.step before request observed after → request.op = .unlinkAt →
    Directories.component request.left = true → before.handles request.first = some parent →
    parent.object ≠ target → before.entries target name = some object →
    after.entries target name = some object

-- §FS-host-boundary.ownership: A genuine earlier unlink on this same actor
-- is a completed inner-directory use. A prior lost call cannot precede this
-- actual later source head; the current call itself may still return or lose.
theorem previous_run_unlink_reference {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} (present : tick.before.actors actor = some engine)
    {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {outside : List Program.Event} {created : List (Request × Reply)} {run : RunDirectory.Owned}
    {work : List Program.Event} {inside : List (Request × Option Reply)}
    (source : RunCleanupParent runtime initial all actor engine.events outside created run work inside request
      adapter.occurrence.rawBefore.length position (tick.before.project engine))
    (segment : CleanupOccurrenceSegment source) (unlink : request.op = .unlinkAt)
    {earlierPosition : Nat} {earlier : ActorTick runtime} (atEarlier : all[earlierPosition]? = some earlier)
    (afterBirth : source.allocation.root.birthPosition < earlierPosition) (beforeCurrent : earlierPosition < position)
    {query : Request} {answer : Option Reply}
    (action : earlier.action.eventFor actor = some (Program.filesystemPrefixEvent (query, answer)))
    (removing : query.op = .unlinkAt) :
    ∃ input, earlier.before.actors actor = some input ∧ Directories.component query.left = true ∧
      input.references query.first = some source.allocation.earlier.source.opening.handle := by
  obtain ⟨input, inputPresent⟩ := tick_event_engine earlier action
  have atEvent := prior_source_event_index journal atEarlier selected beforeCurrent action inputPresent present
  cases answer with
  | none =>
    have impossible := actor_history_excludes_lost adapter.source.history (.filesystem query)
      (List.mem_of_getElem? atEvent)
    exact False.elim impossible
  | some reply =>
    have returned : earlier.action = .returned actor (.filesystem query) reply := filesystem_event_returned_action action
    obtain ⟨output, sample⟩ := selected_source_return atEarlier inputPresent returned
    have useActor : source.allocation.root.use.actor = actor :=
      source.allocation.root.sameActor.trans source.sameActor
    have birthAction : source.allocation.root.birthTick.action =
        .returned actor (.filesystem source.allocation.root.use.request) source.allocation.root.use.reply := by
      apply filesystem_event_returned_action
      exact Eq.mp (congrArg (fun who => source.allocation.root.birthTick.action.eventFor who =
        some (.returned (.filesystem source.allocation.root.use.request) source.allocation.root.use.reply)) useActor)
        source.allocation.root.use.action
    have birthPresent : source.allocation.root.birthTick.before.actors actor = some source.allocation.root.use.engine := by
      exact (congrArg source.allocation.root.birthTick.before.actors useActor).symm.trans source.allocation.root.use.present
    have sourceOrder := returned_positions_order_source_ordinals journal source.allocation.root.birthAt atEarlier
      afterBirth birthAction birthPresent inputPresent
    obtain ⟨descriptor, component, resource⟩ := segment.captured_unlink descriptors journal unlink sample atEvent
      (by omega) removing
    refine ⟨input, inputPresent, component, ?_⟩
    rw [descriptor]
    exact resource

-- §FS-host-boundary.ownership: The final parent-relative removal still names
-- the original lifetime. The joint induction prefix supplies correlated
-- labels/removals, and actual earlier source unlinks supply their operands.
theorem actual_run_cleanup_root_bound {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (frames : UnlinkDirectoryFrameContract kernel)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {native : NativeProcesses}
    (state : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before native)
    (joint : JointPublicationPrefix state)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ tick :: trailing)
    {actor : ActorId} {engine : EngineState} (present : tick.before.actors actor = some engine)
    {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {outside : List Program.Event} {created : List (Request × Reply)} {run : RunDirectory.Owned}
    {work : List Program.Event} {inside : List (Request × Option Reply)}
    (source : RunCleanupParent runtime initial all actor engine.events outside created run work inside request
      adapter.occurrence.rawBefore.length processed.length (tick.before.project engine))
    (root : RunCleanupRootAt runtime source state.custody.current.source.custody.caps.family
      state.custody.current.source.custody.catalogue)
    (unlink : request.op = .unlinkAt) :
    tick.before.shared.entries root.root.parent root.root.name = some root.root.object := by
  have selected : all[processed.length]? = some tick := by
    rw [whole, List.getElem?_append_right (by omega)]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  have birthBefore : root.birth.position < processed.length := by
    rw [root.sourcePosition]
    exact Nat.lt_trans source.allocation.root.earlier source.allocation.earlier.source.earlier
  have birthAt : processed[root.birth.position]? = some root.birth.tick := by
    simpa only [whole, List.getElem?_append_left birthBefore] using root.birth.selected
  obtain ⟨cut⟩ := joint.history.selected_cut birthAt
  obtain ⟨segment⟩ := actual_cleanup_occurrence_segment source
  have useActor : source.allocation.root.use.actor = actor :=
    source.allocation.root.sameActor.trans source.sameActor
  have sourceActual := selected_filesystem_step source.allocation.root.birthTick source.allocation.root.use.action
    source.allocation.root.use.present
  have parentAllocated : source.allocation.root.birthTick.before.shared.allocated root.root.parent = true := by
    have allocated := descriptors.reference_allocated _ _ _ _ _ _ sourceActual source.allocation.root.use.reference
    change source.allocation.root.birthTick.before.shared.allocated source.allocation.root.use.parent.object = true at allocated
    exact (congrArg source.allocation.root.birthTick.before.shared.allocated root.container).symm.trans allocated
  have parentDifferent : root.root.parent ≠ root.root.object := by
    intro same
    have fresh : source.allocation.root.birthTick.before.shared.allocated root.root.object = false := by
      rw [← root.sourceBirth]
      exact root.birth.fresh.1
    rw [same, fresh] at parentAllocated
    cases parentAllocated
  obtain ⟨born, bornPresent, appended⟩ := source_event_after source.allocation.root.birthTick
    source.allocation.root.use.action source.allocation.root.use.present
  have bornAt : root.birth.tick.after.actors actor = some born := by
    exact (congrArg (fun birth : ActorTick runtime => birth.after.actors actor) root.sourceBirth).trans
      ((congrArg source.allocation.root.birthTick.after.actors useActor).symm.trans bornPresent)
  have bornCount : born.events.length = source.allocation.root.use.engine.events.length + 1 := by
    simp only [appended, List.length_append, List.length_singleton]
  have noPublication := actor_interval_request_profile (fun query => query.op ≠ .renameNew)
    cut.remaining.ownership.actual bornAt present (by rw [bornCount]; exact source.source_no_publication)
  apply cut.remaining.private_binding lifetimes state.custody.current.source.custody.valid root.owned
    root.birth.fresh.2 root.privateRoot root.birth.bound
  intro earlier member query answer action destructive binding
  rcases destructive with removing | moving
  · obtain ⟨offset, bound, atOffset⟩ := List.mem_iff_getElem.mp member
    have inTail : cut.trailing[offset]? = some earlier := List.getElem?_eq_some_iff.mpr ⟨bound, atOffset⟩
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
    have afterBirth : source.allocation.root.birthPosition < earlierPosition := by
      have position := cut.count.trans root.sourcePosition
      dsimp only [earlierPosition]
      omega
    have beforeCurrent : earlierPosition < processed.length := by
      have length := congrArg List.length cut.trace
      simp only [List.length_append, List.length_cons] at length
      dsimp only [earlierPosition]
      omega
    obtain ⟨input, inputPresent, component, reference⟩ := previous_run_unlink_reference descriptors journal selected
      present adapter source segment unlink atEarlier afterBirth beforeCurrent action removing
    apply frames.otherDirectory (earlier.before.project input) earlier.after.shared query answer
      source.allocation.earlier.source.opening.handle root.root.parent root.root.name root.root.object
      (selected_filesystem_step earlier action inputPresent) removing component reference ?_ binding
    rw [root.directory]
    exact Ne.symm parentDifferent
  · exact False.elim (noPublication earlier member query answer action moving)

end LeanCage.Host.Kernel
