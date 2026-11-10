import FilesystemCustodyCuts
import FilesystemCommitRoot
import FilesystemPrimitiveIntervals

namespace LeanCage.Host.Kernel
open Filesystem PrivateStreams
universe u

private theorem at_cut {α : Type u} (leading trailing : List α) (value : α) (position : Nat)
    (count : position = leading.length) : (leading ++ value :: trailing)[position]? = some value := by
  subst position
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self, List.getElem?_cons_zero]

-- §FS-host-boundary.publication: Every intermediate snapshot derives this root's
-- current binding/label from its own registered SAME-birth source prefix. It never
-- copies a later family label backwards or assumes an interval/private-region frame.
theorem CommitRootAt.registered_snapshot {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    (lifetimes : LifetimeContract runtime)
    {initial : World} {final : Population} {all : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {firstProcesses lastProcesses : Processes} {firstNative lastNative : NativeProcesses}
    {recording : NativeExternalJournal process child native hostUid firstProcesses firstNative all lastProcesses lastNative}
    (execution : RegisteredCustodyExecution runtime initial all hostUid dataObjects directories semantics recording
      [] (Population.empty initial) final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : all[position]? = some tick)
    (present : tick.before.actors actor = some engine)
    {resources : PrimitiveCommitResources runtime initial all tick actor engine request observed}
    {family : Family} {catalogue : Catalogue runtime all} (root : CommitRootAt runtime resources family catalogue)
    {ordinal : Nat} (point : SelectedNativeCut process child native hostUid firstProcesses lastProcesses
      firstNative lastNative all ordinal)
    (same : selectNativeCut recording ordinal = some point)
    (born : root.birth.position < ordinal) (earlier : ordinal ≤ position) :
    ∃ foreignReferences, ∃ state : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
        foreignReferences point.cut.leading point.tick.before point.cut.priorNative,
      state.current.source.custody.caps.family root.root.object = some root.root.object ∧
      point.tick.before.shared.entries root.root.parent root.root.name = some root.root.object ∧
      state.current.source.custody.catalogue.Owns actor root.root.object := by
  obtain ⟨foreignReferences, ⟨state⟩⟩ := execution.selected_before point same
  have state : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences point.cut.leading point.tick.before point.cut.priorNative := by
    simpa only [List.nil_append] using state
  have pointAt : all[ordinal]? = some point.tick := by
    calc
      all[ordinal]? = (point.cut.leading ++ point.tick :: point.cut.trailing)[ordinal]? :=
        congrArg (fun events : List (ActorTick runtime) => events[ordinal]?) point.cut.shape
      _ = some point.tick := at_cut _ _ _ _ point.cut.count
  have birthAt : all[root.birth.position]? = some root.sourceTick := by
    rw [← root.sourceBirth]
    exact root.birth.selected
  have birthBefore : point.cut.leading[root.birth.position]? = some root.sourceTick := by
    have bound : root.birth.position < point.cut.leading.length := by rw [← point.cut.count]; exact born
    simpa only [point.cut.shape, List.getElem?_append_left bound] using birthAt
  obtain ⟨leading, inside, trailing, trace, region⟩ :=
    journal_between_selected execution.actual birthAt pointAt (Nat.le_of_lt born)
  obtain ⟨current, currentPresent⟩ := actor_journal_presence region root.sourceUse.present
  obtain ⟨leading, inside, trailing, trace, following⟩ :=
    journal_between_selected execution.actual pointAt selected earlier
  have finalPresent : tick.before.actors root.sourceUse.actor = some engine := by
    rw [← root.sourceOwner, root.owner]
    exact present
  obtain ⟨remaining, events⟩ := actor_journal_event_prefix following root.sourceUse.actor current engine
    currentPresent finalPresent
  have quiet : ∀ event ∈ current.events.drop (root.sourceUse.engine.events.length + 1), NondestructiveEvent event := by
    intro event member
    apply root.sourceQuiet event
    rw [events, List.drop_append]
    exact List.mem_append_left _ member
  obtain ⟨bound, privateRoot, owner⟩ := state.source_birth_current lifetimes birthBefore root.sourceUse
    root.birth root.sourceBirth root.sourceOwner currentPresent quiet
  exact ⟨foreignReferences, state, privateRoot, bound, by
    simpa only [← root.sourceOwner, root.owner] using owner⟩

end LeanCage.Host.Kernel
