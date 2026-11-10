import FilesystemCommitInterval
import FilesystemCommitMarker
import FilesystemPrivateMarker
import FilesystemLifetimePositions
import FilesystemRecordedAuthority

namespace LeanCage.Host.Kernel
open Filesystem PrivateStreams
universe u

private theorem selected_middle {α : Type u} (leading inside trailing : List α) (first last value : α)
    (offset : Nat) (selected : inside[offset]? = some value) :
    (leading ++ first :: inside ++ last :: trailing)[leading.length + 1 + offset]? = some value := by
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [List.append_assoc, List.cons_append, List.getElem?_append_right (by omega)]
  have index : leading.length + 1 + offset - leading.length = offset + 1 := by omega
  rw [index, List.getElem?_cons_succ, List.getElem?_append_left bound]
  exact selected

private theorem marker_fold {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {start finish : Population} {ticks : List (ActorTick runtime)} (journal : ActorJournal runtime start ticks finish)
    {object : ObjectId} {value : ByteArray}
    (steps : ∀ (offset : Nat) (tick : ActorTick runtime), ticks[offset]? = some tick →
      tick.before.shared.attributes object Publication.attributeName = some value →
      tick.after.shared.attributes object Publication.attributeName = some value)
    (marked : start.shared.attributes object Publication.attributeName = some value) :
    finish.shared.attributes object Publication.attributeName = some value := by
  induction journal with
  | nil => exact marked
  | @cons tick ticks finish tail ih =>
    apply ih
    · intro offset tick selected
      exact steps (offset + 1) tick selected
    · exact steps 0 tick rfl marked

private theorem live_snapshots {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (lifetimes : LifetimeContract runtime) (objects : ObjectLifetimeContract runtime)
    {start finish : Population} {ticks : List (ActorTick runtime)} {object : ObjectId}
    (journal : ActorJournal runtime start ticks finish) (old : start.shared.allocated object = true)
    (alive : ObjectAlive finish.shared object) :
    ∀ tick ∈ ticks, ObjectAlive tick.before.shared object ∧ ObjectAlive tick.after.shared object := by
  induction journal with
  | nil => intro tick impossible; cases impossible
  | @cons tick ticks finish tail ih =>
    have nextOld := actor_step_allocated lifetimes tick.operation object old
    have nextAlive := actor_journal_live_backward_for lifetimes objects tail nextOld alive
    intro row member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨actor_step_live_backward_for objects row.operation old nextAlive, nextAlive⟩
    · exact ih nextOld alive row later

-- §FS-host-boundary.publication: The publisher's exact acknowledged marker survives
-- to its own selected commit. Every interleaved native/source/foreign row uses its
-- SAME constructed custody snapshot and actual operands; no helper/tag frame is an input.
theorem CommitMarkerAt.current_marker {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    (lifetimes : LifetimeContract runtime) (objects : ObjectLifetimeContract runtime)
    (attributes : ExistingAttributeContract runtime child) (foreign : ForeignContract runtime)
    (nativeAttributes : NativeExistingAttributeContract native)
    {initial : World} {final : Population} {all : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {firstProcesses lastProcesses : Processes} {firstNative lastNative : NativeProcesses}
    {recording : NativeExternalJournal process child native hostUid firstProcesses firstNative all lastProcesses lastNative}
    (execution : RegisteredCustodyExecution runtime initial all hostUid dataObjects directories semantics recording
      [] (Population.empty initial) final)
    {backend : NativeAuthorityJournal recording}
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : all[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    {resources : PrimitiveCommitResources runtime initial all tick actor engine request observed}
    {family : Family} {catalogue : Catalogue runtime all} {root : CommitRootAt runtime resources family catalogue}
    {hmac : ByteArray → ByteArray → ByteArray} (marker : CommitMarkerAt (position := position) runtime root hmac) :
    tick.before.shared.attributes root.root.object Publication.attributeName = some (Publication.marker marker.receipt.tag) := by
  have born := journal_birth_before_allocated lifetimes execution.actual root.birth.selected marker.receipt.markerSelected
    root.birth.fresh.1 marker.beforeAllocated
  obtain ⟨leading, inside, trailing, trace, firstCount, lastCount, interval⟩ := journal_between_after_counted
    execution.actual marker.receipt.markerSelected selected marker.receipt.markerEarlier
  have actual := selected_filesystem_step tick action present
  have alive : ObjectAlive tick.before.shared root.root.object := by
    have reference := objects.reference _ _ _ _ _ _ actual resources.stage.directory.live
    simpa only [root.stage, Population.project, ObjectAlive] using reference
  have live := live_snapshots lifetimes objects interval marker.afterAllocated alive
  apply marker_fold interval _ marker.actualMarker
  intro offset row rowAt marked
  have bound := (List.getElem?_eq_some_iff.mp rowAt).1
  have rowIn : row ∈ inside := List.mem_iff_getElem.mpr ⟨offset, bound, (List.getElem?_eq_some_iff.mp rowAt).2⟩
  have fullAt : all[leading.length + 1 + offset]? = some row :=
    (congrArg (fun ticks : List (ActorTick runtime) => ticks[leading.length + 1 + offset]?) trace).trans
      (selected_middle leading inside trailing marker.receipt.markerTick tick row offset rowAt)
  obtain ⟨cut, cutAt⟩ := selectNativeCut_exists recording fullAt
  let point : SelectedNativeCut process child native hostUid firstProcesses lastProcesses firstNative lastNative all
      (leading.length + 1 + offset) := ⟨row, cut⟩
  obtain ⟨foreignReferences, state, label, binding, owner⟩ := root.registered_snapshot lifetimes execution selected present
    point cutAt (by omega) (by omega)
  exact registered_private_marker_step objects attributes foreign nativeAttributes state cut.current
    (recorded_authority_at recording backend point cutAt).2.1 label (live row rowIn).2 marked

end LeanCage.Host.Kernel
