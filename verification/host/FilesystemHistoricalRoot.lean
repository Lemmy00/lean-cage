import FilesystemOwnershipCuts
import FilesystemRootReopen
import FilesystemDirectoryObjects

namespace LeanCage.Host.Kernel
open Filesystem
universe u

private theorem selected_suffix {α : Type u} {events first last : List α} {position : Nat} {value : α}
    (trace : events = first ++ last) (afterFirst : first.length ≤ position)
    (selected : events[position]? = some value) :
    ∃ offset, position = first.length + offset ∧ last[offset]? = some value := by
  subst events
  induction first generalizing position with
  | nil => exact ⟨position, by simp only [List.length_nil, Nat.zero_add], selected⟩
  | cons head tail ih =>
    cases position with
    | zero => simp only [List.length_cons] at afterFirst; omega
    | succ position =>
      have remaining : tail.length ≤ position := by simp only [List.length_cons] at afterFirst; omega
      have selected : (tail ++ last)[position]? = some value := by
        simpa only [List.cons_append, List.getElem?_cons_succ] using selected
      obtain ⟨offset, count, selected⟩ := ih remaining selected
      exact ⟨offset, by simp only [List.length_cons]; omega, selected⟩

-- §FS-host-boundary.ownership: A later completed root observation selects the earlier
-- binding at its actual open row, before subsequent content writes or publication.
-- The current catalogue supplies owner uniqueness, not future allocation at that old cut.
theorem registered_root_before_selected_open {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (lifetimes : LifetimeContract runtime)
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {population : Population} {native : NativeProcesses}
    (state : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed population native)
    {birthPosition : Nat} {birthTick : ActorTick runtime} (birthAt : processed[birthPosition]? = some birthTick)
    (use : PrimitiveRootUse runtime initial all birthTick)
    {openPosition : Nat} {openTick : ActorTick runtime} (openAt : processed[openPosition]? = some openTick)
    (earlier : birthPosition < openPosition) {engine : EngineState}
    (present : openTick.before.actors use.actor = some engine)
    (source : ∀ event ∈ engine.events.drop (use.engine.events.length + 1), NondestructiveEvent event) :
    ∃ (root : PrivateRoot) (birth : RootBirth runtime all root),
      birth.tick = birthTick ∧ birth.position = birthPosition ∧
      Sigma.mk root birth ∈ state.current.source.custody.catalogue ∧
      root.actor = use.actor ∧ root.parent = use.parent.object ∧ root.name = use.request.left ∧
      openTick.before.shared.entries use.parent.object use.request.left = some root.object ∧
      state.current.source.custody.catalogue.Owns use.actor root.object := by
  obtain ⟨root, birth, current, ordinal, member, owner, parent, name, scopeCut⟩ := state.root_scope birthAt use
  obtain ⟨scopeCut⟩ := scopeCut
  have splitTrace : processed = (scopeCut.leading ++ [birth.tick]) ++ scopeCut.trailing := by
    simpa only [List.append_assoc, List.singleton_append] using scopeCut.trace
  have prefixCount : (scopeCut.leading ++ [birth.tick]).length = birthPosition + 1 := by
    simp only [List.length_append, List.length_singleton, scopeCut.count, ordinal]
  have beforeSelected : (scopeCut.leading ++ [birth.tick]).length ≤ openPosition := by
    rw [prefixCount]
    omega
  obtain ⟨offset, position, selected⟩ := selected_suffix splitTrace beforeSelected openAt
  obtain ⟨cut⟩ := scopeCut.ownership.selected_cut selected
  obtain ⟨born, bornPresent, appended⟩ := source_event_after birthTick use.action use.present
  have bornPresent : birth.tick.after.actors use.actor = some born := by rwa [current]
  have count : born.events.length = use.engine.events.length + 1 := by
    simp only [appended, List.length_append, List.length_singleton]
  have actualSource := actor_interval_nondestructive_profile cut.initial.actual bornPresent present
    (by rw [count]; exact source)
  have owned : state.current.source.custody.catalogue.Owns use.actor root.object :=
    ⟨Sigma.mk root birth, member, owner, rfl⟩
  obtain ⟨bound, label⟩ := cut.initial.private_binding_retained_catalogued lifetimes
    state.current.source.custody.valid owned birth.fresh.2 scopeCut.privateRoot birth.bound actualSource
  exact ⟨root, birth, current, ordinal, member, owner, parent, name,
    by simpa only [parent, name] using bound, owned⟩

-- §FS-host-boundary.ownership: The actual acknowledged reopen selects the SAME lifetime
-- born at that mkdir. A mounted old inode or an unrelated equal-shaped open cannot supply it.
theorem registered_root_handle_at {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (mounts : MountContract kernel initial.allocated)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {population : Population} {native : NativeProcesses}
    (state : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed population native)
    {birthPosition : Nat} {birthTick : ActorTick runtime} (birthAt : processed[birthPosition]? = some birthTick)
    (use : PrimitiveRootUse runtime initial all birthTick)
    {openPosition : Nat} {openTick : ActorTick runtime} (openAt : processed[openPosition]? = some openTick)
    (earlier : birthPosition < openPosition) {engine : EngineState}
    (present : openTick.before.actors use.actor = some engine) {request : Request} {reply : Reply} {fd : UInt64}
    (action : openTick.action.eventFor use.actor = some (Program.filesystemPrefixEvent (request, some reply)))
    (opening : request.op = .openAt) (flags : request.second = directoryFlags)
    (sameName : request.left = use.request.left) (reference : engine.references request.first = some use.parent)
    (recognized : descriptor reply = some fd)
    (source : ∀ event ∈ engine.events.drop (use.engine.events.length + 1), NondestructiveEvent event) :
    ∃ (root : PrivateRoot) (birth : RootBirth runtime all root),
      birth.tick = birthTick ∧ birth.position = birthPosition ∧
      Sigma.mk root birth ∈ state.current.source.custody.catalogue ∧
      root.actor = use.actor ∧ root.parent = use.parent.object ∧ root.name = use.request.left ∧
      ∃ handle, openTick.after.shared.handles fd = some handle ∧ handle.object = root.object ∧ handle.rawOwned = true := by
  obtain ⟨root, birth, current, ordinal, member, owner, parent, name, bound, owned⟩ :=
    registered_root_before_selected_open lifetimes state birthAt use openAt earlier present source
  have actual := selected_filesystem_step openTick action present
  have component : Directories.component request.left = true := by rw [sameName]; exact use.component
  have reserved : PrivateNames.reservedBytes request.left = true := by
    rw [sameName, ← name, ← birth.name]
    exact birth.reserved
  have notDot : request.left ≠ ".".toUTF8 := by
    intro same
    rw [same] at reserved
    exact Bool.noConfusion reserved
  have notUp : request.left ≠ "..".toUTF8 := by
    intro same
    rw [same] at reserved
    exact Bool.noConfusion reserved
  have openBound : (openTick.before.project engine).entries use.parent.object request.left = some root.object := by
    change openTick.before.shared.entries use.parent.object request.left = some root.object
    rw [sameName]
    exact bound
  obtain ⟨handle, live, same⟩ := fresh_directory_lookup mounts actual opening flags reference recognized
    component notDot notUp openBound (root_birth_not_initial lifetimes journal birth)
  exact ⟨root, birth, current, ordinal, member, owner, parent, name, handle, live, same,
    descriptors.allocated_raw _ _ _ _ _ _ actual (.inl opening) recognized live⟩

end LeanCage.Host.Kernel
