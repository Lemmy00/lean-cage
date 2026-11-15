import FilesystemRunFileResources
import FilesystemRootRetention

namespace LeanCage.Host.Kernel
open Filesystem
universe u

private theorem chunks_quiet {logical raw : List Program.Event}
    (source : PrimitiveFilesystem.Chunks logical raw) (quiet : ∀ event ∈ logical, NondestructiveEvent event) :
    ∀ event ∈ raw, NondestructiveEvent event := by
  induction source with
  | nil => intro event impossible; cases impossible
  | cons effect reply inside logical raw adapter remaining ih =>
    intro event member
    rcases List.mem_append.mp member with first | last
    · have head := quiet (.returned effect reply) (by simp)
      cases effect with
      | filesystem request =>
        obtain ⟨events, returned, trace⟩ := Program.lift_filesystem_source (guardedCall request) adapter
        rw [trace] at first
        obtain ⟨⟨operation, answer⟩, occurs, rfl⟩ := List.mem_map.mp first
        have role := profile_returns (guarded_call_profile request) returned (operation, answer) occurs
        change AdapterRequest request operation at role
        change ¬ DestructiveRequest operation
        rcases role with same | magic | flags | close
        · rw [same]; exact head
        · simp [DestructiveRequest, magic]
        · simp [DestructiveRequest, flags]
        · simp [DestructiveRequest, close]
      | spawn | read | wait | terminate | tryWait | descriptor =>
        have singleton := PrimitiveFilesystem.effect_returns_singleton _ adapter
        rw [singleton] at first
        have same := List.mem_singleton.mp first
        subst event
        exact True.intro
    · exact ih (by intro event occurs; exact quiet event (List.mem_cons_of_mem _ occurs)) event last

private theorem drop_append_allowed {α : Type u} {first last : List α} (count : Nat) (allowed : α → Prop)
    (leading : ∀ event ∈ first.drop count, allowed event) (trailing : ∀ event ∈ last, allowed event) :
    ∀ event ∈ (first ++ last).drop count, allowed event := by
  intro event member
  rw [List.drop_append] at member
  rcases List.mem_append.mp member with member | member
  · exact leading event member
  · exact trailing event (List.mem_of_mem_drop member)

theorem RunFileResources.source_nondestructive {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed}
    {call : RunFileCall adapter.occurrence.logicalBefore request} {position : Nat}
    (resources : RunFileResources adapter call position) (opening : request.op = .openAt) :
    ∀ event ∈ engine.events.drop (resources.source.root.use.engine.events.length + 1), NondestructiveEvent event := by
  apply Eq.mpr (congrArg (fun events : List Program.Event =>
    ∀ event ∈ events.drop (resources.source.root.use.engine.events.length + 1), NondestructiveEvent event) resources.eventTrace)
  apply drop_append_allowed
  · intro event member
    exact passive_event_nondestructive (resources.source.root.probes event member)
  · intro event member
    rcases List.mem_cons.mp member with rfl | member
    · change ¬ DestructiveRequest resources.source.opening.request
      simp [DestructiveRequest, resources.source.opening.opening]
    · rcases List.mem_append.mp member with member | guardMember
      · rcases List.mem_append.mp member with postMember | remainingMember
        · obtain ⟨⟨operation, reply⟩, occurs, rfl⟩ := List.mem_map.mp postMember
          exact namespace_passive_not_destructive (resources.source.earlier.passive (operation, reply) occurs)
        · apply chunks_quiet resources.source.earlier.chunks ?_ event remainingMember
          intro candidate occurs
          rcases List.mem_append.mp occurs with created | following
          · obtain ⟨⟨operation, reply⟩, member, rfl⟩ := List.mem_map.mp created
            exact resources.source.opening.nondestructive (operation, reply) member
          · obtain ⟨⟨operation, reply⟩, member, rfl⟩ := List.mem_map.mp following
            have allowed := request_prefix (call.kind.nondestructive call.directory.directory.fd) call.active
              (operation, reply) (List.mem_append_left _ member)
            cases reply <;> exact allowed
      · rw [resources.guards] at guardMember
        exact adapter_namespace_prefix_nondestructive adapter (.inl opening) event guardMember

structure RunFileRootAt {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed}
    {call : RunFileCall adapter.occurrence.logicalBefore request} {position : Nat}
    (resources : RunFileResources adapter call position) (family : Family) (catalogue : Catalogue runtime all) where
  root : PrivateRoot
  birth : RootBirth runtime all root
  member : Sigma.mk root birth ∈ catalogue
  owner : root.actor = actor
  directory : resources.source.earlier.source.opening.handle.object = root.object
  container : resources.source.root.use.parent.object = root.parent
  name : call.directory.name = root.name
  bound : tick.before.shared.entries resources.source.root.use.parent.object call.directory.name = some root.object
  privateRoot : family root.object = some root.object
  publicParent : family resources.source.root.use.parent.object = none
  owned : catalogue.Owns actor root.object
  sourceBirth : birth.tick = resources.source.root.birthTick
  sourceOwner : root.actor = resources.source.root.use.actor

-- §FS-host-boundary.ownership: This actual validator/archive call's run
-- is the SAME registered birth with its still-bound name and private
-- family; no current-root or future writer acknowledgement is assumed.
theorem actual_run_file_root {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (mounts : MountContract kernel initial.allocated)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {native : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before native)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ tick :: trailing)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (present : tick.before.actors actor = some engine)
    {adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed}
    {call : RunFileCall adapter.occurrence.logicalBefore request}
    (resources : RunFileResources adapter call processed.length) (opening : request.op = .openAt) :
    Nonempty (RunFileRootAt resources prior.current.source.custody.caps.family prior.current.source.custody.catalogue) := by
  let source := resources.source
  let earlier := source.earlier.source
  have earlierAt : processed[earlier.position]? = some earlier.tick := by
    simpa only [whole, List.getElem?_append_left earlier.earlier] using earlier.selected
  have earlierAction : earlier.tick.action.eventFor earlier.inputActor =
      some (Program.filesystemPrefixEvent (source.opening.request, some source.opening.reply)) := by
    simp only [earlier.action, ActorAction.eventFor, ↓reduceIte, Program.filesystemPrefixEvent]
  obtain ⟨root, birth, current, ordinal, member, owner, openedHandle, openedLive, openedObject, openedRaw⟩ :=
    source.root.opened_root descriptors lifetimes mounts journal prior whole earlierAt earlier.present
      earlierAction source.opening.opening source.opening.recognized
  have realLive : earlier.tick.after.shared.handles call.directory.directory.fd = some earlier.opening.handle := by
    rw [← earlier.shared_handles]
    exact earlier.opening.live
  have sameOpened : openedHandle = earlier.opening.handle := Option.some.inj (openedLive.symm.trans realLive)
  have directory : earlier.opening.handle.object = root.object :=
    (congrArg Handle.object sameOpened).symm.trans openedObject
  have ownerUse : root.actor = source.root.use.actor := owner.trans source.root.sameActor.symm
  have currentPresent : tick.before.actors source.root.use.actor = some engine := by
    rw [source.root.sameActor, resources.sameActor]
    exact present
  obtain ⟨bound, privateRoot, publicParent, owned, parent, name⟩ := prior.registered_birth_current lifetimes
    source.root.use birth current ownerUse member currentPresent (resources.source_nondestructive opening)
  have actualName : call.directory.name = root.name :=
    (congrArg Request.left source.opening.operation).symm.trans (source.root.sameName.trans name.symm)
  exact ⟨{
    root
    birth
    member
    owner := owner.trans resources.sameActor
    directory
    container := parent.symm
    name := actualName
    bound := by rw [← parent, actualName]; exact bound
    privateRoot
    publicParent := by rw [← parent]; exact publicParent
    owned := Eq.mp (congrArg (fun who => prior.current.source.custody.catalogue.Owns who root.object)
      (source.root.sameActor.trans resources.sameActor)) owned
    sourceBirth := current
    sourceOwner := ownerUse }⟩

end LeanCage.Host.Kernel
