import FilesystemRunCleanupReference
import FilesystemPublicationProgress

namespace LeanCage.Host.Kernel
open Filesystem
universe u

private theorem chunks_no_publication {logical raw : List Program.Event}
    (source : PrimitiveFilesystem.Chunks logical raw)
    (allowed : ∀ event ∈ logical, RequestEvent (fun request => request.op ≠ .renameNew) event) :
    ∀ event ∈ raw, RequestEvent (fun request => request.op ≠ .renameNew) event := by
  induction source with
  | nil => intro event impossible; cases impossible
  | cons effect reply inside logical raw adapter remaining ih =>
    intro event member
    rcases List.mem_append.mp member with first | last
    · have head := allowed (.returned effect reply) (by simp)
      cases effect with
      | filesystem request =>
        obtain ⟨events, returned, trace⟩ := Program.lift_filesystem_source (guardedCall request) adapter
        rw [trace] at first
        obtain ⟨⟨operation, answer⟩, occurs, rfl⟩ := List.mem_map.mp first
        have role := profile_returns (guarded_call_profile request) returned (operation, answer) occurs
        change operation.op ≠ .renameNew
        rcases role with same | magic | flags | close
        · change operation = request at same
          rw [same]
          exact head
        · rw [magic]; decide
        · rw [flags]; decide
        · rw [close]; decide
      | spawn | read | wait | terminate | tryWait | descriptor =>
        have single := PrimitiveFilesystem.effect_returns_singleton _ adapter
        rw [single] at first
        have same := List.mem_singleton.mp first
        subst event
        exact True.intro
    · exact ih (by intro event occurs; exact allowed event (List.mem_cons_of_mem _ occurs)) event last

private theorem nondestructive_no_publication {event : Program.Event} (source : NondestructiveEvent event) :
    RequestEvent (fun request => request.op ≠ .renameNew) event := by
  cases event with
  | returned effect reply =>
    cases effect with
    | filesystem request => exact fun moving => source (.inr moving)
    | spawn | read | wait | terminate | tryWait | descriptor => exact True.intro
  | lost effect =>
    cases effect with
    | filesystem request => exact fun moving => source (.inr moving)
    | spawn | read | wait | terminate | tryWait | descriptor => exact True.intro

private theorem drop_append_allowed {α : Type u} {first last : List α} (count : Nat) (allowed : α → Prop)
    (leading : ∀ event ∈ first.drop count, allowed event) (trailing : ∀ event ∈ last, allowed event) :
    ∀ event ∈ (first ++ last).drop count, allowed event := by
  intro event member
  rw [List.drop_append] at member
  rcases List.mem_append.mp member with member | member
  · exact leading event member
  · exact trailing event (List.mem_of_mem_drop member)

-- §FS-host-boundary.ownership: Actual run cleanup may unlink contents but
-- cannot have published this run first. The proof follows the SAME source
-- birth/open/work/cleanup transcript and every raw adapter chunk.
theorem RunCleanupParent.source_no_publication {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {actor : ActorId} {events outside : List Program.Event}
    {created : List (Request × Reply)} {run : RunDirectory.Owned} {work : List Program.Event}
    {inside : List (Request × Option Reply)} {request : Request} {guardOrdinal limit : Nat} {current : World}
    (source : RunCleanupParent runtime initial all actor events outside created run work inside request guardOrdinal limit current) :
    ∀ event ∈ events.drop (source.allocation.root.use.engine.events.length + 1),
      RequestEvent (fun request => request.op ≠ .renameNew) event := by
  apply Eq.mpr (congrArg (fun actualEvents : List Program.Event =>
    ∀ event ∈ actualEvents.drop (source.allocation.root.use.engine.events.length + 1),
      RequestEvent (fun request => request.op ≠ .renameNew) event) source.eventTrace)
  apply drop_append_allowed
  · intro event member
    exact nondestructive_no_publication (passive_event_nondestructive (source.allocation.root.probes event member))
  · intro event member
    rcases List.mem_cons.mp member with rfl | member
    · change source.allocation.opening.request.op ≠ .renameNew
      rw [source.allocation.opening.opening]
      decide
    · rcases List.mem_append.mp member with member | guardMember
      · rcases List.mem_append.mp member with postMember | remainingMember
        · obtain ⟨⟨operation, reply⟩, occurs, rfl⟩ := List.mem_map.mp postMember
          exact namespace_passive_no_rename operation (source.allocation.earlier.passive (operation, reply) occurs)
        · apply chunks_no_publication source.allocation.earlier.chunks ?_ event remainingMember
          intro candidate occurs
          rcases List.mem_append.mp occurs with creating | following
          · obtain ⟨⟨operation, reply⟩, member, rfl⟩ := List.mem_map.mp creating
            exact fun moving => source.allocation.opening.nondestructive (operation, reply) member (.inr moving)
          · exact source.noPublication candidate following
      · exact nondestructive_no_publication (source.guardsQuiet event guardMember)

theorem PublicationReleaseJournal.actual {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {all : List (ActorTick runtime)} {catalogue : Catalogue runtime all}
    {before after : Population} {first final : Family} {ticks : List (ActorTick runtime)}
    (source : PublicationReleaseJournal runtime catalogue before first ticks after final) :
    ActorJournal runtime before ticks after := by
  induction source with
  | nil => exact .nil _
  | cons current tail ih => exact .cons ih

-- §FS-host-boundary.ownership: The already constructed release journal gives
-- the current private label from this exact birth and source interval. Owned
-- child unlinks are retained; no complete-helper nondestructiveness is assumed.
theorem RegisteredPublicationState.private_label_at_source {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (lifetimes : LifetimeContract runtime)
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {population : Population} {native : NativeProcesses}
    (state : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed population native)
    {root : PrivateRoot} {birth : RootBirth runtime all root}
    (member : Sigma.mk root birth ∈ state.custody.current.source.custody.catalogue)
    {birthTick : ActorTick runtime} (use : PrimitiveRootUse runtime initial all birthTick)
    (sameTick : birth.tick = birthTick) (sameOwner : root.actor = use.actor)
    {engine : EngineState} (present : population.actors use.actor = some engine)
    (quiet : ∀ event ∈ engine.events.drop (use.engine.events.length + 1),
      RequestEvent (fun request => request.op ≠ .renameNew) event) :
    state.custody.current.source.custody.caps.family root.object = some root.object := by
  obtain ⟨scope⟩ := state.releases (Sigma.mk root birth) member
  obtain ⟨born, bornPresent, appended⟩ := source_event_after birthTick use.action use.present
  have presentBorn : birth.tick.after.actors use.actor = some born := by rwa [sameTick]
  have count : born.events.length = use.engine.events.length + 1 := by
    simp only [appended, List.length_append, List.length_singleton]
  have actualSource := actor_interval_request_profile (fun request => request.op ≠ .renameNew)
    scope.release.actual presentBorn present (by rw [count]; exact quiet)
  exact scope.release.private_label_retained lifetimes state.custody.current.source.custody.valid
    ⟨Sigma.mk root birth, member, sameOwner, rfl⟩ birth.fresh.2 scope.privateRoot actualSource

structure RunCleanupRootAt {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    {initial : World} {all : List (ActorTick runtime)} {actor : ActorId} {events outside : List Program.Event}
    {created : List (Request × Reply)} {run : RunDirectory.Owned} {work : List Program.Event}
    {inside : List (Request × Option Reply)} {request : Request} {guardOrdinal limit : Nat} {current : World}
    (source : RunCleanupParent runtime initial all actor events outside created run work inside request guardOrdinal limit current)
    (family : Family) (catalogue : Catalogue runtime all) where
  root : PrivateRoot
  birth : RootBirth runtime all root
  sourceBirth : birth.tick = source.allocation.root.birthTick
  sourcePosition : birth.position = source.allocation.root.birthPosition
  member : Sigma.mk root birth ∈ catalogue
  owner : root.actor = actor
  directory : source.allocation.earlier.source.opening.handle.object = root.object
  container : source.allocation.root.use.parent.object = root.parent
  name : run.name = root.name
  privateRoot : family root.object = some root.object
  owned : catalogue.Owns actor root.object

-- §FS-host-boundary.ownership: Join the actual selected cleanup parent to its
-- recorded root lifetime/current private label and owner. Reusable inode/PID
-- observations never identify the birth, and no future cleanup ACK is required.
theorem actual_run_cleanup_root {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (mounts : MountContract kernel initial.allocated)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {native : NativeProcesses}
    (state : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before native)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ tick :: trailing)
    {actor : ActorId} {engine : EngineState} (present : tick.before.actors actor = some engine)
    {outside : List Program.Event} {created : List (Request × Reply)} {run : RunDirectory.Owned}
    {work : List Program.Event} {inside : List (Request × Option Reply)} {request : Request} {guardOrdinal : Nat}
    (source : RunCleanupParent runtime initial all actor engine.events outside created run work inside request
      guardOrdinal processed.length (tick.before.project engine)) :
    Nonempty (RunCleanupRootAt runtime source state.custody.current.source.custody.caps.family
      state.custody.current.source.custody.catalogue) := by
  let earlier := source.allocation.earlier.source
  have earlierAt : processed[earlier.position]? = some earlier.tick := by
    simpa only [whole, List.getElem?_append_left earlier.earlier] using earlier.selected
  have earlierAction : earlier.tick.action.eventFor earlier.inputActor =
      some (Program.filesystemPrefixEvent (source.allocation.opening.request, some source.allocation.opening.reply)) := by
    simp only [earlier.action, ActorAction.eventFor, ↓reduceIte, Program.filesystemPrefixEvent]
  have birthAt : processed[source.allocation.root.birthPosition]? = some source.allocation.root.birthTick := by
    have beforeBirth : source.allocation.root.birthPosition < processed.length :=
      Nat.lt_trans source.allocation.root.earlier earlier.earlier
    simpa only [whole, List.getElem?_append_left beforeBirth] using source.allocation.root.birthAt
  obtain ⟨root, birth, current, ordinal, member, owner, parent, name, handle, live, identity, raw⟩ :=
    registered_root_handle_at descriptors lifetimes mounts journal state.custody birthAt source.allocation.root.use earlierAt
      source.allocation.root.earlier (by rw [source.allocation.root.sameActor]; exact earlier.present)
      (by rw [source.allocation.root.sameActor]; exact earlierAction) source.allocation.opening.opening source.allocation.root.flags
      source.allocation.root.sameName source.allocation.root.reference source.allocation.opening.recognized
      (fun event member => passive_event_nondestructive (source.allocation.root.probes event member))
  have actualLive : earlier.tick.after.shared.handles run.directory.fd = some earlier.opening.handle := by
    rw [← earlier.shared_handles]
    exact earlier.opening.live
  have same : handle = earlier.opening.handle := Option.some.inj (live.symm.trans actualLive)
  have directory : earlier.opening.handle.object = root.object := (congrArg Handle.object same).symm.trans identity
  have currentPresent : tick.before.actors source.allocation.root.use.actor = some engine := by
    rw [source.allocation.root.sameActor, source.sameActor]
    exact present
  have privateRoot := state.private_label_at_source lifetimes member source.allocation.root.use current owner
    currentPresent source.source_no_publication
  refine ⟨{
    root
    birth
    sourceBirth := current
    sourcePosition := ordinal
    member
    owner := owner.trans (source.allocation.root.sameActor.trans source.sameActor)
    directory
    container := parent.symm
    name := ?_
    privateRoot
    owned := ⟨Sigma.mk root birth, member, owner.trans (source.allocation.root.sameActor.trans source.sameActor), rfl⟩ }⟩
  exact (congrArg Request.left source.allocation.opening.operation).symm.trans
    (source.allocation.root.sameName.trans name.symm)

end LeanCage.Host.Kernel
