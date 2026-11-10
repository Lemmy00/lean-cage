import FilesystemCreatedStage
import FilesystemPublicationCleanupSource
import FilesystemRunCustody

namespace LeanCage.Host.Kernel
open Filesystem
universe u

private theorem returned_pending {α : Type} {program : Filesystem.Program α}
    {events first last : List (Request × Reply)} {request : Request} {reply : Reply} {value : α}
    (source : Returns program events value) (trace : events = first ++ (request, reply) :: last) :
    Prefix program (Publication.completed first ++ [(request, none)]) := by
  subst events
  induction first generalizing program with
  | nil => cases source with | call _ _ _ _ _ rest => exact .lost _ _
  | cons event first ih => cases source with | call _ _ _ _ _ rest => exact .returned _ _ _ _ (ih rest)


structure CleanupStageContinuation {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (all : List (ActorTick runtime)) {before : List Program.Event} {request : Request}
    (call : PublicationCleanup.Host before request) (limit : Nat) (current : World) where
  opening : StageOpening call.source.attempt.context.parent call.source.attempt.context.creating call.source.attempt.context.stage
  earlier : EarlierOpenContinuation runtime initial all
    (call.selectingContext ++ call.source.attempt.context.selecting.map Program.filesystemEvent ++
      opening.before.map Program.filesystemEvent)
    (opening.after.map Program.filesystemEvent ++ call.source.attempt.preparing.map Program.filesystemEvent ++
      call.source.attempt.inside.map Program.filesystemPrefixEvent)
    opening.request opening.reply call.source.attempt.context.stage.directory.fd limit current
  root : RootOpenReceipt runtime initial all earlier.source.tick earlier.source.inputActor earlier.source.input
    opening.request earlier.source.position
  informationReply : Reply
  inspection : opening.after = [({op := .stat, first := call.source.attempt.context.stage.directory.fd}, informationReply)]
  parsed : parseStat informationReply = some call.source.attempt.context.stage.directory.information
  trusted : Directories.trusted call.source.attempt.context.parent.uid call.source.attempt.context.stage.directory.information = true

-- §FS-host-boundary.publication: Failed preparation retains the original
-- stage's exact source-open/mkdir cut. This selected cleanup may interrupt;
-- no successful preparation, commit or cleanup result is required.
theorem primitive_cleanup_stage_continuation {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (call : PublicationCleanup.Host adapter.occurrence.logicalBefore request) :
    ∃ result : CleanupStageContinuation runtime initial all call position (tick.before.project engine),
      result.earlier.source.inputActor = actor ∧
      result.earlier.guards = adapter.occurrence.inside.map Program.filesystemPrefixEvent ∧
      engine.events = result.earlier.source.input.events ++ .returned (.filesystem result.opening.request) result.opening.reply ::
        (result.earlier.post.map Program.filesystemEvent ++ result.earlier.remaining ++ result.earlier.guards) := by
  obtain ⟨opening, informationReply, inspection, parsed, trusted⟩ :=
    created_stage_opening_observed call.source.attempt.context.parent call.source.attempt.context.created
  let before := call.selectingContext ++ call.source.attempt.context.selecting.map Program.filesystemEvent ++
    opening.before.map Program.filesystemEvent
  let after := opening.after.map Program.filesystemEvent ++ call.source.attempt.preparing.map Program.filesystemEvent ++
    call.source.attempt.inside.map Program.filesystemPrefixEvent
  have trace : adapter.occurrence.logicalBefore = before ++ .returned (.filesystem opening.request) opening.reply :: after := by
    apply call.cleanup_trace.trans
    have mapped := congrArg (fun events : List (Request × Reply) =>
      call.selectingContext ++ call.source.attempt.context.selecting.map Program.filesystemEvent ++
        (events ++ call.source.attempt.preparing).map Program.filesystemEvent ++
          call.source.attempt.inside.map Program.filesystemPrefixEvent) opening.trace
    exact mapped.trans (by simp only [before, after, List.map_append, List.map_cons, Program.filesystemEvent,
      List.append_assoc, List.cons_append])
  obtain ⟨continued, sameActor, guards, eventTrace⟩ := primitive_earlier_open_continuation descriptors lifetimes references
    environment journal selected present adapter trace opening.opening opening.recognized
  let earlier := continued.source
  have earlierSource := call.staging_opening_source opening.active
  have sameBefore : before = call.selectingContext ++ call.source.attempt.context.selecting.map Program.filesystemEvent ++
      (Publication.completed opening.before).map Program.filesystemPrefixEvent := by simp only [before, completed_filesystem_events]
  have openingCall : StagingOpeningCall earlier.adapter.occurrence.logicalBefore opening.request :=
    Eq.mpr (congrArg (fun context => StagingOpeningCall context opening.request)
      (earlier.logicalBefore.trans sameBefore)) earlierSource
  obtain ⟨receipt⟩ := staging_private_reopen_receipt descriptors aliases lifetimes references environment journal
    earlier.selected earlier.present earlier.adapter openingCall opening.opening opening.reserved
  exact ⟨⟨opening, continued, receipt, informationReply, inspection, parsed, trusted⟩, sameActor, guards, eventTrace⟩

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

private theorem drop_append_allowed {α : Type u} {first last : List α} (count : Nat) (allowed : α → Prop)
    (leading : ∀ event ∈ first.drop count, allowed event) (trailing : ∀ event ∈ last, allowed event) :
    ∀ event ∈ (first ++ last).drop count, allowed event := by
  intro event member
  rw [List.drop_append] at member
  rcases List.mem_append.mp member with member | member
  · exact leading event member
  · exact trailing event (List.mem_of_mem_drop member)

private theorem nondestructive_no_publication {event : Program.Event} (quiet : NondestructiveEvent event) :
    RequestEvent (fun request => request.op ≠ .renameNew) event := by
  cases event with
  | returned effect reply => cases effect <;> first | exact fun moving => quiet (.inr moving) | exact True.intro
  | lost effect => cases effect <;> first | exact fun moving => quiet (.inr moving) | exact True.intro

-- §FS-host-boundary.ownership: Earlier cleanup may remove stage descendants,
-- but cannot have published this same stage. Every raw guard and cleanup
-- operation remains in the real source suffix from its actual mkdir.
theorem CleanupStageContinuation.no_publication {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {before : List Program.Event} {request : Request}
    {call : PublicationCleanup.Host before request} {limit : Nat} {current : World}
    (source : CleanupStageContinuation runtime initial all call limit current)
    (events : List Program.Event)
    (trace : events = source.earlier.source.input.events ++ .returned (.filesystem source.opening.request) source.opening.reply ::
      (source.earlier.post.map Program.filesystemEvent ++ source.earlier.remaining ++ source.earlier.guards))
    (guarded : ∀ event ∈ source.earlier.guards, NondestructiveEvent event) :
    ∀ event ∈ events.drop (source.root.use.engine.events.length + 1),
      RequestEvent (fun request => request.op ≠ .renameNew) event := by
  apply Eq.mpr (congrArg (fun actualEvents => ∀ event ∈ actualEvents.drop (source.root.use.engine.events.length + 1),
    RequestEvent (fun request => request.op ≠ .renameNew) event) trace)
  apply drop_append_allowed
  · intro event member
    exact nondestructive_no_publication (passive_event_nondestructive (source.root.probes event member))
  · intro event member
    rcases List.mem_cons.mp member with rfl | member
    · change source.opening.request.op ≠ .renameNew
      rw [source.opening.opening]
      decide
    · rcases List.mem_append.mp member with member | guardMember
      · rcases List.mem_append.mp member with postMember | remainingMember
        · obtain ⟨⟨operation, reply⟩, occurs, rfl⟩ := List.mem_map.mp postMember
          exact namespace_passive_no_rename _ (source.earlier.passive (operation, reply) occurs)
        · apply chunks_no_publication source.earlier.chunks ?_ event remainingMember
          intro candidate occurs
          rcases List.mem_append.mp occurs with first | last
          · rcases List.mem_append.mp first with inspected | prepared
            · obtain ⟨information, shape⟩ := source.opening.inspection
              have same : candidate = .returned (.filesystem {
                  op := .stat, first := call.source.attempt.context.stage.directory.fd}) information := by
                simpa only [shape, List.map_cons, List.map_nil, List.mem_singleton, Program.filesystemEvent] using inspected
              subst candidate
              change Op.stat ≠ Op.renameNew
              decide
            · obtain ⟨⟨operation, reply⟩, member, rfl⟩ := List.mem_map.mp prepared
              have allowed := requests_returned (publication_prepare_nondestructive _ _ _ _ _ _ _) call.source.attempt.prepared
                (operation, reply) member
              exact fun moving => allowed (.inr moving)
          · obtain ⟨⟨operation, reply⟩, member, rfl⟩ := List.mem_map.mp last
            have allowed := Publication.safe_prefix (Publication.cleanup_safe _ _ _) call.source.attempt.active
              (operation, reply) (by simp [member])
            cases reply <;> exact Publication.safe_no_rename allowed
      · have quiet := guarded event guardMember
        exact nondestructive_no_publication quiet

structure CleanupStageRootAt {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    {initial : World} {all : List (ActorTick runtime)} {before : List Program.Event} {request : Request}
    {call : PublicationCleanup.Host before request} {limit : Nat} {current : World}
    (source : CleanupStageContinuation runtime initial all call limit current)
    (actor : ActorId) (family : Family) (catalogue : Catalogue runtime all) where
  root : PrivateRoot
  birth : RootBirth runtime all root
  sourceBirth : birth.tick = source.root.birthTick
  sourcePosition : birth.position = source.root.birthPosition
  member : Sigma.mk root birth ∈ catalogue
  owner : root.actor = actor
  directory : source.earlier.source.opening.handle.object = root.object
  container : source.root.use.parent.object = root.parent
  name : call.source.attempt.context.stage.name = root.name
  privateRoot : family root.object = some root.object
  owned : catalogue.Owns actor root.object

-- §FS-host-boundary.ownership: The cleanup's actual original stage open
-- selects its source-registered lifetime and current private scope, even
-- after earlier child removals. No live stage FD or current root is assumed.
theorem actual_cleanup_stage_root {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {call : PublicationCleanup.Host adapter.occurrence.logicalBefore request}
    (source : CleanupStageContinuation runtime initial all call processed.length (tick.before.project engine))
    (sameActor : source.earlier.source.inputActor = actor)
    (guards : source.earlier.guards = adapter.occurrence.inside.map Program.filesystemPrefixEvent)
    (eventTrace : engine.events = source.earlier.source.input.events ++
      .returned (.filesystem source.opening.request) source.opening.reply ::
        (source.earlier.post.map Program.filesystemEvent ++ source.earlier.remaining ++ source.earlier.guards))
    (unlink : request.op = .unlinkAt) :
    Nonempty (CleanupStageRootAt runtime source actor state.custody.current.source.custody.caps.family
      state.custody.current.source.custody.catalogue) := by
  let earlier := source.earlier.source
  have earlierAt : processed[earlier.position]? = some earlier.tick := by
    simpa only [whole, List.getElem?_append_left earlier.earlier] using earlier.selected
  have earlierAction : earlier.tick.action.eventFor earlier.inputActor =
      some (Program.filesystemPrefixEvent (source.opening.request, some source.opening.reply)) := by
    simp only [earlier.action, ActorAction.eventFor, ↓reduceIte, Program.filesystemPrefixEvent]
  have beforeBirth : source.root.birthPosition < processed.length := Nat.lt_trans source.root.earlier earlier.earlier
  have birthAt : processed[source.root.birthPosition]? = some source.root.birthTick := by
    simpa only [whole, List.getElem?_append_left beforeBirth] using source.root.birthAt
  obtain ⟨root, birth, current, ordinal, member, owner, parent, name, handle, live, identity, raw⟩ :=
    registered_root_handle_at descriptors lifetimes mounts journal state.custody birthAt source.root.use earlierAt
      source.root.earlier (by rw [source.root.sameActor]; exact earlier.present)
      (by rw [source.root.sameActor]; exact earlierAction) source.opening.opening source.root.flags
      source.root.sameName source.root.reference source.opening.recognized
      (fun event member => passive_event_nondestructive (source.root.probes event member))
  have actualLive : earlier.tick.after.shared.handles call.source.attempt.context.stage.directory.fd = some earlier.opening.handle := by
    rw [← earlier.shared_handles]
    exact earlier.opening.live
  have same : handle = earlier.opening.handle := Option.some.inj (live.symm.trans actualLive)
  have directory : earlier.opening.handle.object = root.object := (congrArg Handle.object same).symm.trans identity
  have currentPresent : tick.before.actors source.root.use.actor = some engine := by
    rw [source.root.sameActor, sameActor]
    exact present
  have noPublication := source.no_publication engine.events eventTrace (by
    rw [guards]
    exact adapter_namespace_prefix_nondestructive adapter (.inr (.inr (.inl unlink))))
  have privateRoot := state.private_label_at_source lifetimes member source.root.use current owner currentPresent noPublication
  refine ⟨{
    root
    birth
    sourceBirth := current
    sourcePosition := ordinal
    member
    owner := owner.trans (source.root.sameActor.trans sameActor)
    directory
    container := parent.symm
    name := ?_
    privateRoot
    owned := ⟨Sigma.mk root birth, member, owner.trans (source.root.sameActor.trans sameActor), rfl⟩ }⟩
  exact (congrArg Request.left source.opening.operation).symm.trans (source.root.sameName.trans name.symm)

end LeanCage.Host.Kernel
