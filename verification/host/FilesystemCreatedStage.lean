import FilesystemCreatedOpening
import FilesystemPublicationHandles

namespace LeanCage.Host.Kernel
open Filesystem

private theorem returned_pending {α : Type} {program : Filesystem.Program α}
    {events first last : List (Request × Reply)} {request : Request} {reply : Reply} {value : α}
    (source : Returns program events value) (trace : events = first ++ (request, reply) :: last) :
    Prefix program (Publication.completed first ++ [(request, none)]) := by
  subst events
  induction first generalizing program with
  | nil => cases source with | call request next reply tail value rest => exact .lost request next
  | cons event first ih => cases source with | call request next reply tail value rest => exact .returned _ _ _ _ (ih rest)

private theorem prefix_bind_return {α β : Type} {program : Filesystem.Program α}
    {next : α → Filesystem.Program β} {first : List (Request × Reply)} {last : List (Request × Option Reply)}
    {value : α} (source : Returns program first value) (tail : Prefix (next value) last) :
    Prefix (program.bind next) (Publication.completed first ++ last) := by
  induction source with
  | pure => exact tail
  | call request continuation reply events value rest ih => exact .returned _ _ _ _ (ih tail)

private theorem prefix_bind_left {α β : Type} {program : Filesystem.Program α}
    {next : α → Filesystem.Program β} {events : List (Request × Option Reply)}
    (source : Prefix program events) : Prefix (program.bind next) events := by
  induction source with
  | empty => exact .empty _
  | lost request continuation => exact .lost request (fun reply => (continuation reply).bind next)
  | returned request continuation reply tail rest ih => exact .returned _ _ _ _ ih

structure StageOpening (parent : Directories.Parent) (events : List (Request × Reply)) (stage : Directories.Fresh) where
  before : List (Request × Reply)
  after : List (Request × Reply)
  request : Request
  reply : Reply
  trace : events = before ++ (request, reply) :: after
  opening : request.op = .openAt
  recognized : descriptor reply = some stage.directory.fd
  reserved : PrivateNames.reservedBytes request.left = true
  active : Prefix (Directories.fresh parent) (Publication.completed before ++ [(request, none)])
  inspection : ∃ information, after = [({op := .stat, first := stage.directory.fd}, information)]
  operation : request = {
    op := .openAt, first := stage.container.fd, second := directoryFlags, left := stage.name }

-- §FS-host-boundary.publication: The completed stage creation selects its own original
-- child open, with the same raw name, fd and actual source replies.
theorem created_stage_opening (parent : Directories.Parent) {events : List (Request × Reply)} {stage : Directories.Fresh}
    (source : Returns (Directories.fresh parent) events (.ok stage)) : Nonempty (StageOpening parent events stage) := by
  obtain ⟨aliasEvents, creating, shape, alias, created⟩ := Publication.fresh_source parent source
  obtain ⟨random, randomEvents, made, openingEvents, createTrace, randomized, randomSize, childName,
    component, madeZero, madeEmpty, opened, childUid, childMode⟩ := created
  obtain ⟨reply, information, openingTrace, recognized, parsed, trusted⟩ := opened
  let request : Request := {
    op := .openAt
    first := stage.container.fd
    second := directoryFlags
    left := stage.name }
  let before := aliasEvents ++ randomEvents ++ [({
    op := .mkdirAt, first := stage.container.fd, second := 448, left := stage.name}, made)]
  let after : List (Request × Reply) := [({op := .stat, first := stage.directory.fd}, information)]
  have trace : events = before ++ (request, reply) :: after := by
    rw [shape, createTrace, openingTrace]
    simp only [before, after, request, List.append_assoc,
      List.cons_append, List.nil_append]
  exact ⟨⟨before, after, request, reply, trace, rfl, recognized,
    (by change PrivateNames.reservedBytes stage.name = true; rw [childName]; exact private_prefix_reserved _),
    returned_pending source trace, ⟨information, rfl⟩, rfl⟩⟩

-- §FS-host-boundary.lookup: The actual successful stage producer retains
-- the same opening and its precise parsed/trusted stat acknowledgement.
theorem created_stage_opening_observed (parent : Directories.Parent) {events : List (Request × Reply)} {stage : Directories.Fresh}
    (source : Returns (Directories.fresh parent) events (.ok stage)) : ∃ opening : StageOpening parent events stage, ∃ information,
      opening.after = [({op := .stat, first := stage.directory.fd}, information)] ∧
      parseStat information = some stage.directory.information ∧
      Directories.trusted parent.uid stage.directory.information = true := by
  obtain ⟨aliasEvents, creating, shape, alias, created⟩ := Publication.fresh_source parent source
  obtain ⟨random, randomEvents, made, openingEvents, createTrace, randomized, randomSize, childName,
    component, madeZero, madeEmpty, opened, childUid, childMode⟩ := created
  obtain ⟨reply, information, openingTrace, recognized, parsed, trusted⟩ := opened
  let request : Request := {
    op := .openAt
    first := stage.container.fd
    second := directoryFlags
    left := stage.name }
  let before := aliasEvents ++ randomEvents ++ [({
    op := .mkdirAt, first := stage.container.fd, second := 448, left := stage.name}, made)]
  let after : List (Request × Reply) := [({op := .stat, first := stage.directory.fd}, information)]
  have trace : events = before ++ (request, reply) :: after := by
    rw [shape, createTrace, openingTrace]
    simp only [before, after, request, List.append_assoc,
      List.cons_append, List.nil_append]
  exact ⟨⟨before, after, request, reply, trace, rfl, recognized,
    (by change PrivateNames.reservedBytes stage.name = true; rw [childName]; exact private_prefix_reserved _),
    returned_pending source trace, ⟨information, rfl⟩, rfl⟩, information, rfl, parsed, trusted⟩

private theorem attempt_staging_prefix (bundle : Validation.Bundle) (input : Publication.Input)
    (stdoutHash stderrHash : ByteArray) {target : ByteArray} (selection : PublicationCreation.Selected target)
    {inside : List (Request × Option Reply)} (active : Prefix (Directories.fresh selection.parent) inside) :
    Prefix (Publication.attempt bundle input target stdoutHash stderrHash)
      (Publication.completed (selection.displaying ++ selection.selecting) ++ inside) := by
  unfold Publication.attempt
  simp only [Publication.completed, List.map_append, List.append_assoc]
  apply prefix_bind_return selection.displayed
  apply prefix_bind_return selection.selected
  exact prefix_bind_left active

private theorem publish_staging_prefix (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (input effective : Publication.Input) (result : Result (ByteArray × ByteArray))
    (stdoutHash stderrHash : ByteArray) (target : ByteArray)
    {identifying selecting : List (Request × Reply)}
    (identify : Returns input.outcome.identify identifying result)
    (identity : Publication.Identification input result effective stdoutHash stderrHash)
    (chosen : Returns (Publication.destination request bundle effective.outcome.requestId) selecting (.ok target))
    {inside : List (Request × Option Reply)}
    (active : Prefix (Publication.attempt bundle effective target stdoutHash stderrHash) inside) :
    Prefix (Publication.publish request bundle input)
      (Publication.completed identifying ++ Publication.completed selecting ++ inside) := by
  unfold Publication.publish
  rw [List.append_assoc]
  rcases identity with ⟨rfl, rfl⟩ | ⟨error, rfl, rfl, rfl, rfl⟩
  all_goals
    apply prefix_bind_return identify
    apply prefix_bind_return chosen
    exact prefix_bind_left active

-- §FS-host-boundary.publication: Reconstruct the earlier source stage call from the SAME
-- commit's completed producer chain, including error identification and selected public parent.
def HostCommitCall.staging_opening_source {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : HostCommitCall before request observed) {inside : List (Request × Option Reply)} {opening : Request}
    (active : Prefix (Directories.fresh source.source.commit.parent) (inside ++ [(opening, none)])) :
    StagingOpeningCall (source.selectingContext ++ source.source.commit.selecting.map Program.filesystemEvent ++
      inside.map Program.filesystemPrefixEvent) opening := by
  let selection : PublicationCreation.Selected source.source.target := {
    display := source.source.commit.display
    displaying := source.source.commit.displaying
    displayed := source.source.commit.displayed
    parent := source.source.commit.parent
    selecting := source.source.commit.selecting
    selected := source.source.commit.selected }
  let attemptBefore := Publication.completed (selection.displaying ++ selection.selecting) ++ inside
  let allBefore := Publication.completed source.source.identifying ++ Publication.completed source.source.selecting ++ attemptBefore
  let outside := source.invocation.packet.events ++ source.invocation.authenticated.events ++ source.invocation.run.context.events
  have attempted := attempt_staging_prefix source.invocation.authenticated.bundle source.source.effective
    source.source.stdoutHash source.source.stderrHash selection active
  have published := publish_staging_prefix source.invocation.effective source.invocation.authenticated.bundle
    source.invocation.run.context.dispatched.input source.source.effective source.source.identified
    source.source.stdoutHash source.source.stderrHash source.source.target source.source.identify source.source.identity
    source.source.select attempted
  have published : Prefix (Publication.publish source.invocation.effective source.invocation.authenticated.bundle
      source.invocation.run.context.dispatched.input) (allBefore ++ [(opening, none)]) := by
    simpa only [allBefore, attemptBefore, List.append_assoc] using published
  let run : RunPublicationCall source.invocation.effective source.invocation.authenticated.bundle source.invocation.duration
      (source.invocation.run.context.events ++ allBefore.map Program.filesystemPrefixEvent) (.lost (.filesystem opening)) := {
    context := source.invocation.run.context
    inside := allBefore.map Program.filesystemPrefixEvent
    active := by
      simpa only [List.map_append, List.map_cons, List.map_nil, Program.filesystemPrefixEvent] using
        Program.lift_filesystem_prefix published
    trace := rfl }
  let invocation : EntryPublicationCall (outside ++ allBefore.map Program.filesystemPrefixEvent) (.lost (.filesystem opening)) := {
    packet := source.invocation.packet
    original := source.invocation.original
    effective := source.invocation.effective
    duration := source.invocation.duration
    accepted := source.invocation.accepted
    invocation := source.invocation.invocation
    authenticated := source.invocation.authenticated
    command := source.invocation.command
    runBefore := source.invocation.run.context.events ++ allBefore.map Program.filesystemPrefixEvent
    run
    trace := by simp only [outside, List.append_assoc] }
  have exactBefore : source.selectingContext ++ source.source.commit.selecting.map Program.filesystemEvent ++
      inside.map Program.filesystemPrefixEvent = outside ++ allBefore.map Program.filesystemPrefixEvent := by
    simp only [HostCommitCall.selectingContext, outside, allBefore, attemptBefore, selection,
      List.map_append, completed_filesystem_events, List.append_assoc]
  apply Eq.mpr (congrArg (fun context => StagingOpeningCall context opening) exactBefore)
  exact {
    invocation
    earlier := allBefore
    source := {
      identified := source.source.identified
      effective := source.source.effective
      stdoutHash := source.source.stdoutHash
      stderrHash := source.source.stderrHash
      target := source.source.target
      identifying := source.source.identifying
      selecting := source.source.selecting
      inside := attemptBefore
      identify := source.source.identify
      identity := source.source.identity
      select := source.source.select
      site := .staging selection inside active rfl
      trace := rfl }
    projection := rfl
    selection
    inside
    active
    trace := rfl
    classified := rfl }

structure CreatedStageRoot {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (all : List (ActorTick runtime)) (stage : Directories.Fresh) (limit : Nat) where
  context : List Program.Event
  request : Request
  reply : Reply
  earlier : EarlierOpen runtime initial all context request reply stage.directory.fd limit
  source : RootOpenReceipt runtime initial all earlier.tick earlier.inputActor earlier.input request earlier.position

structure CreatedStageContinuation {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (all : List (ActorTick runtime)) {before : List Program.Event} {request : Request} {observed : Option Reply}
    (call : HostCommitCall before request observed) (limit : Nat) (current : World) where
  opening : StageOpening call.source.commit.parent call.source.commit.creating call.source.commit.stage
  earlier : EarlierOpenContinuation runtime initial all
    (call.selectingContext ++ call.source.commit.selecting.map Program.filesystemEvent ++ opening.before.map Program.filesystemEvent)
    (opening.after.map Program.filesystemEvent ++ call.source.commit.preparing.map Program.filesystemEvent)
    opening.request opening.reply call.source.commit.stage.directory.fd limit current
  root : RootOpenReceipt runtime initial all earlier.source.tick earlier.source.inputActor earlier.source.input
    opening.request earlier.source.position

-- §FS-host-boundary.publication: The selected commit supplies the actual earlier stage
-- source cut and descriptor, rather than a separately chosen successful staging execution.
theorem primitive_created_stage_continuation {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (source : HostCommitCall adapter.occurrence.logicalBefore request none) :
    ∃ result : CreatedStageContinuation runtime initial all source position (tick.before.project engine),
      result.earlier.source.inputActor = actor ∧
      result.earlier.guards = adapter.occurrence.inside.map Program.filesystemPrefixEvent ∧
      engine.events = result.earlier.source.input.events ++ .returned (.filesystem result.opening.request) result.opening.reply ::
        (result.earlier.post.map Program.filesystemEvent ++ result.earlier.remaining ++ result.earlier.guards) := by
  obtain ⟨opening⟩ := created_stage_opening source.source.commit.parent source.source.commit.created
  let before := source.selectingContext ++ source.source.commit.selecting.map Program.filesystemEvent ++
    opening.before.map Program.filesystemEvent
  let after := opening.after.map Program.filesystemEvent ++ source.source.commit.preparing.map Program.filesystemEvent
  have trace : adapter.occurrence.logicalBefore = before ++
      .returned (.filesystem opening.request) opening.reply :: after := by
    apply (commit_parent_trace source).trans
    have mapped := congrArg (fun events : List (Request × Reply) =>
      source.selectingContext ++ source.source.commit.selecting.map Program.filesystemEvent ++
        (events ++ source.source.commit.preparing).map Program.filesystemEvent) opening.trace
    exact mapped.trans (by simp only [before, after, List.map_append, List.map_cons, Program.filesystemEvent,
      List.append_assoc, List.cons_append])
  obtain ⟨continued, sameActor, sameGuards, eventTrace⟩ := primitive_earlier_open_continuation descriptors lifetimes references environment journal selected
    present adapter trace opening.opening opening.recognized
  let earlier := continued.source
  have earlierSource := source.staging_opening_source opening.active
  have sameBefore : before = source.selectingContext ++ source.source.commit.selecting.map Program.filesystemEvent ++
      (Publication.completed opening.before).map Program.filesystemPrefixEvent := by simp only [before, completed_filesystem_events]
  have call : StagingOpeningCall earlier.adapter.occurrence.logicalBefore opening.request :=
    Eq.mpr (congrArg (fun context => StagingOpeningCall context opening.request)
      (earlier.logicalBefore.trans sameBefore)) earlierSource
  obtain ⟨receipt⟩ := staging_private_reopen_receipt descriptors aliases lifetimes references environment journal
    earlier.selected earlier.present earlier.adapter call opening.opening opening.reserved
  exact ⟨⟨opening, continued, receipt⟩, sameActor, sameGuards, eventTrace⟩

-- §AR-host-boundary.interfaces: Preserve the original earlier-open/source receipt projection.
theorem primitive_created_stage_root {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (source : HostCommitCall adapter.occurrence.logicalBefore request none) :
    ∃ result : CreatedStageRoot runtime initial all source.source.commit.stage position,
      result.earlier.inputActor = actor := by
  obtain ⟨result, actor, guards, trace⟩ := primitive_created_stage_continuation descriptors aliases lifetimes references
    environment journal selected present adapter source
  exact ⟨⟨_, result.opening.request, result.opening.reply, result.earlier.source, result.root⟩, actor⟩

end LeanCage.Host.Kernel
