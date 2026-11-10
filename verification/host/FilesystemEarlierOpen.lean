import FilesystemOpenSourceCut

namespace LeanCage.Host.Kernel
open Filesystem

structure EarlierOpen {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (all : List (ActorTick runtime)) (context : List Program.Event)
    (request : Request) (reply : Reply) (fd : UInt64) (limit : Nat) where
  position : Nat
  tick : ActorTick runtime
  input : EngineState
  output : EngineState
  selected : all[position]? = some tick
  earlier : position < limit
  inputActor : ActorId
  action : tick.action = .returned inputActor (.filesystem request) reply
  present : tick.before.actors inputActor = some input
  afterPresent : tick.after.actors inputActor = some output
  adapter : PrimitiveAdapterAt runtime initial all tick inputActor input request (some reply)
  logicalBefore : adapter.occurrence.logicalBefore = context
  opening : Lowered.RecordedOpen kernel (fun ordinal request reply =>
    SourceReturnAt runtime all inputActor ordinal Reply (.filesystem request) reply) request fd
  replyExact : opening.reply = reply
  before : opening.before = tick.before.project input
  after : opening.after = tick.after.project output

private theorem returned_output_table {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (tick : ActorTick runtime)
    {actor : ActorId} {β : Type} {effect : Effect β} {reply : β} {output : EngineState}
    (action : tick.action = .returned actor effect reply) (present : tick.after.actors actor = some output) :
    output.references = tick.after.shared.handles := by
  rcases tick with ⟨kind, before, after, actual⟩
  cases actual with
  | launch | foreign | retire | nativeRetire | lost => cases action
  | returned input alive head operation =>
    cases action
    simp only [Population.advance, Population.install, ite_eq_left] at present
    cases present
    rfl

-- §AR-host-boundary.primitives: This selected returned row installs exactly its own
-- observed descriptor table. It does not identify it with another actor's table.
theorem EarlierOpen.shared_handles {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {context : List Program.Event}
    {request : Request} {reply : Reply} {fd : UInt64} {limit : Nat}
    (source : EarlierOpen runtime initial all context request reply fd limit) :
    source.opening.after.handles = source.tick.after.shared.handles := by
  rw [source.after]
  exact returned_output_table source.tick source.action source.afterPresent

structure EarlierOpenContinuation {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (all : List (ActorTick runtime)) (context following : List Program.Event)
    (request : Request) (reply : Reply) (fd : UInt64) (limit : Nat) (current : World) where
  source : EarlierOpen runtime initial all context request reply fd limit
  post : List (Request × Reply)
  remaining : List Program.Event
  guards : List Program.Event
  chunks : PrimitiveFilesystem.Chunks following remaining
  retaining : ∀ event ∈ post, RetainsDescriptors event.1.op
  passive : ∀ event ∈ post, NamespacePassive event.1
  tail : ActorHistoryWith runtime source.inputActor (SourceReturnAt runtime all source.inputActor)
    (source.input.events.length + 1) source.opening.after
    (post.map Program.filesystemEvent ++ remaining ++ guards) current

private theorem recorded_actor {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId} {origin : OperationOrigin} {ordinal : Nat}
    {before after : World} {events : List (Request × Reply)}
    (history : RecordedHistory kernel (fun ordinal request reply =>
      origin ordinal Reply (.filesystem request) reply) ordinal before events after) :
    ActorHistoryWith runtime actor origin ordinal before (events.map Program.filesystemEvent) after := by
  induction history with
  | nil => exact .nil _ _
  | cons actual sampled tail ih => exact .returned actual sampled ih
  | environment actual tail ih => exact .environment actual ih

-- §FS-host-boundary.ownership: The earlier open comes from a selected original source
-- call in this SAME expanded transcript. Its exact global row and original source context
-- are retained; a second occurrence search cannot substitute another equal-shaped open.
theorem primitive_earlier_open_continuation {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {context following : List Program.Event} {openedRequest : Request} {openedReply : Reply} {fd : UInt64}
    (trace : adapter.occurrence.logicalBefore =
      context ++ .returned (.filesystem openedRequest) openedReply :: following)
    (opening : openedRequest.op = .openAt) (recognized : descriptor openedReply = some fd) :
    ∃ result : EarlierOpenContinuation runtime initial all context following openedRequest openedReply fd position
        (tick.before.project engine),
      result.source.inputActor = actor ∧ result.guards = adapter.occurrence.inside.map Program.filesystemPrefixEvent ∧
      engine.events = result.source.input.events ++ .returned (.filesystem openedRequest) openedReply ::
        (result.post.map Program.filesystemEvent ++ result.remaining ++ result.guards) := by
  have reached : PrimitiveFilesystem.Reached Entrypoint.run
      (context ++ .returned (.filesystem openedRequest) openedReply :: following)
      adapter.occurrence.rawBefore (.call (.filesystem adapter.occurrence.primary) adapter.occurrence.next) :=
    trace ▸ adapter.occurrence.reached
  obtain ⟨first, inside, last, next, leading, active, remaining, rawTrace⟩ :=
    PrimitiveFilesystem.reached_selected_filesystem context following openedRequest openedReply reached
  obtain ⟨events, source, insideTrace⟩ := Program.lift_filesystem_source (guardedCall openedRequest) active
  let rest := last ++ adapter.occurrence.inside.map Program.filesystemPrefixEvent
  have full : engine.events = first ++ events.map Program.filesystemEvent ++ rest := by
    rw [adapter.occurrence.trace, rawTrace, insideTrace]
    simp only [rest, List.append_assoc]
  have history := adapter.source.history
  rw [full, List.append_assoc] at history
  obtain ⟨before, firstHistory, afterFirst⟩ := actor_with_split first _ history
  obtain ⟨after, activeHistory, tail⟩ := actor_with_split (events.map Program.filesystemEvent) rest afterFirst
  have recorded : RecordedRun kernel (fun ordinal request reply =>
      SourceReturnAt runtime all actor ordinal Reply (.filesystem request) reply)
      first.length (guardedCall openedRequest) before events after openedReply :=
    ⟨source, by simpa only [Nat.zero_add] using actor_recorded_filesystem activeHistory⟩
  obtain ⟨cut, live, sameReply, postHistory⟩ := Lowered.guarded_open_recorded_cut descriptors recorded opening recognized
  let rawBefore := first ++ cut.checks.map Program.filesystemEvent
  let rawAfter := cut.following.map Program.filesystemEvent ++ rest
  have full : engine.events = rawBefore ++ .returned (.filesystem openedRequest) openedReply :: rawAfter := by
    rw [full, cut.trace, List.map_append, List.map_cons, sameReply]
    simp only [rawBefore, rawAfter, Program.filesystemEvent, List.append_assoc, List.cons_append]
  have sampled : SourceReturnAt runtime all actor rawBefore.length Reply (.filesystem openedRequest)
      openedReply cut.opening.before cut.opening.after := by
    have actual := cut.opening.sampled
    have count : cut.opening.ordinal = rawBefore.length := by
      rw [cut.count]
      simp only [rawBefore, List.length_append, List.length_map]
    rw [sameReply, count] at actual
    exact actual
  obtain ⟨earlierPosition, earlierTick, input, output, earlierAt, action, beforeAt, afterAt, count,
    beforeExact, afterExact⟩ := sampled
  have less : input.events.length < engine.events.length := by
    rw [count, full]
    simp only [List.length_append, List.length_cons]
    omega
  have earlier := source_ordinal_orders_positions journal earlierAt selected actor input engine beforeAt present less
  obtain ⟨prefixEvents, middleEvents, afterEvents, globalTrace, region⟩ :=
    journal_between_selected journal earlierAt selected (Nat.le_of_lt earlier)
  obtain ⟨extra, eventTrace⟩ := actor_journal_event_prefix region actor input engine beforeAt present
  have inputTrace : input.events = rawBefore := by
    have actual : engine.events.take rawBefore.length = input.events := by
      rw [← count, eventTrace]
      exact List.take_left
    have raw : engine.events.take rawBefore.length = rawBefore := by rw [full]; exact List.take_left
    exact actual.symm.trans raw
  let occurrence : PrimitiveFilesystem.FilesystemOccurrence Entrypoint.run input.events openedRequest (some openedReply) := {
    primary := openedRequest
    next
    logicalBefore := context
    rawBefore := first
    inside := Publication.completed cut.checks
    reached := leading
    adapter := by rw [← sameReply]; exact cut.active
    trace := by
      rw [inputTrace]
      change first ++ cut.checks.map Program.filesystemEvent = _
      have functions : Program.filesystemEvent = fun pair : Request × Reply =>
          Program.filesystemPrefixEvent (pair.1, some pair.2) := by
        funext pair
        cases pair
        rfl
      rw [functions]
      simp only [Publication.completed, List.map_map, Function.comp_def] }
  have selectedAction : earlierTick.action.eventFor actor =
      some (Program.filesystemPrefixEvent (openedRequest, some openedReply)) := by
    simp only [action, ActorAction.eventFor, ↓reduceIte, Program.filesystemPrefixEvent]
  obtain ⟨original, sameOccurrence⟩ := actual_primitive_adapter_from_source descriptors lifetimes references
    environment journal earlierAt selectedAction beforeAt occurrence
  let source : EarlierOpen runtime initial all context openedRequest openedReply fd position := {
    position := earlierPosition
    tick := earlierTick
    input
    output
    selected := earlierAt
    earlier
    inputActor := actor
    action
    present := beforeAt
    afterPresent := afterAt
    adapter := original
    logicalBefore := congrArg (fun value => value.logicalBefore) sameOccurrence
    opening := cut.opening
    replyExact := sameReply
    before := beforeExact
    after := afterExact }
  have postActor : ActorHistoryWith runtime actor (SourceReturnAt runtime all actor)
      (input.events.length + 1) cut.opening.after (cut.following.map Program.filesystemEvent) after := by
    have actual : ActorHistoryWith runtime actor (SourceReturnAt runtime all actor)
        (cut.opening.ordinal + 1) cut.opening.after (cut.following.map Program.filesystemEvent) after :=
      recorded_actor postHistory
    have ordinal : cut.opening.ordinal = input.events.length := by
      rw [count, cut.count]
      simp only [rawBefore, List.length_append, List.length_map]
    rwa [ordinal] at actual
  have restActor : ActorHistoryWith runtime actor (SourceReturnAt runtime all actor)
      (input.events.length + 1 + (cut.following.map Program.filesystemEvent).length) after rest
      (tick.before.project engine) := by
    have countEvents := congrArg List.length cut.trace
    simp only [List.length_append, List.length_cons] at countEvents
    have ordinal : 0 + first.length + (events.map Program.filesystemEvent).length =
        input.events.length + 1 + (cut.following.map Program.filesystemEvent).length := by
      rw [count]
      simp only [rawBefore, List.length_append, List.length_map]
      omega
    exact ordinal ▸ tail
  refine ⟨{
    source
    post := cut.following
    remaining := last
    guards := adapter.occurrence.inside.map Program.filesystemPrefixEvent
    chunks := PrimitiveFilesystem.reached_chunks remaining
    retaining := cut.retaining
    passive := cut.passive
    tail := ?_ }, rfl, rfl, ?_⟩
  · simpa only [List.append_assoc] using actor_with_append postActor restActor
  · change engine.events = input.events ++ .returned (.filesystem openedRequest) openedReply ::
      (cut.following.map Program.filesystemEvent ++ last ++ adapter.occurrence.inside.map Program.filesystemPrefixEvent)
    rw [inputTrace]
    simpa only [rawAfter, rest, List.append_assoc] using full

-- §AR-host-boundary.interfaces: Retain the original source-cut projection exactly.
theorem primitive_earlier_open {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {context following : List Program.Event} {openedRequest : Request} {openedReply : Reply} {fd : UInt64}
    (trace : adapter.occurrence.logicalBefore =
      context ++ .returned (.filesystem openedRequest) openedReply :: following)
    (opening : openedRequest.op = .openAt) (recognized : descriptor openedReply = some fd) :
    ∃ result : EarlierOpen runtime initial all context openedRequest openedReply fd position,
      result.inputActor = actor := by
  obtain ⟨result, actor, guards, trace⟩ := primitive_earlier_open_continuation descriptors lifetimes references environment
    journal selected present adapter trace opening recognized
  exact ⟨result.source, actor⟩

end LeanCage.Host.Kernel
