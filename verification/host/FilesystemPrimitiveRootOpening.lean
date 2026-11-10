import FilesystemRootReopen
import FilesystemChildOpenSource
import FilesystemPrimitiveObservations
import FilesystemPrimitiveIntervals
import FilesystemAccessProofs.Last

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.lookup: A successful guarded mkdir ends in its actual primary call.
-- Parent checks remain in the exact raw transcript, and rejected checks cannot report zero.
theorem guarded_mkdir_returned {request : Request} {events : List (Request × Reply)} {reply : Reply}
    (source : Returns (guardedCall request) events reply) (mkdir : request.op = .mkdirAt)
    (zero : reply.1 = 0) :
    ∃ checks, CheckedParents (Lookup.parents request) checks ∧ events = checks ++ [(request, reply)] := by
  unfold guardedCall at source
  obtain ⟨checks, accepted, after, checked, following, shape⟩ := adapter_returns_bind_split _ _ source
  cases accepted with
  | false =>
    change Returns (.pure Lookup.unsupported) after reply at following
    cases following
    have nonzero : Lookup.unsupported.1 ≠ 0 := by decide
    exact False.elim (nonzero zero)
  | true =>
    change Returns (.call request (fun actual => Lookup.opened request actual)) after reply at following
    cases following with
    | call operation next actual tail value remaining =>
      have opened : Lookup.opened request actual = .pure actual := by
        simp only [Lookup.opened, mkdir]
        rfl
      change Returns (Lookup.opened request actual) tail reply at remaining
      rw [opened] at remaining
      cases remaining
      exact ⟨checks, checked_parents_source checked, shape⟩

theorem guarded_mkdir_chunk {request : Request} {events : List Program.Event} {reply : Reply}
    (source : Program.Returns (PrimitiveFilesystem.lowerEffect (.filesystem request)) events reply)
    (mkdir : request.op = .mkdirAt) (zero : reply.1 = 0) :
    ∃ checks, CheckedParents (Lookup.parents request) checks ∧
      events = checks.map Program.filesystemEvent ++ [.returned (.filesystem request) reply] := by
  obtain ⟨raw, actual, trace⟩ := Program.lift_filesystem_source (guardedCall request) source
  obtain ⟨checks, checked, shape⟩ := guarded_mkdir_returned actual mkdir zero
  exact ⟨checks, checked, by simp only [trace, shape, List.map_append, List.map_cons, List.map_nil,
    Program.filesystemEvent]⟩

-- §FS-host-boundary.ownership: The last completed logical call is this very mkdir;
-- its actual raw parent probes and primitive return remain available separately.
theorem chunks_final_mkdir {logical raw : List Program.Event} (chunks : PrimitiveFilesystem.Chunks logical raw)
    {context : List Program.Event} {request : Request} {reply : Reply}
    (trace : logical = context ++ [.returned (.filesystem request) reply])
    (mkdir : request.op = .mkdirAt) (zero : reply.1 = 0) :
    ∃ first checks, PrimitiveFilesystem.Chunks context first ∧ CheckedParents (Lookup.parents request) checks ∧
      raw = (first ++ checks.map Program.filesystemEvent) ++ [.returned (.filesystem request) reply] := by
  have indexed : PrimitiveFilesystem.Chunks (context ++ [.returned (.filesystem request) reply]) raw := trace ▸ chunks
  obtain ⟨first, remaining, before, after, shape⟩ := PrimitiveFilesystem.chunks_split context _ indexed
  cases after with
  | cons effect result inside logical raw source rest =>
    cases rest
    obtain ⟨checks, checked, actual⟩ := guarded_mkdir_chunk source mkdir zero
    exact ⟨first, checks, before, checked, by simp only [shape, List.append_nil, actual, List.append_assoc]⟩

private theorem reached_empty {α : Type} {first last : Program α} {raw : List Program.Event}
    (source : PrimitiveFilesystem.Reached first [] raw last) : raw = [] ∧ first = last := by
  cases source
  exact ⟨rfl, rfl⟩

-- §AR-host-boundary.primitives: Splitting at the last logical call retains its actual
-- original continuation and complete raw adapter chunk, rather than inventing a source cut.
theorem reached_final_filesystem {α : Type} {program after : Program α} {raw : List Program.Event}
    (context : List Program.Event) (request : Request) (reply : Reply)
    (source : PrimitiveFilesystem.Reached program (context ++ [.returned (.filesystem request) reply]) raw after) :
    ∃ first inside next,
      PrimitiveFilesystem.Reached program context first (.call (.filesystem request) next) ∧
      Program.Returns (PrimitiveFilesystem.lowerEffect (.filesystem request)) inside reply ∧
      raw = first ++ inside ∧ after = next reply := by
  induction context generalizing program raw with
  | nil =>
    cases source with
    | call effect next actual inside logical raw after adapter rest =>
      obtain ⟨empty, same⟩ := reached_empty rest
      exact ⟨[], inside, next, .refl _, adapter, by simp only [empty, List.append_nil, List.nil_append], same.symm⟩
  | cons event context ih =>
    cases source with
    | call effect next actual inside logical raw after adapter rest =>
      obtain ⟨first, last, final, leading, active, trace, remaining⟩ := ih rest
      exact ⟨inside ++ first, last, final, .call effect next actual inside _ _ _ adapter leading,
        active, by simp only [trace, List.append_assoc], remaining⟩

private theorem filesystem_returns_prefix {α : Type} {program : Filesystem.Program α}
    {events : List (Request × Reply)} {value : α} (source : Returns program events value) :
    Prefix program (Publication.completed events) := by
  induction source with
  | pure => exact .empty _
  | call request next reply tail value rest ih => exact .returned request next reply _ ih

structure PrimitiveMkdirBeforeOpen {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} (made : Request) (reply : Reply) where
  observation : PrimitiveObservationAt runtime initial all tick actor engine (.filesystem made) reply
  probes : ∀ event ∈ observation.rawAfter, NamespacePassiveEvent event
  retaining : ∀ event ∈ observation.rawAfter, RetainingEvent event
  context : List Program.Event
  rawContext : List Program.Event
  next : Reply → Program UInt32
  checks : List (Request × Reply)
  reached : PrimitiveFilesystem.Reached Entrypoint.run context rawContext (.call (.filesystem made) next)
  guarded : Prefix (guardedCall made) (Publication.completed checks ++ [(made, some reply)])
  beforeTrace : observation.rawBefore = rawContext ++ checks.map Program.filesystemEvent

-- §FS-host-boundary.ownership: After the real successful mkdir, the next directory open
-- contains only its actual parent probes. No assumed quiet owner interval is needed.
theorem primitive_mkdir_before_open_exact {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {context : List Program.Event} {made : Request} {reply : Reply}
    (trace : adapter.occurrence.logicalBefore = context ++ [.returned (.filesystem made) reply])
    (mkdir : made.op = .mkdirAt) (zero : reply.1 = 0) (opening : request.op = .openAt) :
    ∃ source : PrimitiveMkdirBeforeOpen (runtime := runtime) (initial := initial) (all := all)
      (tick := tick) (actor := actor) (engine := engine) made reply, source.context = context := by
  have reached : PrimitiveFilesystem.Reached Entrypoint.run
      (context ++ [.returned (.filesystem made) reply]) adapter.occurrence.rawBefore
      (.call (.filesystem adapter.occurrence.primary) adapter.occurrence.next) := trace ▸ adapter.occurrence.reached
  obtain ⟨first, chunk, next, preceding, sourceChunk, chunkTrace, finalProgram⟩ :=
    reached_final_filesystem context made reply reached
  obtain ⟨raw, guardSource, guardTrace⟩ := Program.lift_filesystem_source (guardedCall made) sourceChunk
  obtain ⟨checks, checked, guardShape⟩ := guarded_mkdir_returned guardSource mkdir zero
  have rawTrace : adapter.occurrence.rawBefore =
      (first ++ checks.map Program.filesystemEvent) ++ [.returned (.filesystem made) reply] := by
    rw [chunkTrace, guardTrace, guardShape]
    simp only [List.map_append, List.map_cons, List.map_nil, Program.filesystemEvent, List.append_assoc]
  have guardPrefix : Prefix (guardedCall made) (Publication.completed checks ++ [(made, some reply)]) := by
    have prefixRun := filesystem_returns_prefix guardSource
    rw [guardShape] at prefixRun
    simpa only [Publication.completed, List.map_append, List.map_cons, List.map_nil] using prefixRun
  obtain ⟨guardChecks, guarded, primary, inside⟩ := guarded_namespace_last adapter.occurrence.adapter (.inl opening)
  let before := first ++ checks.map Program.filesystemEvent
  let after := adapter.occurrence.inside.map Program.filesystemPrefixEvent
  have full : engine.events = before ++ .returned (.filesystem made) reply :: after := by
    rw [adapter.occurrence.trace, rawTrace]
    simp only [before, after, List.append_assoc, List.singleton_append]
  have history := adapter.source.history
  rw [full] at history
  obtain ⟨middle, leading, active⟩ := actor_with_split before _ history
  obtain ⟨actualBefore, actualAfter, environment, operation, sampled, tail⟩ := actor_with_head active
  have leading : ActorHistoryWith runtime actor (SourceReturnAt runtime all actor) 0
      (adapter.source.launch.tick.after.project (.initialFrom (PrimitiveFilesystem.lower Entrypoint.run)
        adapter.source.launch.references adapter.source.launch.closeExec adapter.source.launch.workingDirectory))
      before actualBefore := by
    simpa only [List.append_nil] using actor_with_append leading environment
  let observation : PrimitiveObservationAt runtime initial all tick actor engine (.filesystem made) reply := {
    source := adapter.source
    rawBefore := before
    rawAfter := after
    trace := full
    before := actualBefore
    after := actualAfter
    leading
    actual := operation
    sampled := by simpa only [Nat.zero_add] using sampled
    tail := by simpa only [Nat.zero_add] using tail }
  refine ⟨{
    observation
    probes := ?_
    retaining := adapter_namespace_prefix_retaining adapter (.inl opening)
    context := context
    rawContext := first
    next
    checks
    reached := preceding
    guarded := guardPrefix
    beforeTrace := rfl }, rfl⟩
  intro event member
  change event ∈ adapter.occurrence.inside.map Program.filesystemPrefixEvent at member
  rw [inside] at member
  simp only [List.map_map, Function.comp_def, Program.filesystemPrefixEvent] at member
  obtain ⟨pair, present, same⟩ := List.mem_map.mp member
  subst event
  rcases checked_parents_probes guarded pair present with magic | flags
  · simp only [NamespacePassiveEvent, NamespacePassive, magic]
  · simp only [NamespacePassiveEvent, NamespacePassive, flags]

-- §AR-host-boundary.interfaces: Keep the earlier observation consumer unchanged.
theorem primitive_mkdir_before_open {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {context : List Program.Event} {made : Request} {reply : Reply}
    (trace : adapter.occurrence.logicalBefore = context ++ [.returned (.filesystem made) reply])
    (mkdir : made.op = .mkdirAt) (zero : reply.1 = 0) (opening : request.op = .openAt) :
    Nonempty (PrimitiveMkdirBeforeOpen (runtime := runtime) (initial := initial) (all := all)
      (tick := tick) (actor := actor) (engine := engine) made reply) := by
  obtain ⟨source, contextExact⟩ := primitive_mkdir_before_open_exact adapter trace mkdir zero opening
  exact ⟨source⟩

structure SelectedMkdirBeforeOpen {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {currentTick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {made : Request} {reply : Reply}
    (source : PrimitiveMkdirBeforeOpen (runtime := runtime) (initial := initial) (all := all)
      (tick := currentTick) (actor := actor) (engine := engine) made reply) (currentPosition : Nat) where
  position : Nat
  tick : ActorTick runtime
  input : EngineState
  output : EngineState
  selected : all[position]? = some tick
  action : tick.action = .returned actor (.filesystem made) reply
  present : tick.before.actors actor = some input
  afterPresent : tick.after.actors actor = some output
  before : source.observation.before = tick.before.project input
  after : source.observation.after = tick.after.project output
  exactPrefix : input.events = source.observation.rawBefore
  earlier : position < currentPosition
  probes : ∀ event ∈ engine.events.drop (input.events.length + 1), NamespacePassiveEvent event

-- §FS-host-boundary.ownership: Select the returned mkdir's real global position and exact
-- source prefix. Its derived probe suffix is already sufficient for the ownership interval.
theorem PrimitiveMkdirBeforeOpen.selected {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {final : Population} {all : List (ActorTick runtime)} {currentTick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {made : Request} {reply : Reply}
    (source : PrimitiveMkdirBeforeOpen (runtime := runtime) (initial := initial) (all := all)
      (tick := currentTick) (actor := actor) (engine := engine) made reply)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {currentPosition : Nat} (currentAt : all[currentPosition]? = some currentTick)
    (present : currentTick.before.actors actor = some engine) :
    Nonempty (SelectedMkdirBeforeOpen source currentPosition) := by
  obtain ⟨position, tick, input, output, selected, action, inputAt, outputAt, count, before, after⟩ :=
    source.observation.sampled
  have less : input.events.length < engine.events.length := by
    rw [source.observation.trace]
    simp only [List.length_append, List.length_cons]
    omega
  have earlier := source_ordinal_orders_positions journal selected currentAt actor input engine inputAt present less
  obtain ⟨leading, inside, trailing, trace, region⟩ := journal_between_selected journal selected currentAt
    (Nat.le_of_lt earlier)
  obtain ⟨extra, eventTrace⟩ := actor_journal_event_prefix region actor input engine inputAt present
  have exactPrefix : input.events = source.observation.rawBefore := by
    have actual : engine.events.take source.observation.rawBefore.length = input.events := by
      rw [← count, eventTrace]
      exact List.take_left
    have raw : engine.events.take source.observation.rawBefore.length = source.observation.rawBefore := by
      rw [source.observation.trace]
      exact List.take_left
    exact actual.symm.trans raw
  have sourceTrace : engine.events = input.events ++ .returned (.filesystem made) reply :: source.observation.rawAfter := by
    rw [exactPrefix]
    exact source.observation.trace
  refine ⟨⟨position, tick, input, output, selected, action, inputAt, outputAt, before, after,
    exactPrefix, earlier, ?_⟩⟩
  intro event member
  apply source.probes event
  simpa only [sourceTrace, List.drop_length_add_append, List.drop_succ_cons, List.drop_zero] using member

-- §FS-host-boundary.ownership: The real mkdir and following probes retain the helper's
-- parent FD/OFD. No guessed live handle or whole callback/FFI frame supplies this connection.
theorem PrimitiveMkdirBeforeOpen.parent_reference {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel)
    {initial : World} {all : List (ActorTick runtime)} {currentTick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {made : Request} {reply : Reply}
    (source : PrimitiveMkdirBeforeOpen (runtime := runtime) (initial := initial) (all := all)
      (tick := currentTick) (actor := actor) (engine := engine) made reply)
    (mkdir : made.op = .mkdirAt) {handle : Handle}
    (reference : engine.references made.first = some handle) :
    source.observation.before.handles made.first = some handle := by
  have probes := actor_retaining_event_handles descriptors source.observation.tail source.retaining
  have primary := descriptors.retained _ _ _ _ source.observation.actual (by simp [RetainsDescriptors, mkdir])
  have handles : engine.references = source.observation.before.handles := probes.trans primary
  rw [← handles]
  exact reference

theorem PrimitiveMkdirBeforeOpen.parent_current {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel)
    {initial : World} {all : List (ActorTick runtime)} {currentTick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {made : Request} {reply : Reply}
    (source : PrimitiveMkdirBeforeOpen (runtime := runtime) (initial := initial) (all := all)
      (tick := currentTick) (actor := actor) (engine := engine) made reply)
    (mkdir : made.op = .mkdirAt) {handle : Handle}
    (reference : source.observation.before.handles made.first = some handle) :
    engine.references made.first = some handle := by
  have probes := actor_retaining_event_handles descriptors source.observation.tail source.retaining
  have primary := descriptors.retained _ _ _ _ source.observation.actual (by simp [RetainsDescriptors, mkdir])
  have handles : engine.references = source.observation.before.handles := probes.trans primary
  rw [handles]
  exact reference

-- §AR-host-boundary.interfaces: Preserve the very original source call and guard chunk
-- at the earlier selected raw point. A fresh occurrence search cannot change its context.
def SelectedMkdirBeforeOpen.occurrence {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {currentTick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {made : Request} {reply : Reply}
    {source : PrimitiveMkdirBeforeOpen (runtime := runtime) (initial := initial) (all := all)
      (tick := currentTick) (actor := actor) (engine := engine) made reply} {currentPosition : Nat}
    (selected : SelectedMkdirBeforeOpen source currentPosition) :
    PrimitiveFilesystem.FilesystemOccurrence Entrypoint.run selected.input.events made (some reply) := {
  primary := made
  next := source.next
  logicalBefore := source.context
  rawBefore := source.rawContext
  inside := Publication.completed source.checks
  reached := source.reached
  adapter := source.guarded
  trace := by
    rw [selected.exactPrefix, source.beforeTrace]
    have functions : Program.filesystemEvent = fun pair : Request × Reply =>
        Program.filesystemPrefixEvent (pair.1, some pair.2) := by
      funext pair
      cases pair
      rfl
    rw [functions]
    simp only [Publication.completed, List.map_map, Function.comp_def] }

-- §FS-host-boundary.ownership: The earlier root-use producer uses this actual sampled
-- mkdir, exact original source context, and retained physical parent, with no birth/owner input.
noncomputable def SelectedMkdirBeforeOpen.rootUse {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)} {currentTick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {made : Request} {reply : Reply}
    {source : PrimitiveMkdirBeforeOpen (runtime := runtime) (initial := initial) (all := all)
      (tick := currentTick) (actor := actor) (engine := engine) made reply} {currentPosition : Nat}
    (selected : SelectedMkdirBeforeOpen source currentPosition)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    (mkdir : made.op = .mkdirAt) (component : Directories.component made.left = true)
    {parent : Handle} (parentNow : engine.references made.first = some parent)
    (acknowledged : reply.1 = 0 ∧ reply.2.isEmpty = true)
    (invocation : Nonempty (RunCreationPrefix source.context made none) ∨ Nonempty (StagingCall source.context made)) :
    PrimitiveRootUse runtime initial all selected.tick := by
  have action : selected.tick.action.eventFor actor =
      some (Program.filesystemPrefixEvent (made, some reply)) := by
    simp only [selected.action, ActorAction.eventFor, ↓reduceIte, Program.filesystemPrefixEvent]
  let produced := actual_primitive_adapter_from_source descriptors lifetimes references environment
    journal selected.selected action selected.present selected.occurrence
  let adapter := Classical.choose produced
  have same := Classical.choose_spec produced
  have parentBefore := source.parent_reference descriptors mkdir parentNow
  rw [selected.before] at parentBefore
  exact {
    actor
    engine := selected.input
    request := made
    reply
    action
    present := selected.present
    mkdir
    component
    parent
    reference := parentBefore
    accepted := acknowledged
    adapter
    invocation := by rw [same]; exact invocation }

structure PrimitiveNewChildReopen {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} (uid : Nat) (parent : UInt64) (prefixName : String)
    (before : List (Request × Option Reply)) (request : Request) (context : List Program.Event) where
  child : NewChildOpening uid parent prefixName before request
  made : Request := {
    op := .mkdirAt
    first := parent
    second := 448
    left := (prefixName ++ Snapshot.hex child.random).toUTF8 }
  madeExact : made = {
    op := .mkdirAt
    first := parent
    second := 448
    left := (prefixName ++ Snapshot.hex child.random).toUTF8 }
  source : PrimitiveMkdirBeforeOpen (runtime := runtime) (initial := initial) (all := all)
    (tick := tick) (actor := actor) (engine := engine) made child.made
  sourceContext : source.context = context ++ child.randomEvents.map Program.filesystemEvent

-- §FS-host-boundary.ownership: This actual shared newChild program supplies the exact
-- mkdir arguments, acknowledgement and raw source suffix used by the reopening consumer.
theorem primitive_new_child_reopen {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (uid : Nat) (parent : UInt64) (prefixName : String) {before : List (Request × Option Reply)}
    {context : List Program.Event}
    (active : Prefix (Directories.newChild uid parent prefixName) (before ++ [(request, none)]))
    (trace : adapter.occurrence.logicalBefore = context ++ before.map Program.filesystemPrefixEvent)
    (opening : request.op = .openAt) :
    Nonempty (PrimitiveNewChildReopen (runtime := runtime) (initial := initial) (all := all)
      (tick := tick) (actor := actor) (engine := engine) uid parent prefixName before request context) := by
  obtain ⟨child⟩ := actual_new_child_opening uid parent prefixName active opening
  let made : Request := {
    op := .mkdirAt
    first := parent
    second := 448
    left := (prefixName ++ Snapshot.hex child.random).toUTF8 }
  have logical : adapter.occurrence.logicalBefore =
      (context ++ child.randomEvents.map Program.filesystemEvent) ++ [.returned (.filesystem made) child.made] := by
    have mapped := congrArg (fun events : List (Request × Option Reply) =>
      context ++ events.map Program.filesystemPrefixEvent) child.trace
    apply trace.trans (mapped.trans ?_)
    simp only [List.map_append, completed_filesystem_events, List.map_cons, List.map_nil,
      Program.filesystemPrefixEvent, List.append_assoc, made]
  obtain ⟨source, exactContext⟩ := primitive_mkdir_before_open_exact adapter logical rfl child.acknowledged.1 opening
  exact ⟨⟨child, made, rfl, source, exactContext⟩⟩

end LeanCage.Host.Kernel
