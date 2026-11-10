import FilesystemEarlierOpen
import FilesystemCreationSources

namespace LeanCage.Host.Kernel
open Filesystem

private theorem returned_pending {α : Type} {program : Filesystem.Program α}
    {events first last : List (Request × Reply)} {request : Request} {reply : Reply} {value : α}
    (source : Returns program events value) (trace : events = first ++ (request, reply) :: last) :
    Prefix program (Publication.completed first ++ [(request, none)]) := by
  subst events
  induction first generalizing program with
  | nil =>
    cases source with
    | call request next reply tail value rest => exact .lost request next
  | cons event first ih =>
    cases source with
    | call request next reply tail value rest => exact .returned _ _ _ _ (ih rest)

structure CreatedOpening (program : Filesystem.Program (Result RunDirectory.Owned))
    (events : List (Request × Reply)) (owned : RunDirectory.Owned) where
  before : List (Request × Reply)
  after : List (Request × Reply)
  request : Request
  reply : Reply
  trace : events = before ++ (request, reply) :: after
  opening : request.op = .openAt
  flags : request.second = directoryFlags
  recognized : descriptor reply = some owned.directory.fd
  reserved : PrivateNames.reservedBytes request.left = true
  active : Prefix program (Publication.completed before ++ [(request, none)])

-- §FS-host-boundary.ownership: Select the original run/validator child-open source call
-- from the real successful create program, preserving preceding replies and its raw name.
theorem created_run_opening {events : List (Request × Reply)} {owned : RunDirectory.Owned}
    (source : Returns RunDirectory.create events (.ok owned)) :
    Nonempty (CreatedOpening RunDirectory.create events owned) := by
  obtain ⟨uid, child, selecting, creating, marked, name, shape, selected, created, sameDirectory,
    sameName, markedZero, markedEmpty, decoded, path, bounded⟩ := RunDirectory.create_source source
  obtain ⟨random, randomEvents, made, openingEvents, createTrace, randomized, randomSize, childName,
    component, madeZero, madeEmpty, directoryOpening, childUid, childMode⟩ := created
  obtain ⟨reply, information, openingTrace, recognized, parsed, trusted⟩ := directoryOpening
  let request : Request := {
    op := .openAt
    first := owned.container.fd
    second := directoryFlags
    left := child.name }
  let before := selecting ++ randomEvents ++ [({
    op := .mkdirAt, first := owned.container.fd, second := 448, left := child.name}, made)]
  let after : List (Request × Reply) := [({op := .stat, first := child.directory.fd}, information), ({
    op := .setAttribute
    first := owned.directory.fd
    left := PrivateNames.attributeName
    right := PrivateNames.attributeValue}, marked)]
  have trace : events = before ++ (request, reply) :: after := by
    rw [shape, createTrace, openingTrace]
    simp only [before, after, request, List.append_assoc, List.cons_append, List.nil_append]
  exact ⟨{
    before
    after
    request
    reply
    trace
    opening := rfl
    flags := rfl
    recognized := by rw [sameDirectory]; exact recognized
    reserved := by change PrivateNames.reservedBytes child.name = true; rw [childName]; exact private_prefix_reserved _
    active := returned_pending source trace }⟩

structure CreatedRunRoot {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (all : List (ActorTick runtime)) (owned : RunDirectory.Owned) (limit : Nat) where
  context : List Program.Event
  request : Request
  reply : Reply
  earlier : EarlierOpen runtime initial all context request reply owned.directory.fd limit
  source : RootOpenReceipt runtime initial all earlier.tick earlier.inputActor earlier.input request earlier.position

-- §FS-host-boundary.ownership: Carry the real completed create call through its exact
-- expanded transcript to the original open and source-registered mkdir of this invocation.
theorem primitive_created_run_root {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {context following : List Program.Event} {creating : List (Request × Reply)} {owned : RunDirectory.Owned}
    (created : Returns RunDirectory.create creating (.ok owned))
    (trace : adapter.occurrence.logicalBefore = context ++ creating.map Program.filesystemEvent ++ following) :
    ∃ result : CreatedRunRoot runtime initial all owned position, result.earlier.inputActor = actor := by
  obtain ⟨opening⟩ := created_run_opening created
  let before := context ++ opening.before.map Program.filesystemEvent
  let after := opening.after.map Program.filesystemEvent ++ following
  have selectedTrace : adapter.occurrence.logicalBefore = before ++
      .returned (.filesystem opening.request) opening.reply :: after := by
    apply trace.trans
    have mapped := congrArg (fun events : List (Request × Reply) =>
      context ++ events.map Program.filesystemEvent ++ following) opening.trace
    exact mapped.trans (by
      simp only [before, after, List.map_append, List.map_cons, Program.filesystemEvent,
        List.append_assoc, List.cons_append])
  obtain ⟨earlier, sameActor⟩ := primitive_earlier_open descriptors lifetimes references environment journal selected
    present adapter selectedTrace opening.opening opening.recognized
  have invocation : RunCreationPrefix earlier.adapter.occurrence.logicalBefore opening.request none := {
    context := context
    inside := Publication.completed opening.before
    active := opening.active
    trace := earlier.logicalBefore.trans (by
      change context ++ opening.before.map Program.filesystemEvent = _
      simp only [completed_filesystem_events]) }
  obtain ⟨receipt⟩ := run_private_reopen_receipt descriptors lifetimes references environment journal
    earlier.selected earlier.present earlier.adapter invocation opening.opening opening.reserved
  exact ⟨⟨before, opening.request, opening.reply, earlier, receipt⟩, sameActor⟩

end LeanCage.Host.Kernel
