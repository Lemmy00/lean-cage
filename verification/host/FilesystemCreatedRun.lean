import FilesystemRootOpenReceipt
import FilesystemEarlierOpen
import RunDirectoryProofs.Source

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

structure RunOpening (events : List (Request × Reply)) (run : RunDirectory.Owned) where
  before : List (Request × Reply)
  after : List (Request × Reply)
  request : Request
  reply : Reply
  trace : events = before ++ (request, reply) :: after
  opening : request.op = .openAt
  recognized : descriptor reply = some run.directory.fd
  reserved : PrivateNames.reservedBytes request.left = true
  active : Prefix RunDirectory.create (Publication.completed before ++ [(request, none)])
  uid : Nat
  uidReply : Reply
  uidFollowing : List (Request × Reply)
  beforeUid : before = ({op := .euid}, uidReply) :: uidFollowing
  uidSuccess : nativeError uidReply = false
  uidEmpty : uidReply.2 = .empty
  uidValue : uidReply.1.toNat = uid
  informationReply : Reply
  markerReply : Reply
  afterShape : after = [({op := .stat, first := run.directory.fd}, informationReply),
    ({op := .setAttribute, first := run.directory.fd,
      left := PrivateNames.attributeName, right := PrivateNames.attributeValue}, markerReply)]
  parsed : parseStat informationReply = some run.directory.information
  trusted : Directories.trusted uid run.directory.information = true
  operation : request = {
    op := .openAt, first := run.container.fd, second := directoryFlags, left := run.name }
  retaining : ∀ event ∈ after, RetainsDescriptors event.1.op
  identity : ∀ event ∈ after.map Program.filesystemEvent, PrimitiveFilesystem.IdentityEvent event
  nondestructive : ∀ event ∈ after, ¬ DestructiveRequest event.1

-- §FS-host-boundary.ownership: The completed run producer identifies its own
-- reserved open, actual descriptor and following stat/private-marker calls.
-- No independent successful directory or guessed lifetime is substituted.
theorem completed_run_original_opening {events : List (Request × Reply)} {run : RunDirectory.Owned}
    (source : Returns RunDirectory.create events (.ok run)) : Nonempty (RunOpening events run) := by
  obtain ⟨uid, child, selecting, creating, marked, name, trace, selected,
    created, directory, childName, markedZero, markedEmpty, decoded, path, bounded⟩ :=
    RunDirectory.create_source source
  obtain ⟨random, randomEvents, made, openingEvents, createdTrace, randomized,
    randomSize, childBytes, component, madeZero, madeEmpty, opened, childUid, childMode⟩ := created
  obtain ⟨reply, information, openingTrace, recognized, parsed, trusted⟩ := opened
  obtain ⟨uidReply, uidFollowing, selectedTrace, uidSuccess, uidEmpty, uidValue, uidBound, selectedOpening⟩ := selected
  let request : Request := {
    op := .openAt, first := run.container.fd, second := directoryFlags, left := run.name }
  let before := selecting ++ randomEvents ++ [({
    op := .mkdirAt, first := run.container.fd, second := 448, left := run.name }, made)]
  let after : List (Request × Reply) := [
    ({op := .stat, first := run.directory.fd}, information),
    ({op := .setAttribute, first := run.directory.fd,
      left := PrivateNames.attributeName, right := PrivateNames.attributeValue}, marked)]
  have shape : events = before ++ (request, reply) :: after := by
    rw [trace, createdTrace, openingTrace, ← directory, ← childName]
    simp only [before, after, request, List.append_assoc, List.cons_append, List.nil_append]
  exact ⟨{
    before
    after
    request
    reply
    trace := shape
    opening := rfl
    recognized := by rw [directory]; exact recognized
    reserved := by
      change PrivateNames.reservedBytes run.name = true
      rw [childName, childBytes]
      exact private_prefix_reserved _
    active := returned_pending source shape
    uid
    uidReply
    uidFollowing := uidFollowing ++ randomEvents ++ [({
      op := .mkdirAt, first := run.container.fd, second := 448, left := run.name}, made)]
    beforeUid := by simp only [before, selectedTrace, List.cons_append, List.append_assoc]
    uidSuccess
    uidEmpty
    uidValue := uidValue.symm
    informationReply := information
    markerReply := marked
    afterShape := rfl
    parsed := by rw [directory]; exact parsed
    trusted := by rw [directory]; exact trusted
    operation := rfl
    retaining := by
      intro event member
      rcases List.mem_cons.mp member with rfl | later
      · simp [RetainsDescriptors]
      · have same := List.mem_singleton.mp later
        subst event
        simp [RetainsDescriptors]
    identity := by
      intro event member
      obtain ⟨event, occurs, rfl⟩ := List.mem_map.mp member
      rcases List.mem_cons.mp occurs with rfl | later
      · rfl
      · have same := List.mem_singleton.mp later
        subst event
        rfl
    nondestructive := by
      intro event member
      rcases List.mem_cons.mp member with rfl | later
      · simp [DestructiveRequest]
      · have same := List.mem_singleton.mp later
        subst event
        simp [DestructiveRequest] }⟩

structure CreatedRunContinuation {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (all : List (ActorTick runtime)) (outside : List Program.Event)
    (created : List (Request × Reply)) (run : RunDirectory.Owned) (following : List Program.Event)
    (limit : Nat) (current : World) where
  opening : RunOpening created run
  earlier : EarlierOpenContinuation runtime initial all
    (outside ++ opening.before.map Program.filesystemEvent)
    (opening.after.map Program.filesystemEvent ++ following)
    opening.request opening.reply run.directory.fd limit current
  root : RootOpenReceipt runtime initial all earlier.source.tick earlier.source.inputActor earlier.source.input
    opening.request earlier.source.position

-- §FS-host-boundary.ownership: A later run operation obtains the actual same
-- source allocation/open cut through its lowering witness. Loss, raw guards
-- and every intervening actor/native row remain on that original journal.
theorem primitive_run_opening_continuation {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} (present : tick.before.actors actor = some engine)
    {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {outside : List Program.Event} {created : List (Request × Reply)} {run : RunDirectory.Owned}
    {following : List Program.Event}
    (opening : RunOpening created run)
    (trace : adapter.occurrence.logicalBefore = outside ++ created.map Program.filesystemEvent ++ following) :
    ∃ result : CreatedRunContinuation runtime initial all outside created run following position (tick.before.project engine),
      result.earlier.source.inputActor = actor ∧
      result.earlier.guards = adapter.occurrence.inside.map Program.filesystemPrefixEvent ∧
      engine.events = result.earlier.source.input.events ++ .returned (.filesystem result.opening.request) result.opening.reply ::
        (result.earlier.post.map Program.filesystemEvent ++ result.earlier.remaining ++ result.earlier.guards) := by
  have actualTrace : adapter.occurrence.logicalBefore =
      (outside ++ opening.before.map Program.filesystemEvent) ++
        .returned (.filesystem opening.request) opening.reply :: (opening.after.map Program.filesystemEvent ++ following) := by
    exact trace.trans ((congrArg (fun events : List (Request × Reply) =>
      outside ++ events.map Program.filesystemEvent ++ following) opening.trace).trans (by
        simp only [List.map_append, List.map_cons, Program.filesystemEvent, List.append_assoc, List.cons_append]))
  obtain ⟨continued, sameActor, guards, rawTrace⟩ := primitive_earlier_open_continuation descriptors lifetimes
    references environment journal selected present adapter actualTrace opening.opening opening.recognized
  let invocation : RunCreationPrefix continued.source.adapter.occurrence.logicalBefore opening.request none := {
    context := outside
    inside := Publication.completed opening.before
    active := opening.active
    trace := continued.source.logicalBefore.trans (by rw [completed_filesystem_events]) }
  obtain ⟨root⟩ := run_private_reopen_receipt descriptors lifetimes references environment journal
    continued.source.selected continued.source.present continued.source.adapter invocation opening.opening opening.reserved
  exact ⟨⟨opening, continued, root⟩, sameActor, guards, rawTrace⟩


-- §AR-host-boundary.interfaces: Preserve the completed-create consumer; the
-- earlier-open sibling also applies to a real marker-failure source prefix.
theorem primitive_created_run_continuation {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} (present : tick.before.actors actor = some engine)
    {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {outside : List Program.Event} {created : List (Request × Reply)} {run : RunDirectory.Owned}
    {following : List Program.Event}
    (source : Returns RunDirectory.create created (.ok run))
    (trace : adapter.occurrence.logicalBefore = outside ++ created.map Program.filesystemEvent ++ following) :
    ∃ result : CreatedRunContinuation runtime initial all outside created run following position (tick.before.project engine),
      result.earlier.source.inputActor = actor ∧
      result.earlier.guards = adapter.occurrence.inside.map Program.filesystemPrefixEvent ∧
      engine.events = result.earlier.source.input.events ++ .returned (.filesystem result.opening.request) result.opening.reply ::
        (result.earlier.post.map Program.filesystemEvent ++ result.earlier.remaining ++ result.earlier.guards) := by
  obtain ⟨opening⟩ := completed_run_original_opening source
  exact primitive_run_opening_continuation descriptors lifetimes references environment journal selected present
    adapter opening trace

end LeanCage.Host.Kernel
