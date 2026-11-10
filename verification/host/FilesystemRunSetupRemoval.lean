import FilesystemRunRemoval
import RunDirectoryProofs.SetupCleanup

namespace LeanCage.Host.Kernel
open Filesystem
universe u

private theorem prefix_bind_return {α β : Type} {program : Filesystem.Program α}
    {next : α → Filesystem.Program β} {first : List (Request × Reply)} {last : List (Request × Option Reply)}
    {value : α} (source : Returns program first value) (tail : Prefix (next value) last) :
    Prefix (program.bind next) (Publication.completed first ++ last) := by
  induction source with
  | pure => exact tail
  | call request continuation reply events value rest ih =>
    exact .returned request (fun reply => (continuation reply).bind next) reply _ (ih tail)

private theorem prefix_bind_left {α β : Type} {program : Filesystem.Program α}
    {next : α → Filesystem.Program β} {events : List (Request × Option Reply)}
    (source : Prefix program events) : Prefix (program.bind next) events := by
  induction source with
  | empty => exact .empty _
  | lost request continuation => exact .lost request (fun reply => (continuation reply).bind next)
  | returned request continuation reply tail rest ih =>
    exact .returned request (fun reply => (continuation reply).bind next) reply tail ih

private theorem returned_pending {α : Type} {program : Filesystem.Program α}
    {events first last : List (Request × Reply)} {request : Request} {reply : Reply} {value : α}
    (source : Returns program events value) (trace : events = first ++ (request, reply) :: last) :
    Prefix program (Publication.completed first ++ [(request, none)]) := by
  subst events
  induction first generalizing program with
  | nil => cases source with | call _ _ _ _ _ rest => exact .lost _ _
  | cons event first ih => cases source with | call _ _ _ _ _ rest => exact .returned _ _ _ _ (ih rest)

-- §FS-host-boundary.ownership: This descriptor view is a partial allocation,
-- not a successful run result. Its actual source marker reply may be an error.
def _root_.LeanCage.Host.RunDirectory.SetupRemoval.directoryView {before : List (Request × Option Reply)} {request : Request}
    (source : RunDirectory.SetupRemoval before request) : RunDirectory.Owned := {
  path := source.path
  directory := source.child.directory
  container := source.container
  name := source.child.name }

def _root_.LeanCage.Host.RunDirectory.SetupRemoval.openingEvents {before : List (Request × Option Reply)} {request : Request}
    (source : RunDirectory.SetupRemoval before request) : List (Request × Reply) :=
  source.selecting ++ source.creating ++ [({
    op := .setAttribute, first := source.child.directory.fd,
    left := PrivateNames.attributeName, right := PrivateNames.attributeValue }, source.marked)]

-- §FS-host-boundary.ownership: Reuse the original real open/stat before a
-- failed marker, retaining its actual bytes and source prefix. No invented
-- successful marker reply or completed create execution is needed.
theorem _root_.LeanCage.Host.RunDirectory.SetupRemoval.original_opening {before : List (Request × Option Reply)} {request : Request}
    (source : RunDirectory.SetupRemoval before request) :
    Nonempty (RunOpening source.openingEvents source.directoryView) := by
  obtain ⟨random, randomEvents, made, openingEvents, createdTrace, randomized,
    randomSize, childBytes, component, madeZero, madeEmpty, opened, childUid, childMode⟩ :=
    Publication.newChild_source _ _ _ source.created
  obtain ⟨reply, information, openingTrace, recognized, parsed, trusted⟩ := opened
  obtain ⟨uidReply, uidFollowing, selectedTrace, uidSuccess, uidEmpty, uidValue, uidBound, selectedOpening⟩ :=
    (RunDirectory.temporaryParent_source source.selected).2
  let operation : Request := {
    op := .openAt, first := source.container.fd, second := directoryFlags, left := source.child.name }
  let leading : List (Request × Reply) := source.selecting ++ randomEvents ++ [({
    op := .mkdirAt, first := source.container.fd, second := 448, left := source.child.name }, made)]
  let remaining : List (Request × Reply) := [
    ({op := .stat, first := source.child.directory.fd}, information),
    ({op := .setAttribute, first := source.child.directory.fd,
      left := PrivateNames.attributeName, right := PrivateNames.attributeValue}, source.marked)]
  have childTrace : source.creating =
      (randomEvents ++ [({op := .mkdirAt, first := source.container.fd, second := 448, left := source.child.name}, made)]) ++
        (operation, reply) :: [({op := .stat, first := source.child.directory.fd}, information)] := by
    rw [createdTrace, openingTrace]
  have shape : source.openingEvents = leading ++ (operation, reply) :: remaining := by
    rw [RunDirectory.SetupRemoval.openingEvents, childTrace]
    simp only [leading, remaining, List.append_assoc, List.cons_append, List.nil_append]
  have active : Prefix RunDirectory.create (Publication.completed leading ++ [(operation, none)]) := by
    have pending := returned_pending source.created childTrace
    unfold RunDirectory.create
    have targetTrace : Publication.completed leading ++ [(operation, none)] =
        Publication.completed source.selecting ++
          (Publication.completed (randomEvents ++ [({
            op := .mkdirAt, first := source.container.fd, second := 448, left := source.child.name}, made)]) ++
            [(operation, none)]) := by
      simp only [leading, Publication.completed, List.map_append, List.append_assoc]
    rw [targetTrace]
    apply prefix_bind_return source.selected
    exact prefix_bind_left pending
  refine ⟨{
    before := leading
    after := remaining
    request := operation
    reply
    trace := shape
    opening := rfl
    recognized
    reserved := by change PrivateNames.reservedBytes source.child.name = true; rw [childBytes]; exact private_prefix_reserved _
    active
    uid := source.uid
    uidReply
    uidFollowing := uidFollowing ++ randomEvents ++ [({
      op := .mkdirAt, first := source.container.fd, second := 448, left := source.child.name}, made)]
    beforeUid := by simp only [leading, selectedTrace, List.cons_append, List.append_assoc]
    uidSuccess
    uidEmpty
    uidValue := uidValue.symm
    informationReply := information
    markerReply := source.marked
    afterShape := rfl
    parsed
    trusted
    operation := rfl
    retaining := by
      intro event member
      rcases List.mem_cons.mp member with rfl | last
      · simp [RetainsDescriptors]
      · have same := List.mem_singleton.mp last
        subst event
        simp [RetainsDescriptors]
    identity := by
      intro event member
      obtain ⟨event, occurs, rfl⟩ := List.mem_map.mp member
      rcases List.mem_cons.mp occurs with rfl | last
      · rfl
      · have same := List.mem_singleton.mp last
        subst event
        rfl
    nondestructive := by
      intro event member
      rcases List.mem_cons.mp member with rfl | last
      · simp [DestructiveRequest]
      · have same := List.mem_singleton.mp last
        subst event
        simp [DestructiveRequest] }⟩

structure RunSetupRemovalAt {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (position : Nat) where
  invocation : RunCreationPrefix adapter.occurrence.logicalBefore request none
  source : RunDirectory.SetupRemoval invocation.inside request
  allocation : CreatedRunContinuation runtime initial all invocation.context source.openingEvents
    source.directoryView [.returned (.filesystem {op := .close, first := source.child.directory.fd}) source.closed]
    position (tick.before.project engine)
  sameActor : allocation.earlier.source.inputActor = actor
  eventTrace : engine.events = allocation.earlier.source.input.events ++
    .returned (.filesystem allocation.opening.request) allocation.opening.reply ::
      (allocation.earlier.post.map Program.filesystemEvent ++ allocation.earlier.remaining ++ allocation.earlier.guards)
  reference : engine.references request.first = some allocation.root.use.parent
  sameName : request.left = allocation.root.use.request.left
  quiet : ∀ event ∈ engine.events.drop (allocation.root.use.engine.events.length + 1), NondestructiveEvent event

private theorem drop_append_allowed {α : Type u} {first last : List α} (count : Nat) (allowed : α → Prop)
    (leading : ∀ event ∈ first.drop count, allowed event) (trailing : ∀ event ∈ last, allowed event) :
    ∀ event ∈ (first ++ last).drop count, allowed event := by
  intro event member
  rw [List.drop_append] at member
  rcases List.mem_append.mp member with member | member
  · exact leading event member
  · exact trailing event (List.mem_of_mem_drop member)

-- §FS-host-boundary.ownership: Marker failure retains the original parent
-- through its actual child close and current raw guard. The same source
-- prefix has no earlier destructive operation after this exact root birth.
theorem actual_run_setup_removal {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} (present : tick.before.actors actor = some engine)
    {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (invocation : RunCreationPrefix adapter.occurrence.logicalBefore request none)
    (unlink : request.op = .unlinkAt) : Nonempty (RunSetupRemovalAt adapter position) := by
  obtain ⟨source⟩ := RunDirectory.setup_removal_source invocation.active unlink
  obtain ⟨opening⟩ := source.original_opening
  have trace : adapter.occurrence.logicalBefore = invocation.context ++ source.openingEvents.map Program.filesystemEvent ++
      [.returned (.filesystem {op := .close, first := source.child.directory.fd}) source.closed] := by
    exact invocation.trace.trans ((congrArg (fun events => invocation.context ++
      events.map Program.filesystemPrefixEvent) source.trace).trans (by
        simp only [completed_filesystem_events, RunDirectory.SetupRemoval.openingEvents, List.map_append, List.map_cons,
          List.map_nil, Program.filesystemEvent, List.append_assoc, List.cons_append,
          List.nil_append]))
  obtain ⟨allocation, sameActor, guards, eventTrace⟩ := primitive_run_opening_continuation descriptors lifetimes
    references environment journal selected present adapter opening trace
  obtain ⟨point⟩ := allocation.allocation descriptors
  have keptGuards : ∀ event ∈ allocation.earlier.guards, RetainingEvent event := by
    rw [guards]
    exact adapter_namespace_prefix_retaining adapter (.inr (.inr (.inl unlink)))
  have parent : (tick.before.project engine).handles source.directoryView.container.fd =
      some allocation.root.use.parent := by
    apply point.after_kept_returns descriptors _ _ point.container
      (program := Program.liftFilesystem (Filesystem.Program.effect {
        op := .close, first := source.child.directory.fd})) (value := source.closed)
    · exact .call _ _ _ [] _ (.pure _)
    · apply Lowered.actor_filesystem
      change BorrowPost kernel source.directoryView.container.fd allocation.root.use.parent (fun _ => True)
        (.call {op := .close, first := source.child.directory.fd} (fun reply => .pure reply))
      apply BorrowPost.call
      · intro before after observed actual live
        rw [descriptors.close_other _ _ _ _ _ actual rfl (Ne.symm point.distinct)]
        exact live
      · intro before after reply actual live
        exact .pure True.intro
    · exact keptGuards
  have remainingTrace : allocation.earlier.remaining = allocation.opening.after.map Program.filesystemEvent ++
      [.returned (.filesystem {op := .close, first := source.child.directory.fd}) source.closed] :=
    PrimitiveFilesystem.chunks_identity allocation.earlier.chunks (by
      intro event member
      rcases List.mem_append.mp member with opened | closed
      · exact allocation.opening.identity event opened
      · have same := List.mem_singleton.mp closed
        subst event
        rfl)
  refine ⟨{
    invocation
    source
    allocation
    sameActor
    eventTrace
    reference := ?_
    sameName := ?_
    quiet := ?_ }⟩
  · exact Eq.mpr (congrArg (fun fd => engine.references fd = some allocation.root.use.parent)
      (congrArg Request.first source.operation)) parent
  · exact (congrArg Request.left source.operation).trans
      ((congrArg Request.left allocation.opening.operation).symm.trans allocation.root.sameName)
  · apply Eq.mp (congrArg (fun events => ∀ event ∈ events.drop
        (allocation.root.use.engine.events.length + 1), NondestructiveEvent event) eventTrace.symm)
    apply drop_append_allowed _ NondestructiveEvent
    · intro event member
      exact passive_event_nondestructive (allocation.root.probes event member)
    · intro event member
      rcases List.mem_cons.mp member with rfl | member
      · simp only [NondestructiveEvent, DestructiveRequest, allocation.opening.opening]
        decide
      · rcases List.mem_append.mp member with member | guardMember
        · rcases List.mem_append.mp member with postMember | remainingMember
          · obtain ⟨⟨operation, reply⟩, occurs, rfl⟩ := List.mem_map.mp postMember
            exact namespace_passive_not_destructive (allocation.earlier.passive (operation, reply) occurs)
          · rw [remainingTrace] at remainingMember
            rcases List.mem_append.mp remainingMember with opened | closed
            · obtain ⟨⟨operation, reply⟩, occurs, rfl⟩ := List.mem_map.mp opened
              exact allocation.opening.nondestructive (operation, reply) occurs
            · have same := List.mem_singleton.mp closed
              subst event
              simp [NondestructiveEvent, DestructiveRequest]
        · rw [guards] at guardMember
          exact adapter_namespace_prefix_nondestructive adapter (.inr (.inr (.inl unlink))) event guardMember

-- §FS-host-boundary.ownership: The setup-error removal is authorized by its
-- SAME actual mkdir and nondestructive source suffix. It advances the joint
-- prefix for every actual return/error/loss without assuming a usable run.
theorem actual_run_setup_unlink_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (frames : ByteNamespaceFrameContract kernel semantics) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (environment : InterferenceContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (accounts : AccountContract kernel hostUid) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {foreignReferences : ForeignReferences} {currentNative : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    (joint : JointPublicationPrefix prior)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ tick :: trailing)
    (invocation : RunCreationPrefix adapter.occurrence.logicalBefore request none)
    (unlink : request.op = .unlinkAt) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
        foreignReferences (processed ++ [tick]) tick.after currentNative,
      next.custody.current.source.custody.catalogue = prior.custody.current.source.custody.catalogue ∧
      next.custody.current.source.custody.caps.family = prior.custody.current.source.custody.caps.family ∧
      JointPublicationPrefix next := by
  have selected : all[processed.length]? = some tick := by
    rw [whole, List.getElem?_append_right (by omega)]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  obtain ⟨source⟩ := actual_run_setup_removal descriptors lifetimes references environment journal selected present
    adapter invocation unlink
  have birthBefore : source.allocation.root.birthPosition < processed.length :=
    Nat.lt_trans source.allocation.root.earlier source.allocation.earlier.source.earlier
  have birthAt : processed[source.allocation.root.birthPosition]? = some source.allocation.root.birthTick := by
    simpa only [whole, List.getElem?_append_left birthBefore] using source.allocation.root.birthAt
  have sourceActor : source.allocation.root.use.actor = actor := source.allocation.root.sameActor.trans source.sameActor
  have sourcePresent : tick.before.actors source.allocation.root.use.actor = some engine := by
    rw [sourceActor]
    exact present
  obtain ⟨root, birth, sameTick, ordinal, member, owner, parent, name, bound, privateRoot, publicParent, owned⟩ :=
    registered_root_current_nondestructive lifetimes prior.custody birthAt source.allocation.root.use sourcePresent source.quiet
  have boundQuery : tick.before.shared.entries source.allocation.root.use.parent.object request.left = some root.object :=
    Eq.mpr (congrArg (fun selectedName => tick.before.shared.entries source.allocation.root.use.parent.object selectedName =
      some root.object) source.sameName) bound
  have parentPublic : prior.custody.current.source.custody.caps.family source.allocation.root.use.parent.object = none :=
    publicParent
  have comparison := registered_boundaries_exact prior.custody.current.source.custody.namespaceState.boundaries
    prior.custody.current.source.custody.names _ _ _ _ boundQuery privateRoot parentPublic
  have actual := selected_filesystem_step tick action present
  have component : Directories.component request.left = true := by
    exact (congrArg Directories.component source.sameName).trans source.allocation.root.use.component
  have change : DataChange dataObjects request (tick.before.project engine) tick.after.shared := by
    apply namespaceLaws.mutation _ _ _ _ actual (.inr (.inl unlink))
    · simpa only [ComponentRequest, unlink] using component
    · simp only [DirectoryOperands, unlink]
      exact ⟨source.allocation.root.use.parent, source.reference⟩
    · intro fd occurs handle live
      have sameFd : fd = request.first := by simpa only [Lookup.parents, unlink, List.mem_singleton] using occurs
      subst fd
      have same := Option.some.inj (live.symm.trans source.reference)
      subst handle
      exact comparison
  apply owned_unlink_publication_joint frames descriptors lifetimes references sdk accounts objects metadata lookup
    journal selected action present unlink source.reference component comparison change prior joint
  intro object scope binding label
  have sameObject : root.object = object := Option.some.inj (boundQuery.symm.trans binding)
  subst object
  have sameScope : root.object = scope := Option.some.inj (privateRoot.symm.trans label)
  exact sourceActor ▸ (sameScope ▸ owned)

end LeanCage.Host.Kernel
