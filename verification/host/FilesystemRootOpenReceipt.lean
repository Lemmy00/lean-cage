import FilesystemRunOpeningSource
import FilesystemStagingOpeningSource
import FilesystemPrimitiveRootOpening
import FilesystemHistoricalRoot

namespace LeanCage.Host.Kernel
open Filesystem

structure RootOpenReceipt {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (all : List (ActorTick runtime)) (tick : ActorTick runtime)
    (actor : ActorId) (engine : EngineState) (request : Request) (position : Nat) where
  birthPosition : Nat
  birthTick : ActorTick runtime
  birthAt : all[birthPosition]? = some birthTick
  earlier : birthPosition < position
  use : PrimitiveRootUse runtime initial all birthTick
  sameActor : use.actor = actor
  flags : request.second = directoryFlags
  sameName : request.left = use.request.left
  reference : engine.references request.first = some use.parent
  probes : ∀ event ∈ engine.events.drop (use.engine.events.length + 1), NamespacePassiveEvent event

private theorem temporary_open_requests :
    RequestProgram (fun request => request.op = .openAt → request = {
      op := .openAt, first := cwd, second := directoryFlags, left := "/tmp".toUTF8 })
      Directories.temporaryParent := by
  unfold Directories.temporaryParent
  apply RequestProgram.call (by intro invalid; cases invalid)
  intro reply
  dsimp only [Filesystem.Program.bind]
  split
  · exact .pure _
  · apply request_bind
    · unfold Directories.openAt
      apply RequestProgram.call (by intro _; rfl)
      intro reply
      split
      · exact .pure _
      · unfold Directories.inspect
        apply RequestProgram.call (by intro invalid; cases invalid)
        intro reply
        repeat' first
          | exact .pure _
          | split
          | exact RequestProgram.call (by intro invalid; cases invalid) (fun _ => .pure _)
    · intro value
      cases value <;> exact .pure _

-- §FS-host-boundary.ownership: A reserved-name reopen in the actual run/validator helper
-- derives its own earlier acknowledged mkdir and retained parent from the real source path.
-- No chosen root, parent role or private-region invariant is a premise.
theorem run_private_reopen_receipt {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (invocation : RunCreationPrefix adapter.occurrence.logicalBefore request none)
    (opening : request.op = .openAt) (reserved : PrivateNames.reservedBytes request.left = true) :
    Nonempty (RootOpenReceipt runtime initial all tick actor engine request position) := by
  obtain ⟨route⟩ := actual_run_directory_opening invocation.active opening
  cases route with
  | selecting active =>
    have operation := request_prefix temporary_open_requests active (request, none) (by simp) opening
    have name : request.left = "/tmp".toUTF8 := congrArg Request.left operation
    rw [name] at reserved
    exact Bool.noConfusion reserved
  | child container path uid selecting selectedParent inside active trace =>
    let context := invocation.context ++ selecting.map Program.filesystemEvent
    have sourceTrace : adapter.occurrence.logicalBefore = context ++ inside.map Program.filesystemPrefixEvent := by
      apply invocation.trace.trans
      have mapped := congrArg (fun events : List (Request × Option Reply) =>
        invocation.context ++ events.map Program.filesystemPrefixEvent) trace
      exact mapped.trans (by simp only [List.map_append, completed_filesystem_events, List.append_assoc, context])
    obtain ⟨receipt⟩ := primitive_new_child_reopen adapter uid container.fd PrivateNames.prefixText
      active sourceTrace opening
    have mkdir : receipt.made.op = .mkdirAt := by rw [receipt.madeExact]
    obtain ⟨earlier⟩ := receipt.source.selected journal selected present
    have earlierAction : earlier.tick.action.eventFor actor =
        some (Program.filesystemPrefixEvent (receipt.made, some receipt.child.made)) := by
      simp only [earlier.action, ActorAction.eventFor, ↓reduceIte, Program.filesystemPrefixEvent]
    obtain ⟨earlierAdapter, exactOccurrence⟩ := actual_primitive_adapter_from_source descriptors lifetimes
      references environment journal earlier.selected earlierAction earlier.present earlier.occurrence
    have exactContext : earlierAdapter.occurrence.logicalBefore = receipt.source.context :=
      congrArg (fun value => value.logicalBefore) exactOccurrence
    have sourceContext : earlierAdapter.occurrence.logicalBefore = invocation.context ++
        selecting.map Program.filesystemEvent ++ receipt.child.randomEvents.map Program.filesystemEvent :=
      exactContext.trans receipt.sourceContext
    have actualInvocation := run_root_mkdir_invocation container path uid selectedParent receipt.child invocation.context
    have sameCall : (earlierAdapter.occurrence.logicalBefore, receipt.made) =
        (invocation.context ++ selecting.map Program.filesystemEvent ++
          receipt.child.randomEvents.map Program.filesystemEvent, {
            op := .mkdirAt, first := container.fd, second := 448,
            left := (PrivateNames.prefixText ++ Snapshot.hex receipt.child.random).toUTF8 }) :=
      Prod.ext sourceContext receipt.madeExact
    have earlierInvocation : RunCreationPrefix earlierAdapter.occurrence.logicalBefore receipt.made none :=
      Eq.mp (congrArg (fun call : List Program.Event × Request => RunCreationPrefix call.1 call.2 none) sameCall).symm actualInvocation
    obtain ⟨parentSource⟩ := primitive_run_parent_observations earlierAdapter earlierInvocation mkdir
    obtain ⟨parent, parentBefore, raw⟩ := primitive_run_parent_reference descriptors parentSource
    have atMade : receipt.source.observation.before.handles receipt.made.first = some parent := by
      rw [earlier.before]
      exact parentBefore
    have parentCurrent := receipt.source.parent_current descriptors mkdir atMade
    let use : PrimitiveRootUse runtime initial all earlier.tick := {
      actor
      engine := earlier.input
      request := receipt.made
      reply := receipt.child.made
      action := earlierAction
      present := earlier.present
      mkdir
      component := by rw [receipt.madeExact]; exact receipt.child.component
      parent
      reference := parentBefore
      accepted := receipt.child.acknowledged
      adapter := earlierAdapter
      invocation := .inl ⟨earlierInvocation⟩ }
    refine ⟨{
      birthPosition := earlier.position
      birthTick := earlier.tick
      birthAt := earlier.selected
      earlier := earlier.earlier
      use
      sameActor := rfl
      flags := congrArg Request.second receipt.child.operation
      sameName := (congrArg Request.left receipt.child.operation).trans
        (congrArg Request.left receipt.madeExact).symm
      reference := ?_
      probes := earlier.probes }⟩
    change engine.references request.first = some parent
    have sameFD : request.first = receipt.made.first :=
      (congrArg Request.first receipt.child.operation).trans (congrArg Request.first receipt.madeExact).symm
    rw [sameFD]
    exact parentCurrent

-- §FS-host-boundary.publication: The stage's reserved-name reopen likewise keeps the
-- exact publisher selection, dot alias and earlier real mkdir of this invocation.
theorem staging_private_reopen_receipt {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (call : StagingOpeningCall adapter.occurrence.logicalBefore request)
    (opening : request.op = .openAt) (reserved : PrivateNames.reservedBytes request.left = true) :
    Nonempty (RootOpenReceipt runtime initial all tick actor engine request position) := by
  obtain ⟨route⟩ := actual_fresh_opening call.selection.parent call.active opening
  cases route with
  | alias empty operation =>
    rw [operation] at reserved
    exact Bool.noConfusion reserved
  | child container openingEvents opened inside active trace =>
    obtain ⟨child⟩ := actual_new_child_opening call.selection.parent.uid container.fd
      PrivateNames.prefixText active opening
    let made : Request := {
      op := .mkdirAt
      first := container.fd
      second := 448
      left := (PrivateNames.prefixText ++ Snapshot.hex child.random).toUTF8 }
    let context := call.context ++ (call.source.identifying ++ call.source.selecting ++
      call.selection.displaying ++ call.selection.selecting ++ openingEvents ++ child.randomEvents).map Program.filesystemEvent
    have logical : adapter.occurrence.logicalBefore = context ++ [.returned (.filesystem made) child.made] := by
      have outer := congrArg (fun events : List (Request × Option Reply) => call.context ++
        (call.source.identifying ++ call.source.selecting ++ call.selection.displaying ++
          call.selection.selecting).map Program.filesystemEvent ++ events.map Program.filesystemPrefixEvent) trace
      have inner := congrArg (fun events : List (Request × Option Reply) => call.context ++
        (call.source.identifying ++ call.source.selecting ++ call.selection.displaying ++
          call.selection.selecting).map Program.filesystemEvent ++
          (Publication.completed openingEvents ++ events).map Program.filesystemPrefixEvent) child.trace
      exact call.source_trace.trans (outer.trans (inner.trans (by
        simp only [context, made, List.map_append, completed_filesystem_events, List.map_cons, List.map_nil,
          Program.filesystemPrefixEvent, List.append_assoc])))
    obtain ⟨source, sourceContext⟩ := primitive_mkdir_before_open_exact adapter logical rfl child.acknowledged.1 opening
    obtain ⟨earlier⟩ := source.selected journal selected present
    have earlierAction : earlier.tick.action.eventFor actor =
        some (Program.filesystemPrefixEvent (made, some child.made)) := by
      simp only [earlier.action, ActorAction.eventFor, ↓reduceIte, Program.filesystemPrefixEvent]
    obtain ⟨earlierAdapter, exactOccurrence⟩ := actual_primitive_adapter_from_source descriptors lifetimes
      references environment journal earlier.selected earlierAction earlier.present earlier.occurrence
    have exactContext : earlierAdapter.occurrence.logicalBefore = source.context :=
      congrArg (fun value => value.logicalBefore) exactOccurrence
    have earlierCall : StagingCall earlierAdapter.occurrence.logicalBefore made := by
      have actualCall := call.mkdir_source container openingEvents opened child
      exact (exactContext.trans sourceContext).symm ▸ actualCall
    obtain ⟨parentSource⟩ := primitive_staging_parent descriptors aliases earlierAdapter earlierCall rfl
    have parentBefore : earlier.input.references made.first = some parentSource.container.handle := by
      have sameFD := congrArg Request.first parentSource.source.child.child.operation
      change (earlier.tick.before.project earlier.input).handles made.first = some parentSource.container.handle
      rw [sameFD]
      exact parentSource.container.live
    have atMade : source.observation.before.handles made.first = some parentSource.container.handle := by
      rw [earlier.before]
      exact parentBefore
    have parentCurrent := source.parent_current descriptors rfl atMade
    let use : PrimitiveRootUse runtime initial all earlier.tick := {
      actor
      engine := earlier.input
      request := made
      reply := child.made
      action := earlierAction
      present := earlier.present
      mkdir := rfl
      component := child.component
      parent := parentSource.container.handle
      reference := parentBefore
      accepted := child.acknowledged
      adapter := earlierAdapter
      invocation := .inr ⟨earlierCall⟩ }
    refine ⟨{
      birthPosition := earlier.position
      birthTick := earlier.tick
      birthAt := earlier.selected
      earlier := earlier.earlier
      use
      sameActor := rfl
      flags := congrArg Request.second child.operation
      sameName := by
        change request.left = (PrivateNames.prefixText ++ Snapshot.hex child.random).toUTF8
        exact congrArg Request.left child.operation
      reference := ?_
      probes := earlier.probes }⟩
    change engine.references request.first = some parentSource.container.handle
    rw [congrArg Request.first child.operation]
    exact parentCurrent

-- §FS-host-boundary.ownership: Connect that exact source receipt to the constructed
-- registry at a later point. The actual open descriptor denotes its own recorded birth.
theorem RootOpenReceipt.opened_root {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (mounts : MountContract kernel initial.allocated)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {population : Population} {native : NativeProcesses}
    (state : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed population native)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ trailing)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request}
    (receipt : RootOpenReceipt runtime initial all tick actor engine request position)
    (selected : processed[position]? = some tick) (present : tick.before.actors actor = some engine)
    {reply : Reply} {fd : UInt64}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, some reply)))
    (opening : request.op = .openAt) (recognized : descriptor reply = some fd) :
    ∃ (root : PrivateRoot) (birth : RootBirth runtime all root),
      birth.tick = receipt.birthTick ∧ birth.position = receipt.birthPosition ∧
      Sigma.mk root birth ∈ state.current.source.custody.catalogue ∧ root.actor = actor ∧
      ∃ handle, tick.after.shared.handles fd = some handle ∧ handle.object = root.object ∧ handle.rawOwned = true := by
  obtain ⟨inBounds, atPosition⟩ := List.getElem?_eq_some_iff.mp selected
  have birthAt : processed[receipt.birthPosition]? = some receipt.birthTick := by
    have earlier : receipt.birthPosition < processed.length := Nat.lt_trans receipt.earlier inBounds
    simpa only [whole, List.getElem?_append_left earlier] using receipt.birthAt
  have quiet : ∀ event ∈ engine.events.drop (receipt.use.engine.events.length + 1), NondestructiveEvent event := by
    intro event member
    have passive := receipt.probes event member
    cases event with
    | @returned β effect reply =>
      cases effect <;> dsimp only [NondestructiveEvent] <;> first
        | exact namespace_passive_not_destructive passive
        | exact True.intro
    | @lost β effect =>
      cases effect <;> dsimp only [NondestructiveEvent] <;> first
        | exact namespace_passive_not_destructive passive
        | exact True.intro
  obtain ⟨root, birth, current, ordinal, member, owner, parent, name, handle, live, identity, raw⟩ :=
    registered_root_handle_at descriptors lifetimes mounts journal state birthAt receipt.use selected receipt.earlier
      (by rwa [receipt.sameActor]) (by rwa [receipt.sameActor]) opening receipt.flags receipt.sameName
      receipt.reference recognized quiet
  exact ⟨root, birth, current, ordinal, member, owner.trans receipt.sameActor, handle, live, identity, raw⟩

end LeanCage.Host.Kernel
