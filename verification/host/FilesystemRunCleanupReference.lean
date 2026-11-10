import FilesystemRunReference
import RunDirectoryProofs.CleanupFrontier
import FilesystemOutputSources.Application
import FilesystemSourceNondestructive
import FilesystemPublicationContentProfile

namespace LeanCage.Host.Kernel
open Filesystem

private theorem script_returns (replies : List (Request × Reply)) :
    Returns (callScript (replies.map Prod.fst)) replies () := by
  induction replies with
  | nil => exact .pure ()
  | cons head tail ih => exact .call head.1 (fun _ => callScript (tail.map Prod.fst)) head.2 tail () ih

private theorem kept_guard_borrow {kernel : Contract} (descriptors : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (request : Request) (keeps : KeepsReference held request) :
    BorrowPost kernel held handle (fun _ => True) (guardedCall request) := by
  by_cases allocating : AllocatesDescriptor request.op
  · exact borrow_weaken (guarded_open_fresh_borrow descriptors held handle request allocating) (fun _ _ => True.intro)
  · by_cases closing : request.op = .close
    · have identity : guardedCall request = Filesystem.Program.effect request := by
        cases request with
        | mk op first second third left right => cases closing; rfl
      rw [identity]
      apply BorrowPost.call
      · intro before after observed actual live
        rw [descriptors.close_other _ _ _ _ _ actual closing (keeps.2 closing)]
        exact live
      · intro before after reply actual live
        exact .pure True.intro
    · apply guarded_passive_borrow descriptors held handle request
      exact ⟨fun h => allocating (.inl h), fun h => allocating (.inr (.inl h)),
        fun h => allocating (.inr (.inr h)), closing, keeps.1⟩

private theorem kept_script_borrow {kernel : Contract} (descriptors : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (requests : List Request)
    (keeps : ∀ request ∈ requests, KeepsReference held request) :
    BorrowPost kernel held handle (fun _ => True) (callScript requests).lower := by
  induction requests with
  | nil => exact .pure True.intro
  | cons request rest ih =>
    change BorrowPost kernel held handle (fun _ => True)
      ((guardedCall request).bind (fun _ => (callScript rest).lower))
    apply borrow_bind (kept_guard_borrow descriptors held handle request (keeps request (by simp)))
    intro reply _
    exact ih (by intro request member; exact keeps request (List.mem_cons_of_mem _ member))

private theorem map_nondestructive {events : List (Request × Reply)}
    (source : ∀ event ∈ events, ¬ DestructiveRequest event.1) :
    ∀ event ∈ events.map Program.filesystemEvent, NondestructiveEvent event := by
  intro event member
  obtain ⟨pair, occurs, rfl⟩ := List.mem_map.mp member
  exact source pair occurs

private theorem runtime_nondestructive {α : Type} {program : Program α} {events : List Program.Event} {value : α}
    (source : Program.RuntimeOnly program) (returned : Program.Returns program events value) :
    ∀ event ∈ events, NondestructiveEvent event := by
  intro event member
  have allowed := Program.runtime_only_prefix source (Program.returns_prefix returned) event member
  cases event with
  | returned effect reply => cases effect <;> first | exact True.intro | exact False.elim allowed
  | lost effect => cases effect <;> first | exact True.intro | exact False.elim allowed

private theorem returned_member_prefix {α : Type} {program : Program α} {events : List Program.Event} {value : α}
    (returned : Program.Returns program events value) {event : Program.Event} (member : event ∈ events) :
    ∃ before, Program.Prefix program (before ++ [event]) := by
  induction returned with
  | pure => cases member
  | call effect next reply tail value rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨[], .returned effect next reply [] (.empty _)⟩
    · obtain ⟨before, prefixSource⟩ := ih member
      exact ⟨.returned effect reply :: before, .returned effect next reply _ prefixSource⟩

private theorem dispatch_nondestructive {caller : GatewayWire.Request} {bundle : Validation.Bundle} {duration : Option Nat}
    (context : RunPrefixCuts.Dispatched caller bundle duration) :
    ∀ event ∈ context.dispatching, NondestructiveEvent event := by
  intro event member
  obtain ⟨before, source⟩ := returned_member_prefix context.dispatch member
  cases event with
  | returned effect reply =>
    cases effect with
    | filesystem request =>
      exact namespace_passive_not_destructive (dispatch_namespace_passive
        (observed := some reply) _ _ _ _ _ _ _ _ source)
    | spawn | read | wait | terminate | tryWait | descriptor => exact True.intro

  | lost effect =>
    cases effect with
    | filesystem request =>
      exact namespace_passive_not_destructive (dispatch_namespace_passive
        (observed := none) _ _ _ _ _ _ _ _ source)
    | spawn | read | wait | terminate | tryWait | descriptor => exact True.intro

private theorem returns_discard {α : Type} {program : Program α} {events : List Program.Event} {value : α}
    (source : Program.Returns program events value) :
    Program.Returns (do let _ ← program; pure ()) events () := by
  induction source with
  | pure => exact .pure ()
  | call effect next reply rest value continued ih => exact .call effect _ reply rest () ih

private theorem image_nondestructive (fd : UInt64) (bundle : Validation.Bundle) (overlay : List Image.Entry) :
    RequestProgram (fun request => ¬ DestructiveRequest request) (Image.create fd bundle overlay) := by
  unfold Image.create
  split
  · exact .pure _
  · apply request_bind (request_weaken (read_only_namespace_passive (Image.copyIdentified_readOnly _ _ _))
      (fun _ => namespace_passive_not_destructive))
    intro base
    cases base with
    | error => exact .pure _
    | ok base =>
      apply RequestProgram.call (by simp [DestructiveRequest])
      intro reply
      dsimp only [Filesystem.Program.bind]
      split
      · exact .pure _
      · apply request_weaken (Image.contentClose_requests _ _ _)
        intro operation role
        rcases role with writing | closing
        · simp only [DestructiveRequest, writing.1]
          decide
        · simp only [DestructiveRequest, closing]
          decide

private theorem quiet_no_rename {event : Program.Event} (quiet : NondestructiveEvent event) :
    RequestEvent (fun request => request.op ≠ .renameNew) event := by
  cases event with
  | returned effect reply =>
    cases effect with
    | filesystem => exact fun moving => quiet (.inr moving)
    | spawn | read | wait | terminate | tryWait | descriptor => exact True.intro
  | lost effect =>
    cases effect with
    | filesystem => exact fun moving => quiet (.inr moving)
    | spawn | read | wait | terminate | tryWait | descriptor => exact True.intro

structure RunCleanupParent {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (all : List (ActorTick runtime)) (actor : ActorId) (events : List Program.Event)
    (outside : List Program.Event)
    (created : List (Request × Reply)) (run : RunDirectory.Owned) (work : List Program.Event)
    (inside : List (Request × Option Reply)) (request : Request) (guardOrdinal limit : Nat) (current : World) where
  allocation : CreatedRunContinuation runtime initial all outside created run
    (work ++ inside.map Program.filesystemPrefixEvent) limit current
  point : RunAllocationPoint allocation
  sameActor : allocation.earlier.source.inputActor = actor
  eventTrace : events = allocation.earlier.source.input.events ++
    .returned (.filesystem allocation.opening.request) allocation.opening.reply ::
      (allocation.earlier.post.map Program.filesystemEvent ++ allocation.earlier.remaining ++ allocation.earlier.guards)
  noPublication : ∀ event ∈ work ++ inside.map Program.filesystemPrefixEvent,
    RequestEvent (fun request => request.op ≠ .renameNew) event
  workQuiet : ∀ event ∈ work, NondestructiveEvent event
  guardsQuiet : ∀ event ∈ allocation.earlier.guards, NondestructiveEvent event
  statBeforeGuard : point.observation.sample.ordinal < guardOrdinal
  component : Directories.component request.left = true
  workProgram : Program Unit
  worked : Program.Returns workProgram work ()
  workBorrows : ∀ who held handle, handle.rawOwned = true →
    ActorBorrowPost runtime who held handle (fun _ => True) (PrimitiveFilesystem.lower workProgram)
  cleanupSource : Prefix (RunDirectory.cleanup run) (inside ++ [(request, none)])
  handle : Handle
  reference : current.handles request.first = some handle
  origin : (request.first = run.directory.fd ∧ handle = allocation.earlier.source.opening.handle) ∨
    (request.first = run.container.fd ∧ handle = allocation.root.use.parent)

-- §FS-host-boundary.ownership: The selected cleanup call uses either its own
-- original run handle or its retained original container. Earlier source
-- writes/runtime observations and all raw guards are replayed on the SAME cut.
private theorem actual_cleanup_parent {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} (present : tick.before.actors actor = some engine)
    {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {outside : List Program.Event} {created : List (Request × Reply)} {run : RunDirectory.Owned}
    (creation : Returns RunDirectory.create created (.ok run))
    {α : Type} {program : Program α} {work : List Program.Event} {value : α}
    (worked : Program.Returns program work value)
    (workBorrows : ∀ who held handle, handle.rawOwned = true →
      ActorBorrowPost runtime who held handle (fun _ => True) (PrimitiveFilesystem.lower program))
    (workQuiet : ∀ event ∈ work, NondestructiveEvent event)
    {inside : List (Request × Option Reply)}
    (active : Prefix (RunDirectory.cleanup run) (inside ++ [(request, none)]))
    (trace : adapter.occurrence.logicalBefore = outside ++ created.map Program.filesystemEvent ++
      work ++ inside.map Program.filesystemPrefixEvent)
    (unlink : request.op = .unlinkAt) :
    Nonempty (RunCleanupParent runtime initial all actor engine.events outside created run work inside request
      adapter.occurrence.rawBefore.length position (tick.before.project engine)) := by
  obtain ⟨allocation, sameActor, sameGuards, eventTrace⟩ := primitive_created_run_continuation descriptors lifetimes
    references environment journal selected present adapter creation (by simpa only [List.append_assoc] using trace)
  obtain ⟨point⟩ := allocation.allocation descriptors
  obtain ⟨cleanup⟩ := cleanup_frontier active
  have keeps := cleanup.keeps_parent point.distinct unlink
  have sourceReplies : Program.Returns (Program.liftFilesystem (callScript (cleanup.replies.map Prod.fst)))
      (inside.map Program.filesystemPrefixEvent) () := by
    have mapped : inside.map Program.filesystemPrefixEvent = cleanup.replies.map Program.filesystemEvent :=
      (congrArg (List.map Program.filesystemPrefixEvent) cleanup.trace).trans (completed_filesystem_events _)
    exact Eq.mpr (congrArg (fun events => Program.Returns
      (Program.liftFilesystem (callScript (cleanup.replies.map Prod.fst))) events ()) mapped)
      (Program.lift_filesystem_returns (script_returns cleanup.replies))
  have workedSource : Program.Returns (program.bind (fun _ => Program.liftFilesystem
      (callScript (cleanup.replies.map Prod.fst)))) (work ++ inside.map Program.filesystemPrefixEvent) () :=
    Program.returns_bind worked sourceReplies
  have guards : ∀ event ∈ allocation.earlier.guards, RetainingEvent event := by
    rw [sameGuards]
    exact adapter_namespace_prefix_retaining adapter (.inr (.inr (.inl unlink)))
  have guardsQuiet : ∀ event ∈ allocation.earlier.guards, NondestructiveEvent event := by
    rw [sameGuards]
    exact adapter_namespace_prefix_nondestructive adapter (.inr (.inr (.inl unlink)))
  have statBeforeGuard : point.observation.sample.ordinal < adapter.occurrence.rawBefore.length := by
    have observed := point.observation.earlier
    have firstCount := congrArg List.length eventTrace
    have insideCount := congrArg List.length point.trace
    have rawCount := congrArg List.length adapter.occurrence.trace
    have guardCount := congrArg List.length sameGuards
    simp only [List.length_append, List.length_cons, List.length_map] at firstCount insideCount rawCount guardCount observed
    omega
  have retain (held : UInt64) (handle : Handle) (raw : handle.rawOwned = true)
      (live : point.world.handles held = some handle) (sameFD : held = request.first) :
      (tick.before.project engine).handles held = some handle := by
    apply point.after_kept_returns descriptors held handle live workedSource ?_ guards
    apply Lowered.actor_bind (workBorrows _ _ _ raw)
    intro result _
    apply Lowered.actor_filesystem
    apply kept_script_borrow descriptors held handle
    intro operation member
    obtain ⟨reply, occurs, identity⟩ := List.mem_map.mp member
    subst operation
    rw [sameFD]
    exact keeps reply occurs
  have currentRole := RunDirectory.cleanup_request_prefix run active (request, none) (by simp)
  have noPublication : ∀ event ∈ work ++ inside.map Program.filesystemPrefixEvent,
      RequestEvent (fun request => request.op ≠ .renameNew) event := by
    intro event member
    rcases List.mem_append.mp member with worked | cleaning
    · exact quiet_no_rename (workQuiet event worked)
    · obtain ⟨pair, occurs, rfl⟩ := List.mem_map.mp cleaning
      have notMoving := request_prefix (run_cleanup_no_rename run) active pair (List.mem_append_left _ occurs)
      rcases pair with ⟨query, reply⟩
      cases reply <;> exact notMoving
  let construct (component : Directories.component request.left = true) (handle : Handle)
      (reference : (tick.before.project engine).handles request.first = some handle)
      (origin : (request.first = run.directory.fd ∧ handle = allocation.earlier.source.opening.handle) ∨
        (request.first = run.container.fd ∧ handle = allocation.root.use.parent)) :
      RunCleanupParent runtime initial all actor engine.events outside created run work inside request
        adapter.occurrence.rawBefore.length position (tick.before.project engine) := {
    allocation
    point
    sameActor
    eventTrace
    noPublication
    workQuiet
    guardsQuiet
    statBeforeGuard
    component
    workProgram := do let _ ← program; pure ()
    worked := returns_discard worked
    workBorrows := by
      intro who held handle raw
      apply Lowered.actor_bind (workBorrows who held handle raw)
      intro result _
      exact .pure True.intro
    cleanupSource := active
    handle
    reference
    origin }
  unfold RunDirectory.CleanupRequest at currentRole
  rw [unlink] at currentRole
  rcases currentRole with child | root
  · have component : Directories.component request.left = true := by
      have names := child.2.2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at names
      rcases names with same | same | same
      · rw [same]
        change Directories.component (ByteArray.mk #[114, 101, 113, 117, 101, 115, 116, 46, 99, 112, 105, 111]) = true
        simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem]
      · rw [same]
        change Directories.component (ByteArray.mk #[99, 111, 110, 116, 114, 111, 108, 46, 115, 111, 99, 107]) = true
        simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem]
      · rw [same]
        change Directories.component (ByteArray.mk #[112, 111, 108, 105, 99, 121, 46, 106, 115, 111, 110]) = true
        simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem]
    exact ⟨construct component allocation.earlier.source.opening.handle
      (child.1.symm ▸ retain _ _ point.directoryRaw point.directory child.1.symm) (.inl ⟨child.1, rfl⟩)⟩
  · have component : Directories.component request.left = true := by
      have name : run.name = allocation.root.use.request.left :=
        (congrArg Request.left allocation.opening.operation).symm.trans allocation.root.sameName
      rw [root.2.2, name]
      exact allocation.root.use.component
    exact ⟨construct component allocation.root.use.parent
      (root.1.symm ▸ retain _ _ point.containerRaw point.container root.1.symm) (.inr ⟨root.1, rfl⟩)⟩

theorem actual_validator_failed_write_cleanup_parent {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} (present : tick.before.actors actor = some engine)
    {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (raw : ByteArray) (context : ValidatorPrefixCuts.Allocated)
    {writing : List (Request × Reply)} {error : Failure}
    (written : Returns (context.writeProgram raw) writing (.error error))
    {outside inside : List Program.Event}
    (active : Program.Prefix (Program.liftFilesystem (RunDirectory.cleanup context.directory))
      (inside ++ [Program.filesystemPrefixEvent (request, none)]))
    (trace : adapter.occurrence.logicalBefore = outside ++ context.events ++ writing.map Program.filesystemEvent ++ inside)
    (unlink : request.op = .unlinkAt) :
    ∃ selectedInside, inside = selectedInside.map Program.filesystemPrefixEvent ∧
      Nonempty (RunCleanupParent runtime initial all actor engine.events outside context.allocating context.directory
        (writing.map Program.filesystemEvent) selectedInside request adapter.occurrence.rawBefore.length
        position (tick.before.project engine)) := by
  obtain ⟨selectedInside, source, insideTrace⟩ := selected_filesystem_source active
  refine ⟨selectedInside, insideTrace, ?_⟩
  apply actual_cleanup_parent descriptors lifetimes references environment journal selected present adapter
    context.allocate (Program.lift_filesystem_returns written) ?_ ?_ source ?_ unlink
  · intro who held handle _
    exact Lowered.actor_filesystem who (Lowered.writeNew_borrow descriptors held handle _ _ _ _)
  · exact map_nondestructive (requests_returned (writeNew_nondestructive _ _ _ _) written)
  · simpa only [ValidatorPrefixCuts.Allocated.events, insideTrace] using trace

private def validator_work (bundle : Validation.Bundle) (raw : ByteArray) (run : RunDirectory.Owned) : Program Unit := do
  let _ ← Program.liftFilesystem (writeNew run.directory.fd "policy.json".toUTF8 raw)
  let child ← Program.effect (.spawn (Validation.validatorArguments bundle (run.path ++ "/policy.json")))
  let _ ← Validation.observeChild raw child
  pure ()

private theorem validator_work_source (bundle : Validation.Bundle) (raw : ByteArray)
    (context : ValidatorPrefixCuts.Observed bundle raw) :
    Program.Returns (validator_work bundle raw context.spawned.written.allocated.directory)
      (context.spawned.written.writing.map Program.filesystemEvent ++ context.spawned.spawning ++ context.observing) () := by
  unfold validator_work
  rw [List.append_assoc]
  apply Program.returns_bind (Program.lift_filesystem_returns context.spawned.written.write)
  apply Program.returns_bind context.spawned.spawn
  exact returns_discard context.observe

private theorem validator_work_borrow {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (rawHandle : handle.rawOwned = true)
    (bundle : Validation.Bundle) (raw : ByteArray) (run : RunDirectory.Owned) :
    ActorBorrowPost runtime actor held handle (fun _ => True)
      (PrimitiveFilesystem.lower (validator_work bundle raw run)) := by
  unfold validator_work
  apply Lowered.actor_bind (Lowered.actor_filesystem actor (Lowered.writeNew_borrow descriptors held handle _ _ _ _))
  intro result _
  apply Lowered.actor_bind (runtime_only_borrow sdk actor held handle rawHandle
    (.call (.spawn _) _ (by trivial) (fun _ => .pure _)))
  intro child _
  apply Lowered.actor_bind (runtime_only_borrow sdk actor held handle rawHandle
    (observe_child_runtime_only raw child))
  intro result _
  exact .pure True.intro

-- §FS-host-boundary.ownership: The source supplies the actual completed
-- write/spawn/read/wait prefix. Each parent-runtime step retains the run's
-- raw references; successful reaping is retained separately, never inferred.
theorem actual_validator_observed_cleanup_parent {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    (sdk : RuntimeDescriptorContract runtime)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} (present : tick.before.actors actor = some engine)
    {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {bundle : Validation.Bundle} {raw : ByteArray} (context : ValidatorPrefixCuts.Observed bundle raw)
    {outside inside : List Program.Event}
    (active : Program.Prefix (Program.liftFilesystem
      (RunDirectory.cleanup context.spawned.written.allocated.directory))
      (inside ++ [Program.filesystemPrefixEvent (request, none)]))
    (trace : adapter.occurrence.logicalBefore = outside ++ context.events ++ inside)
    (unlink : request.op = .unlinkAt) :
    ∃ selectedInside, inside = selectedInside.map Program.filesystemPrefixEvent ∧
      Nonempty (RunCleanupParent runtime initial all actor engine.events outside context.spawned.written.allocated.allocating
        context.spawned.written.allocated.directory
        (context.spawned.written.writing.map Program.filesystemEvent ++ context.spawned.spawning ++ context.observing)
        selectedInside request adapter.occurrence.rawBefore.length position (tick.before.project engine)) := by
  obtain ⟨selectedInside, source, insideTrace⟩ := selected_filesystem_source active
  refine ⟨selectedInside, insideTrace, ?_⟩
  apply actual_cleanup_parent descriptors lifetimes references environment journal selected present adapter
    context.spawned.written.allocated.allocate (validator_work_source bundle raw context)
    (fun who held handle rawHandle => validator_work_borrow descriptors sdk who held handle rawHandle bundle raw _) ?_ source ?_ unlink
  · intro event member
    rcases List.mem_append.mp member with before | observing
    · rcases List.mem_append.mp before with writing | spawning
      · exact map_nondestructive (requests_returned
          (writeNew_nondestructive _ _ _ _) context.spawned.written.write) event writing
      · exact runtime_nondestructive (.call (.spawn _) _ (by trivial) (fun _ => .pure _)) context.spawned.spawn event spawning
    · exact runtime_nondestructive (observe_child_runtime_only raw context.spawned.child) context.observe event observing
  ·
    simpa only [ValidatorPrefixCuts.Observed.events, ValidatorPrefixCuts.Spawned.events,
      ValidatorPrefixCuts.Written.events, ValidatorPrefixCuts.Allocated.events, insideTrace, List.append_assoc] using trace

private def vm_work (caller : GatewayWire.Request) (bundle : Validation.Bundle) (duration : Option Nat)
    (context : RunPrefixCuts.Allocated caller bundle duration) : Program Publication.Input := do
  let image ← Program.liftFilesystem context.imageProgram
  dispatchImage (Snapshot.hex context.setup.random) bundle (caller.command == GatewayWire.checkCommand)
    context.setup.policy context.directory context.setup.duration context.setup.transport image

private theorem vm_work_source {caller : GatewayWire.Request} {bundle : Validation.Bundle} {duration : Option Nat}
    (context : RunPrefixCuts.Dispatched caller bundle duration) :
    Program.Returns (vm_work caller bundle duration context.imaged.allocated)
      (context.imaged.imaging.map Program.filesystemEvent ++ context.dispatching) context.input := by
  unfold vm_work
  exact Program.returns_bind (Program.lift_filesystem_returns context.imaged.archive) context.dispatch

private theorem vm_work_borrow {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (rawHandle : handle.rawOwned = true)
    (caller : GatewayWire.Request) (bundle : Validation.Bundle) (duration : Option Nat)
    (context : RunPrefixCuts.Allocated caller bundle duration) :
    ActorBorrowPost runtime actor held handle (fun _ => True)
      (PrimitiveFilesystem.lower (vm_work caller bundle duration context)) := by
  unfold vm_work
  apply Lowered.actor_bind (Lowered.actor_filesystem actor (Lowered.image_create_borrow descriptors held handle _ _ _))
  intro image _
  exact Lowered.dispatch_image_borrow descriptors sdk actor held handle rawHandle _ _ _ _ _ _ _ image

-- §FS-host-boundary.ownership: VM cleanup uses the SAME actual run allocation,
-- image source and dispatch result. Per-child liveness/reaping stays on its
-- separate exact-token journal; no descendant cleanup is assumed here.
theorem actual_vm_cleanup_parent {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    (sdk : RuntimeDescriptorContract runtime)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} (present : tick.before.actors actor = some engine)
    {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {caller : GatewayWire.Request} {bundle : Validation.Bundle} {duration : Option Nat}
    (context : RunPrefixCuts.Dispatched caller bundle duration) {outside inside : List Program.Event}
    (active : Program.Prefix (Program.liftFilesystem (RunDirectory.cleanup context.imaged.allocated.directory))
      (inside ++ [Program.filesystemPrefixEvent (request, none)]))
    (trace : adapter.occurrence.logicalBefore = outside ++ context.events ++ inside)
    (unlink : request.op = .unlinkAt) :
    ∃ selectedInside, inside = selectedInside.map Program.filesystemPrefixEvent ∧
      Nonempty (RunCleanupParent runtime initial all actor engine.events (outside ++ context.imaged.allocated.setup.events)
        context.imaged.allocated.allocating context.imaged.allocated.directory
        (context.imaged.imaging.map Program.filesystemEvent ++ context.dispatching)
        selectedInside request adapter.occurrence.rawBefore.length position (tick.before.project engine)) := by
  obtain ⟨selectedInside, source, insideTrace⟩ := selected_filesystem_source active
  refine ⟨selectedInside, insideTrace, ?_⟩
  apply actual_cleanup_parent descriptors lifetimes references environment journal selected present adapter
    context.imaged.allocated.allocate (vm_work_source context)
    (fun who held handle rawHandle => vm_work_borrow descriptors sdk who held handle rawHandle caller bundle duration _) ?_ source ?_ unlink
  · intro event member
    rcases List.mem_append.mp member with imaging | dispatching
    · exact map_nondestructive (requests_returned (image_nondestructive _ _ _) context.imaged.archive) event imaging
    · exact dispatch_nondestructive context event dispatching
  · simpa only [RunPrefixCuts.Dispatched.events, RunPrefixCuts.Imaged.events,
      RunPrefixCuts.Allocated.events, insideTrace, List.append_assoc] using trace

end LeanCage.Host.Kernel
