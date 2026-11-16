import FilesystemCommitGuarantee
import FilesystemJointMkdirs
import FilesystemJointUnlinks
import FilesystemJointExclusives
import FilesystemAnchorHistory
import FilesystemRecordedBackend
import FilesystemCustodyCuts
import FilesystemBootstrapManifest
import FilesystemInstalledEngine
import GatewayResponseWriterPrefix
import CallerProofs
import SnapshotProofs
import PublicationProofs.Cuts
import PublicationProofs.Reporting
import RetrievalProofs.ReadOnly
import RetrievalProofs.Justification

-- §AR-host-boundary.acceptance.engine: The final M5.2 statement and its closing statements.
-- §DA-host-delivery.engine: Its premises are exactly these; every other fact is a conclusion.
-- Definitions and statement plumbing only; no open closing statement is proved here.

namespace LeanCage.Host.EngineGuarantee
open Kernel Filesystem PrivateStreams

-- Premises

-- §DA-host-delivery.engine: Platform premise, the individual operation contracts of
-- §AR-host-boundary.primitives. No field describes a complete helper, caller or callback.
structure Platform {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (child : ChildPrimitive kernel) (native : NativePrimitive kernel) (hostUid : Nat)
    (semantics : NameSemanticsView) (dataObjects directories : ObjectId → Prop)
    (sha256 : ByteArray → ByteArray) (hmac : ByteArray → ByteArray → ByteArray)
    (initial : World) where
  crypto : CryptographicContract kernel sha256 hmac
  namespaceLaws : ByteNamespaceContract kernel semantics dataObjects
  namespaceFrames : NamespaceContract kernel
  descriptors : DescriptorContract kernel
  aliases : DirectoryAliasContract kernel
  lifetimes : LifetimeContract runtime
  references : ReferenceContract runtime
  environment : InterferenceContract kernel
  raw : RawReferenceLifetimeContract kernel
  sdk : RuntimeDescriptorContract runtime
  accounts : AccountContract kernel hostUid
  objects : ObjectLifetimeContract runtime
  liveMetadata : LiveMetadataContract runtime child
  metadata : GlobalAuthorityContract runtime child
  nativeMetadata : NativeMetadataContract native
  attributes : ExistingAttributeContract runtime child
  foreign : ForeignContract runtime
  nativeAttributes : NativeExistingAttributeContract native
  lookup : LookupMutationContract (runtime := runtime) child native
  probes : LookupPrimitiveContract kernel.step kernel.interference semantics
  types : CreationTypeContract kernel directories
  targets : OpenTargetContract kernel semantics initial.allocated dataObjects
  mounts : MountContract kernel initial.allocated
  dataLookup : DynamicDataLookupContract kernel semantics initial.allocated dataObjects
  cwdLookup : WorkingDirectoryContract kernel initial.allocated dataObjects
  directoryRetirement : DirectoryRetirementContract kernel
  introductions : DescriptionIntroductionContract kernel
  retirement : DescriptorRetirementContract kernel

-- §AR-host-boundary.acceptance.engine: The actual run: engine actors, calling processes, other
-- users and the validator/VM children on one journal, with each tick's recorded row.
structure Run {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (process : ProcessContract runtime) (child : ChildPrimitive kernel) (native : NativePrimitive kernel)
    (hostUid : Nat) (initial : World) where
  all : List (ActorTick runtime)
  final : Population
  journal : ActorJournal runtime (Population.empty initial) all final
  firstNative : NativeProcesses
  lastProcesses : Processes
  lastNative : NativeProcesses
  recording : NativeExternalJournal process child native hostUid Processes.empty firstNative all
    lastProcesses lastNative

-- §FS-host-boundary.ownership: Operator/bootstrap profile of the initial world. Later steps
-- are constrained only by the separate premises below.
structure Operator {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (child : ChildPrimitive kernel) (semantics : NameSemanticsView) (initial : World)
    (firstNative : NativeProcesses) where
  anchor : TemporaryAnchor initial
  anchorLookup : TemporaryLookupContract kernel anchor
  anchorOperations : AnchorOperationContract runtime child semantics anchor
  anchorState : SystemAnchorState anchor semantics initial
  wellFormed : NamespaceWellFormed initial
  foreignReferences : ForeignReferences
  foreignLive : ∀ object, foreignReferences object = true → initial.allocated object = true
  nativeLive : NativeReferencesLive firstNative initial
  catalogue : BootstrapCatalogue initial
  installedEngine : InstalledEngine catalogue
  engineArguments : NativeExec

section Premises
variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {semantics : NameSemanticsView} {initial : World} {firstNative : NativeProcesses}

-- §DA-host-delivery.engine: Engine start for one row: the identified image and fixed arguments,
-- with only raw descriptors 0, 1 and 3. Endpoint facts are in ExclusiveLaunches and the
-- caller-side hypothesis of ResponseCommitted.
def StartStep (operator : Operator runtime child semantics initial firstNative)
    {before after : Processes} {callers next : NativeProcesses} {tick : ActorTick runtime} :
    NativeExternalStep process child native hostUid before callers tick after next → Prop
  | .launch _ handoff =>
    handoff.execution.image = operator.installedEngine.image ∧
      handoff.execution.arguments = operator.engineArguments ∧
      ∀ fd, fd ≠ 0 → fd ≠ 1 → fd ≠ 3 → handoff.execution.references.rawProjection.handles fd = none
  | _ => True

def StartJournal (operator : Operator runtime child semantics initial firstNative)
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)} :
    NativeExternalJournal process child native hostUid before callers ticks after next → Prop
  | .nil _ _ => True
  | .cons current rest => StartStep operator current ∧ StartJournal operator rest

-- §DA-host-delivery.engine: One engine launch with its inherited raw descriptor table.
def LaunchAt {process : ProcessContract runtime} (run : Run runtime process child native hostUid initial)
    (position : Nat) (actor : ActorId) (references : UInt64 → Option Handle) : Prop :=
  ∃ (tick : ActorTick runtime) (closeExec : UInt64 → Bool) (directory : ObjectId),
    run.all[position]? = some tick ∧ tick.action = .launch actor references closeExec directory

-- §DA-host-delivery.engine: Across launches, one engine's request, response and cancellation
-- endpoints are inherited by no other engine actor.
def ExclusiveLaunches {process : ProcessContract runtime} (run : Run runtime process child native hostUid initial) :
    Prop :=
  ∀ (first second : Nat) (one two : ActorId) (left right : UInt64 → Option Handle)
    (leftFd rightFd : UInt64) (leftHandle rightHandle : Handle),
    LaunchAt run first one left → LaunchAt run second two right → one ≠ two →
    left leftFd = some leftHandle → right rightFd = some rightHandle →
    leftHandle.object ≠ rightHandle.object

-- §DA-host-delivery.engine: Calling-process premise, host-code profile 1 on the actual
-- recorded native operations.
structure CallingProcess (native : NativePrimitive kernel)
    (operator : Operator runtime child semantics initial firstNative)
    (all : List (ActorTick runtime)) (hostUid : Nat) : Prop where
  authority : NativeAuthorityProfile native all hostUid
  lookup : NativeLookupProfile native all hostUid
  anchor : NativeAnchorProfile native operator.anchor semantics all

def ChildAnchorStep (anchor : TemporaryAnchor initial)
    {before after : Processes} {callers next : NativeProcesses} {tick : ActorTick runtime} :
    NativeExternalStep process child native hostUid before callers tick after next → Prop
  | .child _ call => ChildAnchorOperandSafe anchor call.beforeReferences tick.before.shared call.operation
  | _ => True

def ChildAnchorJournal (anchor : TemporaryAnchor initial)
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)} :
    NativeExternalJournal process child native hostUid before callers ticks after next → Prop
  | .nil _ _ => True
  | .cons current rest => ChildAnchorStep anchor current ∧ ChildAnchorJournal anchor rest

-- §DA-host-delivery.engine: Child premise: recorded validator/VM calls leave trusted authority
-- metadata and the system anchor alone.
structure Children (run : Run runtime process child native hostUid initial)
    (operator : Operator runtime child semantics initial run.firstNative) : Prop where
  authority : RecordedChildAuthority run.recording
  anchor : ChildAnchorJournal operator.anchor run.recording

-- §FS-host-boundary.ownership: Operator premise: no tick other than an engine call changes
-- the contents of an installed bootstrap file.
def InstallationProtected (run : Run runtime process child native hostUid initial)
    (operator : Operator runtime child semantics initial run.firstNative) : Prop :=
  ∀ (position : Nat) (tick : ActorTick runtime), run.all[position]? = some tick →
    (∀ actor, tick.action.eventFor actor = none) →
    ∀ root name object, operator.catalogue.files root name object →
      tick.after.shared.contents object = tick.before.shared.contents object

structure Premises (run : Run runtime process child native hostUid initial)
    (operator : Operator runtime child semantics initial run.firstNative) : Prop where
  start : StartJournal operator run.recording
  exclusive : ExclusiveLaunches run
  calling : CallingProcess native operator run.all hostUid
  children : Children run operator
  installation : InstallationProtected run operator

end Premises

-- Conclusions

section Conclusions
variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
  {initial : World}

-- §FS-host-boundary.ownership: This snapshot records `object` in a scope owned by `actor`.
def OwnScope {all processed : List (ActorTick runtime)} {foreignReferences : ForeignReferences}
    {population : Population} {current : NativeProcesses}
    (state : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed population current)
    (actor : ActorId) (object : ObjectId) : Prop :=
  ∃ scope, state.current.source.custody.caps.family object = some scope ∧
    state.current.source.custody.catalogue.Owns actor scope

def Bound (world : World) (object : ObjectId) : Prop :=
  ∃ parent name, world.entries parent name = some object

-- §AR-host-boundary.acceptance.engine: One engine step's effects. In a public directory it adds
-- only fresh bindings or its own stage commit and removes only its own bindings; it touches no
-- other private scope. Contents and attributes change only on its own, fresh or IPC objects.
structure OwnedEffects {all processed : List (ActorTick runtime)} {foreignReferences : ForeignReferences}
    {current : NativeProcesses} (tick : ActorTick runtime)
    (state : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before current)
    (actor : ActorId) (engine : EngineState) (event : Program.Event) : Prop where
  bindings : ∀ parent name, tick.after.shared.entries parent name ≠ tick.before.shared.entries parent name →
    OwnScope state actor parent ∨
    (state.current.source.custody.caps.family parent = none ∧
      ((tick.before.shared.entries parent name = none ∧ ∃ object,
        tick.after.shared.entries parent name = some object ∧
        (tick.before.shared.allocated object = false ∨
          (∃ request observed, event = Program.filesystemPrefixEvent (request, observed) ∧
            request.op = .renameNew ∧ OwnScope state actor object ∧
            tick.before.shared.entries parent request.left = some object))) ∨
      (∃ object, tick.before.shared.entries parent name = some object ∧ OwnScope state actor object ∧
        tick.after.shared.entries parent name = none)))
  contents : ∀ object, tick.after.shared.contents object ≠ tick.before.shared.contents object →
    OwnScope state actor object ∨ tick.before.shared.allocated object = false ∨
    (∃ request observed handle, event = Program.filesystemPrefixEvent (request, observed) ∧
      request.op = .write ∧ engine.references request.first = some handle ∧ handle.object = object ∧
      state.current.source.custody.caps.family object = none ∧ ¬ Bound tick.before.shared object)
  attributes : ∀ object name,
    tick.after.shared.attributes object name ≠ tick.before.shared.attributes object name →
    OwnScope state actor object

def OwnedTick {all processed : List (ActorTick runtime)} {foreignReferences : ForeignReferences}
    {current : NativeProcesses} (tick : ActorTick runtime)
    (state : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before current) : Prop :=
  ∀ actor engine event, tick.before.actors actor = some engine →
    tick.action.eventFor actor = some event → OwnedEffects tick state actor engine event

-- §AR-host-boundary.acceptance.engine: Each custody snapshot certifies the step taken from it.
inductive OwnedAlong {all : List (ActorTick runtime)} :
    {before after : Processes} → {first last : NativeProcesses} →
    {ticks processed : List (ActorTick runtime)} → {start finish : Population} →
    {recording : NativeExternalJournal process child native hostUid before first ticks after last} →
    RegisteredCustodyExecution runtime initial all hostUid dataObjects directories semantics recording
      processed start finish → Prop where
  | nil {processes : Processes} {callers : NativeProcesses} {processed : List (ActorTick runtime)}
      {population : Population} {foreignReferences : ForeignReferences}
      (state : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
        foreignReferences processed population callers) :
      OwnedAlong (RegisteredCustodyExecution.nil (processes := processes) (callers := callers) state)
  | cons {before middle after : Processes} {first next last : NativeProcesses}
      {tick : ActorTick runtime} {ticks processed : List (ActorTick runtime)} {final : Population}
      {foreignReferences : ForeignReferences}
      {current : NativeExternalStep process child native hostUid before first tick middle next}
      {rest : NativeExternalJournal process child native hostUid middle next ticks after last}
      {state : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
        foreignReferences processed tick.before first}
      {tail : RegisteredCustodyExecution runtime initial all hostUid dataObjects directories semantics rest
        (processed ++ [tick]) tick.after final}
      (owned : OwnedTick tick state) (later : OwnedAlong tail) :
      OwnedAlong (RegisteredCustodyExecution.cons current rest state tail)

-- §AR-host-boundary.acceptance.engine: The whole run's custody history exists and certifies
-- every engine step. It is the closing statement of `global-source-family-fold`.
def CustodyConstructed (run : Run runtime process child native hostUid initial) : Prop :=
  ∃ execution : RegisteredCustodyExecution runtime initial run.all hostUid dataObjects directories
      semantics run.recording [] (Population.empty initial) run.final,
    OwnedAlong execution

-- §FS-host-boundary.ownership: Installed bootstrap contents never change during the run;
-- this supplies the read-interval observation of the installed-manifest consumer.
def InstallationStable {firstNative : NativeProcesses} (run : Run runtime process child native hostUid initial)
    (operator : Operator runtime child semantics initial firstNative) : Prop :=
  ∀ (position : Nat) (tick : ActorTick runtime), run.all[position]? = some tick →
    ∀ root name object, operator.catalogue.files root name object →
      tick.after.shared.contents object = tick.before.shared.contents object

-- §FS-host-boundary.caller: Engine part of ChannelWriteSources: every engine write into this
-- pair is the launched actor's write on its inherited descriptor 1's description.
def EngineWriters {after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)}
    {pair : Pair} {Token : Type}
    (primitive : Primitive process child native hostUid Processes.empty after callers next ticks pair Token)
    (actor : ActorId) (handle : Handle) : Prop :=
  ∀ entry token, primitive.enteredEngine token entry →
    entry.actor = actor ∧ entry.sender = .engine ∧ entry.handle.description = handle.description

-- §AR-host-boundary.acceptance.engine: For every channel history of the run, bytes queued to
-- the caller prefix the engine's encoded answer. Caller-side native entries are a premise.
def ResponseCommitted (run : Run runtime process child native hostUid initial) : Prop :=
  ∀ (pair : Pair) (Token : Type)
    (primitive : Primitive process child native hostUid Processes.empty run.lastProcesses
      run.firstNative run.lastNative run.all pair Token)
    (records : List Record) (final : PhysicalState),
    SynchronizedJournal primitive 0 run.all .unborn records final →
    (∀ entry token, primitive.enteredNative token entry → entry.sender = .caller) →
    ∀ (actor : ActorId) (handle : Handle) (tick : ActorTick runtime) (engine : EngineState)
      (history : SelectedActorHistory runtime initial run.all tick actor engine),
      history.launch.references 1 = some handle → handle.object = pair.engine →
      (records.flatMap Record.actions).flatMap (written .caller) ≠ [] →
      ∃ entry token, primitive.enteredEngine token entry ∧ entry.actor = actor ∧
        ∃ response : EngineResponse entry, ∃ current,
          final.ledger entry.key = some current ∧
          response.source.writer.offset + current.committed ≤ response.source.context.bytes.size ∧
          (records.flatMap Record.actions).flatMap (written .caller) =
            (response.source.context.bytes.extract 0
              (response.source.writer.offset + current.committed)).data.toList

-- §AR-host-boundary.acceptance.engine: Source facets over every execution of the shared
-- programs: snapshot, complete answer, report preservation, no rollback, retrieval. Each field
-- is exactly the statement of an existing checked theorem.
structure SourceFacets : Prop where
  snapshotBounds : type_of% @Snapshot.freeze_bounds
  snapshotHashes : type_of% @Snapshot.freeze_hashes
  snapshotInputs : type_of% @Snapshot.freeze_no_write_prefix
  complete : type_of% @CallerProofs.actual_application_complete
  publishedReport : type_of% @Publication.publish_report
  storageFailure : type_of% @Publication.storageFailure_fields
  commitNoRollback : type_of% @Publication.nonerror_commit_no_rollback
  finishNoRollback : type_of% @Publication.finishCommit_no_rollback
  retrievalReadOnly : type_of% @Retrieval.report_no_write_prefix
  retrievalJustified : type_of% @Retrieval.report_justified

theorem source_facets : SourceFacets :=
  ⟨@Snapshot.freeze_bounds, @Snapshot.freeze_hashes, @Snapshot.freeze_no_write_prefix,
    @CallerProofs.actual_application_complete, @Publication.publish_report,
    @Publication.storageFailure_fields, @Publication.nonerror_commit_no_rollback,
    @Publication.finishCommit_no_rollback, @Retrieval.report_no_write_prefix, @Retrieval.report_justified⟩

-- §AR-host-boundary.acceptance.engine: The conclusion of the final M5.2 theorem for one run.
structure Guarantee (run : Run runtime process child native hostUid initial)
    (operator : Operator runtime child semantics initial run.firstNative) : Prop where
  custody : CustodyConstructed (dataObjects := dataObjects) (directories := directories)
    (semantics := semantics) run
  installation : InstallationStable run operator
  response : ResponseCommitted run
  sources : SourceFacets
  engines : ∀ actor engine, run.final.actors actor = some engine →
    Program.Prefix (PrimitiveFilesystem.lower Entrypoint.run) engine.events

end Conclusions

-- The final statement

-- §AR-host-boundary.acceptance.engine: The final M5.2 proposition.
def Statement : Prop :=
  ∀ {kernel : Contract} {runtime : PrimitiveActorRuntime kernel} {process : ProcessContract runtime}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray} {initial : World}
    (_platform : Platform runtime child native hostUid semantics dataObjects directories sha256 hmac initial)
    (run : Run runtime process child native hostUid initial)
    (operator : Operator runtime child semantics initial run.firstNative),
    Premises run operator →
      Guarantee (dataObjects := dataObjects) (directories := directories) run operator

-- Closing statements

-- §AR-host-boundary.acceptance.engine: Closing statement of `global-source-family-fold`.
def FoldClosing : Prop :=
  ∀ {kernel : Contract} {runtime : PrimitiveActorRuntime kernel} {process : ProcessContract runtime}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray} {initial : World}
    (_platform : Platform runtime child native hostUid semantics dataObjects directories sha256 hmac initial)
    (run : Run runtime process child native hostUid initial)
    (operator : Operator runtime child semantics initial run.firstNative),
    Premises run operator →
      CustodyConstructed (dataObjects := dataObjects) (directories := directories) (semantics := semantics) run

-- §AR-host-boundary.acceptance.engine: Closes `same-birth-directory-custody` and
-- `public-path-and-cwd-custody`: each actual engine step on its own recorded row advances the
-- joint publication state and certifies its effects.
def EngineStepClosing : Prop :=
  ∀ {kernel : Contract} {runtime : PrimitiveActorRuntime kernel} {process : ProcessContract runtime}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray} {initial : World}
    (_platform : Platform runtime child native hostUid semantics dataObjects directories sha256 hmac initial)
    (run : Run runtime process child native hostUid initial)
    (operator : Operator runtime child semantics initial run.firstNative),
    Premises run operator →
    ∀ {position : Nat}
      (selected : SelectedNativeCut process child native hostUid Processes.empty run.lastProcesses
        run.firstNative run.lastNative run.all position),
      selectNativeCut run.recording position = some selected →
    ∀ {actor : ActorId} {event : Program.Event}, selected.tick.action.eventFor actor = some event →
    ∀ {foreignReferences : ForeignReferences}
      (prior : RegisteredPublicationState runtime initial run.all hostUid dataObjects directories semantics
        foreignReferences selected.cut.leading selected.tick.before selected.cut.priorNative),
      JointPublicationPrefix prior →
      ∃ next : RegisteredPublicationState runtime initial run.all hostUid dataObjects directories semantics
          foreignReferences (selected.cut.leading ++ [selected.tick]) selected.tick.after selected.cut.nextNative,
        JointPublicationPrefix next ∧ OwnedTick selected.tick prior.custody

-- §AR-host-boundary.acceptance.engine: Closes `foreign-and-backend-interference`: each tick
-- without an engine call, including launch, native and retirement rows, advances the state.
def ExternalStepClosing : Prop :=
  ∀ {kernel : Contract} {runtime : PrimitiveActorRuntime kernel} {process : ProcessContract runtime}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray} {initial : World}
    (_platform : Platform runtime child native hostUid semantics dataObjects directories sha256 hmac initial)
    (run : Run runtime process child native hostUid initial)
    (operator : Operator runtime child semantics initial run.firstNative),
    Premises run operator →
    ∀ {position : Nat}
      (selected : SelectedNativeCut process child native hostUid Processes.empty run.lastProcesses
        run.firstNative run.lastNative run.all position),
      selectNativeCut run.recording position = some selected →
      (∀ actor, selected.tick.action.eventFor actor = none) →
    ∀ {foreignReferences : ForeignReferences}
      (prior : RegisteredPublicationState runtime initial run.all hostUid dataObjects directories semantics
        foreignReferences selected.cut.leading selected.tick.before selected.cut.priorNative),
      JointPublicationPrefix prior →
      ∃ (foreignAfter : ForeignReferences)
        (next : RegisteredPublicationState runtime initial run.all hostUid dataObjects directories semantics
          foreignAfter (selected.cut.leading ++ [selected.tick]) selected.tick.after selected.cut.nextNative),
        JointPublicationPrefix next

-- §AR-host-boundary.acceptance.engine: Closing statement of the installed-read interval producer.
def InstallationClosing : Prop :=
  ∀ {kernel : Contract} {runtime : PrimitiveActorRuntime kernel} {process : ProcessContract runtime}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray} {initial : World}
    (_platform : Platform runtime child native hostUid semantics dataObjects directories sha256 hmac initial)
    (run : Run runtime process child native hostUid initial)
    (operator : Operator runtime child semantics initial run.firstNative),
    Premises run operator → InstallationStable run operator

-- §AR-host-boundary.acceptance.engine: Closes the engine half of the response channel: only
-- the launched actor's response writer enters its own pair.
def ResponseClosing : Prop :=
  ∀ {kernel : Contract} {runtime : PrimitiveActorRuntime kernel} {process : ProcessContract runtime}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray} {initial : World}
    (_platform : Platform runtime child native hostUid semantics dataObjects directories sha256 hmac initial)
    (run : Run runtime process child native hostUid initial)
    (operator : Operator runtime child semantics initial run.firstNative),
    Premises run operator →
    ∀ (pair : Pair) (Token : Type)
      (primitive : Primitive process child native hostUid Processes.empty run.lastProcesses
        run.firstNative run.lastNative run.all pair Token)
      (records : List Record) (final : PhysicalState),
      SynchronizedJournal primitive 0 run.all .unborn records final →
      (∀ entry token, primitive.enteredNative token entry → entry.sender = .caller) →
    ∀ (actor : ActorId) (handle : Handle) (tick : ActorTick runtime) (engine : EngineState)
      (history : SelectedActorHistory runtime initial run.all tick actor engine),
      history.launch.references 1 = some handle → handle.object = pair.engine →
      EngineWriters primitive actor handle

-- §AR-host-boundary.acceptance.engine: Useful run: an engine reached a complete `run` answer.
def UsefulComplete {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {initial : World} (run : Run runtime process child native hostUid initial) : Prop :=
  ∃ (actor : ActorId) (engine : EngineState) (context : EntrypointPrefixCuts.Responded)
    (request : GatewayWire.Request) (raw later : List Program.Event) (residual : Program UInt32),
    run.final.actors actor = some engine ∧ engine.events = raw ++ later ∧
    PrimitiveFilesystem.Reached Entrypoint.run context.events raw residual ∧
    context.read.packet = .ok request ∧ request.command = GatewayWire.runCommand ∧
    RequestGuarantee.statusField context.response.2 = some "complete"

-- §AR-host-boundary.acceptance.engine: The response facet's hypotheses hold nonvacuously:
-- a channel history with caller-side native entries and bytes toward the caller.
def ResponseWitness {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {initial : World} (run : Run runtime process child native hostUid initial) : Prop :=
  ∃ (pair : Pair) (Token : Type)
    (primitive : Primitive process child native hostUid Processes.empty run.lastProcesses
      run.firstNative run.lastNative run.all pair Token)
    (records : List Record) (final : PhysicalState),
    Nonempty (SynchronizedJournal primitive 0 run.all .unborn records final) ∧
    (∀ entry token, primitive.enteredNative token entry → entry.sender = .caller) ∧
    ∃ (actor : ActorId) (handle : Handle) (tick : ActorTick runtime) (engine : EngineState)
      (history : SelectedActorHistory runtime initial run.all tick actor engine),
      history.launch.references 1 = some handle ∧ handle.object = pair.engine ∧
      (records.flatMap Record.actions).flatMap (written .caller) ≠ []

-- §AR-host-boundary.acceptance.engine: Rejected run: an engine reached a nonzero status.
def Rejected {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {initial : World} (run : Run runtime process child native hostUid initial) : Prop :=
  ∃ (actor : ActorId) (engine : EngineState) (context : EntrypointPrefixCuts.Responded)
    (raw later : List Program.Event) (residual : Program UInt32),
    run.final.actors actor = some engine ∧ engine.events = raw ++ later ∧
    PrimitiveFilesystem.Reached Entrypoint.run context.events raw residual ∧
    context.response.1 ≠ 0

-- §AR-host-boundary.acceptance.engine: Lost-reply run: some engine call has no reply.
def LostReply {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {initial : World} (run : Run runtime process child native hostUid initial) : Prop :=
  ∃ (position : Nat) (tick : ActorTick runtime) (actor : ActorId) (β : Type) (effect : Effect β),
    run.all[position]? = some tick ∧ tick.action = .lost actor effect

-- §AR-host-boundary.acceptance.engine: Closes `joint-usefulness-and-acceptance` for the engine:
-- one model satisfies every premise with useful, rejected and lost-reply runs.
def ModelClosing : Prop :=
  ∃ (kernel : Contract) (runtime : PrimitiveActorRuntime kernel) (process : ProcessContract runtime)
    (child : ChildPrimitive kernel) (native : NativePrimitive kernel) (hostUid : Nat)
    (semantics : NameSemanticsView) (dataObjects directories : ObjectId → Prop)
    (sha256 : ByteArray → ByteArray) (hmac : ByteArray → ByteArray → ByteArray) (initial : World),
    Nonempty (Platform runtime child native hostUid semantics dataObjects directories sha256 hmac initial) ∧
    (∃ (run : Run runtime process child native hostUid initial)
        (operator : Operator runtime child semantics initial run.firstNative),
      Premises run operator ∧ UsefulComplete run ∧ ResponseWitness run) ∧
    (∃ (run : Run runtime process child native hostUid initial)
        (operator : Operator runtime child semantics initial run.firstNative),
      Premises run operator ∧ Rejected run) ∧
    (∃ (run : Run runtime process child native hostUid initial)
        (operator : Operator runtime child semantics initial run.firstNative),
      Premises run operator ∧ LostReply run)

-- Statement plumbing

-- §FS-host-boundary.caller: The engine writer closing statement and the caller-side premise
-- supply the existing writer-prefix consumer's write sources.
theorem response_committed (closing : ResponseClosing) {kernel : Contract}
    {runtime : PrimitiveActorRuntime kernel} {process : ProcessContract runtime}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray} {initial : World}
    (platform : Platform runtime child native hostUid semantics dataObjects directories sha256 hmac initial)
    (run : Run runtime process child native hostUid initial)
    (operator : Operator runtime child semantics initial run.firstNative)
    (premises : Premises run operator) : ResponseCommitted run := by
  intro pair Token primitive records final physical callerSide actor handle tick engine history
    inherited endpoint nonempty
  have engineSide := closing platform run operator premises pair Token primitive records final physical
    callerSide actor handle tick engine history inherited endpoint
  exact actual_response_written_prefix platform.descriptors platform.directoryRetirement
    platform.introductions platform.retirement platform.sdk platform.lifetimes platform.references
    platform.environment run.journal physical actor handle ⟨engineSide, callerSide⟩ tick engine history
    inherited endpoint nonempty

-- §AR-host-boundary.acceptance.engine: The final statement follows from the closing statements
-- and checked source/journal results. This plumbing proves no closing statement.
theorem statement_of_closings (fold : FoldClosing) (installation : InstallationClosing)
    (response : ResponseClosing) : Statement := by
  intro kernel runtime process child native hostUid semantics dataObjects directories sha256 hmac
    initial platform run operator premises
  exact ⟨fold platform run operator premises, installation platform run operator premises,
    response_committed response platform run operator premises, source_facets,
    fun actor engine present => actual_actor_entry_prefix_for (actor_journal_history run.journal) actor engine present⟩

end LeanCage.Host.EngineGuarantee
