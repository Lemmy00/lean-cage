import FilesystemPreparingRoot
import FilesystemCleanupObservations

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.lookup: The current preparation keeps the actual
-- original stat observation and the SAME retained raw stage reference.
theorem PreparingStageResources.observation_at {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed}
    {call : PublicationPreparing.Call adapter.occurrence.logicalBefore request} {position : Nat}
    (resources : PreparingStageResources adapter call position) :
    ∃ observation : ObservedDirectory kernel (fun ordinal query reply =>
        SourceReturnAt runtime all actor ordinal Reply (.filesystem query) reply)
        engine.events.length (tick.before.project engine) call.context.parent.uid call.context.stage.directory,
      observation.handle = resources.source.earlier.source.opening.handle ∧
        observation.sample.ordinal = resources.point.observation.sample.ordinal := by
  let point := resources.point
  let checked := point.observation.mapOrigin (fun ordinal query reply before after evidence =>
    Eq.mp (congrArg (fun who => SourceReturnAt runtime all who ordinal Reply (.filesystem query) reply before after)
      resources.sameActor) evidence)
  have live : (tick.before.project engine).handles call.context.stage.directory.fd = some checked.handle := by
    change engine.references call.context.stage.directory.fd = some point.observation.handle
    rw [point.sameObserved]
    exact resources.directory
  have total := congrArg List.length resources.eventTrace
  simp only [List.length_append, List.length_cons, List.length_map] at total
  have rest := congrArg List.length point.trace
  simp only [List.length_append] at rest
  dsimp only [point] at rest
  have bounded : resources.source.earlier.source.input.events.length + 1 +
      resources.source.earlier.post.length + resources.point.inspectionRaw.length ≤ engine.events.length := by omega
  exact ⟨checked.advance live (by simpa only [List.length_map] using bounded), point.sameObserved, rfl⟩

-- §FS-host-boundary.lookup: The original stage stat precedes the SAME
-- current operation's raw guard. Its position is derived from complete
-- source chunks, rather than a separately selected matching stat reply.
theorem PreparingStageResources.stat_before_guard {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed}
    {call : PublicationPreparing.Call adapter.occurrence.logicalBefore request} {position : Nat}
    (resources : PreparingStageResources adapter call position) :
    resources.point.observation.sample.ordinal < adapter.occurrence.rawBefore.length := by
  have actualTotal := congrArg List.length adapter.occurrence.trace
  have canonicalTotal := congrArg List.length resources.eventTrace
  have rest := congrArg List.length resources.point.trace
  have guards := congrArg List.length resources.guards
  have earlier := resources.point.observation.earlier
  simp only [List.length_append, List.length_cons, List.length_map] at actualTotal canonicalTotal rest guards earlier
  omega

theorem preparing_stage_uid_sample {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel)
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (call : PublicationPreparing.Call adapter.occurrence.logicalBefore request) :
    Nonempty (UidSample kernel (fun ordinal query reply =>
      SourceReturnAt runtime all actor ordinal Reply (.filesystem query) reply) call.context.parent.uid) := by
  obtain ⟨selection⟩ := primitive_filesystem_phase adapter call.context.selected
    (show adapter.occurrence.logicalBefore = call.selectingContext ++ call.context.selecting.map Program.filesystemEvent ++
      (call.context.creating.map Program.filesystemEvent ++ call.inside.map Program.filesystemPrefixEvent) from by
        simpa only [List.append_assoc] using call.trace)
  obtain ⟨parent⟩ := Lowered.parent_recorded descriptors _ selection.phase.rawBefore.length call.host.source.target true
    selection.phase.actual
  exact ⟨parent.identity⟩

-- §FS-host-boundary.lookup: This real current stage operand derives its
-- comparison from the SAME original stat, retained OFD and current probes.
-- No parent authority, safe comparison or private-family frame is assumed.
theorem PreparingStageResources.directory_comparison {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {semantics : NameSemanticsView}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (raw : RawReferenceLifetimeContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (authority : GlobalAuthorityContract runtime child) (nativeMetadata : NativeMetadataContract native)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    (probes : LookupPrimitiveContract kernel.step kernel.interference semantics)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    (authorityProfile : NativeAuthorityProfile native all hostUid) (lookupProfile : NativeLookupProfile native all hostUid)
    {before after : Processes} {first last : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid before first all after last)
    {backend : NativeAuthorityJournal recording}
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (selected : all[position]? = some tick) (present : tick.before.actors actor = some engine)
    {adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed}
    {call : PublicationPreparing.Call adapter.occurrence.logicalBefore request}
    (resources : PreparingStageResources adapter call position) (kind : NamespaceRequest request)
    (member : call.context.stage.directory.fd ∈ Lookup.parents request) :
    (semantics.at tick.before.shared resources.source.earlier.source.opening.handle.object).byteExact := by
  obtain ⟨identity⟩ := preparing_stage_uid_sample descriptors adapter call
  have uid := sampled_uid_is_host accounts identity
  obtain ⟨original, sameHandle, sameOrdinal⟩ := resources.observation_at
  let observation : ObservedDirectory kernel (fun ordinal query reply =>
      SourceReturnAt runtime all actor ordinal Reply (.filesystem query) reply)
      engine.events.length (tick.before.project engine) hostUid call.context.stage.directory := {
    handle := original.handle
    live := original.live
    raw := original.raw
    sample := original.sample
    earlier := original.earlier
    trusted := uid ▸ original.trusted }
  have beforeGuard : observation.sample.ordinal < adapter.occurrence.rawBefore.length := by
    change original.sample.ordinal < adapter.occurrence.rawBefore.length
    rw [sameOrdinal]
    exact resources.stat_before_guard
  have live : engine.references call.context.stage.directory.fd = some observation.handle := observation.live
  obtain ⟨interval, intervalHandle, intervalOrdinal⟩ := checked_parent_interval_owned (backend := backend) descriptors
    lifetimes references raw sdk accounts journal recording selected present observation live observation.earlier
  obtain ⟨information, known, trusted, names⟩ := checked_parent_comparison lifetimes authority nativeMetadata lookup probes
    journal authorityProfile lookupProfile interval adapter kind call.context.stage.directory.fd member observation.handle
    live (by rw [intervalHandle]) (by rw [intervalOrdinal]; exact beforeGuard)
  have checked : (semantics.at tick.before.shared original.handle.object).byteExact := by
    simpa only [intervalHandle] using names
  simpa only [sameHandle] using checked

namespace Lowered

-- §FS-host-boundary.lookup: Both traversal modes retain each real child
-- stat sample; create=true uses the actual ensureAt source and its replies.
theorem preparing_chain_observed {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (descriptors : DescriptorContract kernel)
    (actor : ActorId) (origin : OperationOrigin) (limit : Nat) {family : Family}
    (opens : PrivateDirectoryOpens kernel (fun index query reply before after =>
      origin index Reply (.filesystem query) reply before after ∧ index < limit) family)
    {uid : Nat} {create : Bool} {root leaf : UInt64} {names : List String} {logical : List (Request × Reply)}
    (source : Publication.DirectoryChain uid create root names logical leaf)
    {raw : List Program.Event} (chunks : PrimitiveFilesystem.Chunks (logical.map Program.filesystemEvent) raw)
    {ordinal : Nat} {before after : World}
    (history : ActorHistoryWith runtime actor origin ordinal before raw after)
    (bounded : ordinal + raw.length ≤ limit) {information : Stat}
    (starting : ObservedDirectory kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
      ordinal before uid {fd := root, information}) {scope : ObjectId}
    (privateRoot : family starting.handle.object = some scope) :
    ∃ directory : Directories.Opened, directory.fd = leaf ∧
      ∃ observation : ObservedDirectory kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
        (ordinal + raw.length) after uid directory, family observation.handle.object = some scope := by
  induction source generalizing raw ordinal before information with
  | root parent =>
    cases chunks
    have live : after.handles parent = some starting.handle := by
      rw [actor_retaining_event_handles descriptors history (by intro event impossible; cases impossible)]
      exact starting.live
    exact ⟨{fd := parent, information}, rfl, starting.advance live (by simp), privateRoot⟩
  | @child parent name names opened opening following last component actual below ih =>
    rw [List.map_append] at chunks
    obtain ⟨first, final, openingChunks, followingChunks, trace⟩ := PrimitiveFilesystem.chunks_split _ _ chunks
    obtain ⟨middle, initialHistory, lastHistory⟩ := actor_with_split first final (trace ▸ history)
    obtain ⟨events, openingSource, openingTrace⟩ := PrimitiveFilesystem.chunks_filesystem_returns actual openingChunks
    have openingHistory := actor_recorded_filesystem (openingTrace ▸ initialHistory)
    have openingBound : ordinal + events.length ≤ limit := by
      have length := congrArg List.length trace
      have openingLength := congrArg List.length openingTrace
      simp only [List.length_append, List.length_map] at length openingLength
      omega
    have boundedHistory := recorded_history_source_bound openingHistory limit openingBound
    have operands : Directories.component name.toUTF8 = true ∧ name.toUTF8 ≠ ".".toUTF8 ∧ name.toUTF8 ≠ "..".toUTF8 :=
      ⟨SourceReadForms.valid_component_form name component,
        fun same => component.2.2.1 (String.toByteArray_inj.mp same),
        fun same => component.2.2.2.1 (String.toByteArray_inj.mp same)⟩
    have child : ∃ observation : ObservedDirectory kernel
        (fun index query reply before after => origin index Reply (.filesystem query) reply before after ∧ index < limit)
        (ordinal + events.length) middle uid opened, family observation.handle.object = some scope := by
      cases create <;> simp only [Publication.childOpening, Bool.false_eq_true, ↓reduceIte] at openingSource
      · exact directory_open_private descriptors opens ordinal uid parent name.toUTF8 starting.handle scope
          ⟨openingSource, boundedHistory⟩ starting.live privateRoot operands.1 operands.2.1 operands.2.2
      · exact directory_ensure_private descriptors opens ordinal uid parent name.toUTF8 starting.handle scope
          ⟨openingSource, boundedHistory⟩ starting.live privateRoot operands.1 operands.2.1 operands.2.2
    obtain ⟨observed, privateChild⟩ := child
    let checked := observed.mapOrigin (fun _ _ _ _ _ evidence => evidence.1)
    let atChild : ObservedDirectory kernel (fun ordinal query reply => origin ordinal Reply (.filesystem query) reply)
        (ordinal + first.length) middle uid opened := checked.advance checked.live (by
      have length := congrArg List.length openingTrace
      simp only [List.length_map] at length
      omega)
    obtain ⟨directory, same, observation, privateParent⟩ :=
      ih followingChunks lastHistory (by rw [trace, List.length_append] at bounded; omega) atChild privateChild
    exact ⟨directory, same, observation.advance observation.live (by rw [trace, List.length_append]; omega), privateParent⟩

end Lowered

end LeanCage.Host.Kernel
