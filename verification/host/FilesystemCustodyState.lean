import FilesystemNativeCustody
import FilesystemCwdCustody
import FilesystemLaunchPrefix
import FilesystemBirthScopes

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.ownership: Source custody, native references and inherited CWD share
-- one current population and the SAME native process ledger; no future IPC IDs are allocated.
structure CustodyState {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram)
    (initial : World) (ticks : List (ActorTick runtime)) (hostUid : Nat)
    (dataObjects directories : ObjectId → Prop) (semantics : NameSemanticsView)
    (foreignReferences : ForeignReferences) (processed : List (ActorTick runtime))
    (population : Population) (native : NativeProcesses) where
  source : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics foreignReferences processed population
  nativePublic : NativeReferencesPublic native source.custody.caps.family
  nativeLive : NativeReferencesLive native population.shared
  directoriesPublic : EngineDirectoriesPublic population source.custody.caps.family
  directoriesLive : EngineDirectoriesLive population
  births : CatalogueBirthScopes runtime source.custody.catalogue processed population source.custody.caps.family

def initial_custody_state {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram)
    (initial : World) (ticks : List (ActorTick runtime)) (hostUid : Nat)
    (dataObjects directories : ObjectId → Prop) (semantics : NameSemanticsView)
    (foreignReferences : ForeignReferences) (native : NativeProcesses)
    (wellFormed : NamespaceWellFormed initial)
    (live : ∀ object, foreignReferences object = true → initial.allocated object = true)
    (nativeLive : NativeReferencesLive native initial) :
    CustodyState runtime initial ticks hostUid dataObjects directories semantics foreignReferences []
      (Population.empty initial) native := {
  source := initial_ownership_prefix runtime initial ticks hostUid dataObjects directories semantics foreignReferences wellFormed live
  nativePublic := fun _ _ => rfl
  nativeLive
  directoriesPublic := (empty_directories_custody initial Capabilities.empty.family).2
  directoriesLive := (empty_directories_custody initial Capabilities.empty.family).1
  births := empty_catalogue_birth_scopes runtime ticks initial }

-- §FS-host-boundary.ownership: A separately derived actual source case cannot privatize
-- an old native reference/CWD. Runtime child actions remain separate from this parent step.
def CustodyState.application {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (runtimeLaws : RuntimeDescriptorContract runtime) (lifetimes : LifetimeContract runtime)
    {initial : World} {ticks processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignBefore foreignAfter : ForeignReferences} {tick : ActorTick runtime} {native : NativeProcesses}
    (prior : CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignBefore processed tick.before native)
    (next : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignAfter (processed ++ [tick]) tick.after)
    (notLaunch : ∀ actor references closeExec directory, tick.action ≠ .launch actor references closeExec directory)
    (labels : ExistingLabels tick.before.shared tick.after.shared prior.source.custody.caps.family next.custody.caps.family)
    (included : ∀ record ∈ prior.source.custody.catalogue, record ∈ next.custody.catalogue)
    (newRecords : ∀ record ∈ next.custody.catalogue, record ∈ prior.source.custody.catalogue ∨
      (record.2.tick = tick ∧ record.2.position = processed.length ∧
        next.custody.caps.family record.1.object = some record.1.object ∧
        tick.after.shared.allocated record.1.parent = true ∧ next.custody.caps.family record.1.parent = none))
    (ownership : CustodyOwnershipStep next.custody.catalogue tick
      prior.source.custody.caps.family next.custody.caps.family) :
    CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignAfter (processed ++ [tick]) tick.after native := by
  obtain ⟨liveDirectories, publicDirectories⟩ := nonlaunch_directories_custody runtimeLaws lifetimes tick.operation notLaunch
    prior.directoriesLive prior.directoriesPublic labels
  exact {
    source := next
    nativePublic := native_public_existing_labels prior.nativeLive prior.nativePublic labels
    nativeLive := fun object held => actor_step_allocated lifetimes tick.operation object (prior.nativeLive object held)
    directoriesPublic := publicDirectories
    directoriesLive := liveDirectories
    births := catalogue_birth_scopes_advance included newRecords prior.births ownership labels
      (fun object => actor_step_allocated lifetimes tick.operation object) }

private theorem launch_shared {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {actor : ActorId} {references : UInt64 → Option Handle}
    {closeExec : UInt64 → Bool} {directory : ObjectId}
    (actual : ActorStep runtime (.launch actor references closeExec directory) before after) :
    after.shared = before.shared := by cases actual; rfl

private theorem transferred_held {processes : NativeProcesses} {actor : ActorId} {execution : NativeExecution}
    {object : ObjectId} (held : NativeHeld (processes.transfer actor execution) object) : NativeHeld processes object := by
  rcases held with ⟨token, references, present, reference⟩ | retired
  · by_cases same : token = actor
    · simp only [NativeProcesses.transfer, same, ite_eq_left] at present
      cases present
    · exact .inl ⟨token, references, by simpa only [NativeProcesses.transfer, ite_eq_right same] using present, reference⟩
  · exact .inr retired

-- §FS-host-boundary.caller: The source launch consumes the actual same exec snapshot and
-- transfers its current native token. Raw channels and complementary SDK references coexist.
theorem handoff_custody_state_retained {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime)
    {initial : World} {ticks processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories ipc : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {before : NativeProcesses}
    (handoff : NativeHandoffAt tick before)
    (binding : InitialEngineBinding ipc handoff.execution.references.rawProjection.handles
      handoff.execution.references.rawProjection.closeOnExec)
    (separate : ∀ object, ipc object → ¬ dataObjects object)
    (prior : CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before before) :
    ∃ next : CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after (before.transfer handoff.actor handoff.execution),
      next.source.custody.catalogue = prior.source.custody.catalogue ∧
      next.source.custody.caps.family = prior.source.custody.caps.family := by
  have actual : ActorStep runtime (.launch handoff.actor handoff.execution.references.rawProjection.handles
      handoff.execution.references.rawProjection.closeOnExec handoff.execution.references.workingDirectory)
      tick.before tick.after := handoff.action ▸ tick.operation
  have shared := launch_shared actual
  have owned := launched_engine_references_owned actual binding separate
    prior.source.custody.namespaceState.graph prior.source.custody.references
  have state : NamespaceCustody tick.after.shared prior.source.custody.caps hostUid initial.allocated
      dataObjects directories foreignReferences := shared ▸ prior.source.custody.namespaceState
  let next := prior.source.custody.advance descriptors lifetimes references prior.source.custody.caps
    prior.source.custody.catalogue state (shared ▸ prior.source.custody.names) prior.source.custody.coverage
    (shared ▸ prior.source.custody.valid) owned .same
  have ownership : CustodyOwnershipStep next.catalogue tick prior.source.custody.caps.family next.caps.family :=
    nonremoving_ownership_step next.catalogue (by intro parent name object bound; rw [shared]; exact bound)
      (by intro object allocated; rfl)
  have nativePublic : NativeReferencesPublic (before.transfer handoff.actor handoff.execution)
      next.caps.family := fun object held => prior.nativePublic object (transferred_held held)
  have nativeLive : NativeReferencesLive (before.transfer handoff.actor handoff.execution) tick.after.shared := by
    intro object held
    rw [shared]
    exact prior.nativeLive object (transferred_held held)
  obtain ⟨directoriesLive, directoriesPublic⟩ := native_handoff_directories_custody handoff
    prior.nativeLive prior.nativePublic prior.directoriesLive prior.directoriesPublic
  have births := catalogue_birth_scopes_existing (by intro record member; exact member)
    (by intro record member; exact member) prior.births ownership (unchanged_existing_labels _ _ _)
    (fun object allocated => by rw [shared]; exact allocated)
  exact ⟨⟨prior.source.advance next (by intro record member; exact member) ownership,
    nativePublic, nativeLive, directoriesPublic, directoriesLive, births⟩, rfl, rfl⟩

-- §AR-host-boundary.interfaces: Preserve the original catalogue projection.
theorem handoff_custody_state_catalogued {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime)
    {initial : World} {ticks processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories ipc : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {before : NativeProcesses}
    (handoff : NativeHandoffAt tick before)
    (binding : InitialEngineBinding ipc handoff.execution.references.rawProjection.handles
      handoff.execution.references.rawProjection.closeOnExec)
    (separate : ∀ object, ipc object → ¬ dataObjects object)
    (prior : CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before before) :
    ∃ next : CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after (before.transfer handoff.actor handoff.execution),
      next.source.custody.catalogue = prior.source.custody.catalogue := by
  obtain ⟨next, catalogue, family⟩ := handoff_custody_state_retained descriptors lifetimes references handoff binding separate prior
  exact ⟨next, catalogue⟩

-- §AR-host-boundary.interfaces: Preserve the original handoff consumer while retaining
-- the exact catalogue in the stronger sibling used by the registered global source fold.
theorem handoff_custody_state {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime)
    {initial : World} {ticks processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories ipc : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {before : NativeProcesses}
    (handoff : NativeHandoffAt tick before)
    (binding : InitialEngineBinding ipc handoff.execution.references.rawProjection.handles
      handoff.execution.references.rawProjection.closeOnExec)
    (separate : ∀ object, ipc object → ¬ dataObjects object)
    (prior : CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before before) :
    Nonempty (CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after (before.transfer handoff.actor handoff.execution)) := by
  obtain ⟨next, catalogue⟩ := handoff_custody_state_catalogued descriptors lifetimes references
    handoff binding separate prior
  exact ⟨next⟩

-- §FS-host-boundary.ownership: This constructor consumes the concrete native source row,
-- resolved per-operation operands and the existing versioned external host-code profile.
theorem native_custody_state_retained {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {primitive : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : NativeNamespaceContract primitive) (metadata : NativeLiveMetadataContract primitive)
    (heldMetadata : NativeMetadataContract primitive) (descriptors : DescriptorContract kernel)
    (runtimeLaws : RuntimeDescriptorContract runtime) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (objects : ObjectLifetimeContract runtime)
    (lookup : NativeNonemptyLookupContract primitive semantics)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (boundaryProfile : NativeBoundaryAuthorityProfile primitive ticks hostUid)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick)
    {before after : NativeProcesses} (call : NativeCallAt primitive tick before after)
    {processed : List (ActorTick runtime)} {foreignReferences : ForeignReferences}
    (prior : CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before before)
    (profile : NativePrivateOperandProfile namespaceLaws call prior.source.custody.caps.family) :
    ∃ next : CustodyState runtime initial ticks hostUid dataObjects directories semantics
        foreignReferences (processed ++ [tick]) tick.after after,
      next.source.custody.catalogue = prior.source.custody.catalogue ∧
      next.source.custody.caps.family = prior.source.custody.caps.family := by
  obtain ⟨next, nativePublic, nativeLive, caps, catalogue⟩ := native_custody_prefix_current namespaceLaws metadata
    heldMetadata descriptors lifetimes references objects lookup journal boundaryProfile selected call prior.source
    profile prior.nativePublic
  have notLaunch : ∀ actor references closeExec directory, tick.action ≠ .launch actor references closeExec directory := by
    intro actor references closeExec directory impossible
    rw [call.action] at impossible
    cases impossible
  have labels : ExistingLabels tick.before.shared tick.after.shared
      prior.source.custody.caps.family next.custody.caps.family := by
    rw [caps]
    exact unchanged_existing_labels _ _ _
  obtain ⟨liveDirectories, publicDirectories⟩ := nonlaunch_directories_custody runtimeLaws lifetimes tick.operation notLaunch
    prior.directoriesLive prior.directoriesPublic labels
  have ownership : CustodyOwnershipStep next.custody.catalogue tick
      prior.source.custody.caps.family next.custody.caps.family := by
    rw [caps, catalogue]
    exact native_namespace_ownership_step namespaceLaws prior.source.custody.catalogue call profile
  have included : ∀ record ∈ prior.source.custody.catalogue, record ∈ next.custody.catalogue := by
    rw [catalogue]
    exact fun _ member => member
  have old : ∀ record ∈ next.custody.catalogue, record ∈ prior.source.custody.catalogue := by
    rw [catalogue]
    exact fun _ member => member
  have family := congrArg Capabilities.family caps
  exact ⟨⟨next, nativePublic, nativeLive, publicDirectories, liveDirectories,
    catalogue_birth_scopes_existing included old prior.births ownership labels
      (fun object => actor_step_allocated lifetimes tick.operation object)⟩, catalogue, family⟩

-- §AR-host-boundary.interfaces: Preserve the original native-row result;
-- the stronger sibling retains the exact family/catalogue for cumulative source custody.
theorem native_custody_state {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {primitive : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : NativeNamespaceContract primitive) (metadata : NativeLiveMetadataContract primitive)
    (heldMetadata : NativeMetadataContract primitive) (descriptors : DescriptorContract kernel)
    (runtimeLaws : RuntimeDescriptorContract runtime) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (objects : ObjectLifetimeContract runtime)
    (lookup : NativeNonemptyLookupContract primitive semantics)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (boundaryProfile : NativeBoundaryAuthorityProfile primitive ticks hostUid)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick)
    {before after : NativeProcesses} (call : NativeCallAt primitive tick before after)
    {processed : List (ActorTick runtime)} {foreignReferences : ForeignReferences}
    (prior : CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before before)
    (profile : NativePrivateOperandProfile namespaceLaws call prior.source.custody.caps.family) :
    Nonempty (CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after after) := by
  obtain ⟨next, catalogue, family⟩ := native_custody_state_retained namespaceLaws metadata heldMetadata descriptors
    runtimeLaws lifetimes references objects lookup journal boundaryProfile selected call prior profile
  exact ⟨next⟩

end LeanCage.Host.Kernel
