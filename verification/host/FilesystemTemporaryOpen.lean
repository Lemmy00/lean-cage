import FilesystemInitialDirectoryCustody
import FilesystemAnchorHistory

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: The initialized root/tmp/mount anchor resolves ONE
-- exact openat, including an introduced descriptor with error/lost acknowledgement.
-- It supplies no request-specific child binding, name freshness or ownership role.
structure TemporaryOpenTargetContract (kernel : Contract) {initial : World} (anchor : TemporaryAnchor initial)
    {semantics : NameSemanticsView} {dataObjects : ObjectId → Prop}
    (targets : OpenTargetContract kernel semantics initial.allocated dataObjects) : Prop where
  resolved : ∀ before after observed object,
    kernel.step before {op := .openAt, first := cwd, second := directoryFlags, left := "/tmp".toUTF8} observed after →
    anchor.At before →
    targets.target before {op := .openAt, first := cwd, second := directoryFlags, left := "/tmp".toUTF8}
      observed after object → object = anchor.visible

-- §AR-host-boundary.interfaces: The old acknowledged-open law is a specialization
-- of the same actual resolution contract, rather than another independent FD fixture.
theorem TemporaryOpenTargetContract.acknowledged {kernel : Contract} {initial : World} {anchor : TemporaryAnchor initial}
    {semantics : NameSemanticsView} {dataObjects : ObjectId → Prop}
    {targets : OpenTargetContract kernel semantics initial.allocated dataObjects}
    (source : TemporaryOpenTargetContract kernel anchor targets) (descriptors : DescriptorContract kernel) :
    TemporaryLookupContract kernel anchor where
  opened before after reply _fd handle actual atAnchor opened live :=
    source.resolved before after (some reply) handle.object actual atAnchor
      (targets.acknowledged descriptors actual rfl opened live)

-- §FS-host-boundary.ownership: A prefix-only /tmp selection obtains its public
-- lifetime from the actual initial anchor. No future open/stat success is assumed,
-- and a real error/lost acknowledgement can still introduce a descriptor.
theorem temporary_open_registered_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (namespaceLaws : PassiveNamespaceContract kernel) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} (targets : OpenTargetContract kernel semantics initial.allocated dataObjects)
    (anchor : TemporaryAnchor initial) (resolution : TemporaryOpenTargetContract kernel anchor targets)
    {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    (anchors : SystemAnchorJournal runtime anchor semantics (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    {position : Nat} (selected : all[position]? = some tick) {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (operation : request = {op := .openAt, first := cwd, second := directoryFlags, left := "/tmp".toUTF8}) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative) := by
  have actual := selected_filesystem_step tick action present
  have filesystem := selected_filesystem_action_family action
  have safe := selected_primitive_action_authority journal selected
  have passive : NamespacePassive request := by rw [operation]; exact .inr rfl
  have requestSafe : AuthoritySafeRequest request := by intro setting; rw [operation] at setting; cases setting
  have entries := namespaceLaws.operation (tick.before.project engine) tick.after.shared request observed actual passive
  have state := source_unchanged_filesystem_custody accounts objects metadata actual filesystem safe requestSafe
    prior.current.source.custody.namespaceState.project entries
  have names := filesystem_registered_root_names lookup filesystem safe
    prior.current.source.custody.namespaceState.registry prior.current.source.custody.names
  obtain ⟨anchorState⟩ := system_anchor_selected anchors selected
  have atAnchor : anchor.At (tick.before.project engine) := anchorState.bound
  have owned := opened_filesystem_references_owned targets action present (congrArg Request.op operation)
    prior.current.source.custody.consistent (unchanged_existing_labels _ _ _) (by intro record member; exact member)
    prior.current.source.custody.references (by
      intro object scope target label
      have same : object = anchor.visible := resolution.resolved (tick.before.project engine) tick.after.shared observed object
        (operation ▸ actual) atAnchor (operation ▸ target)
      have publicObject := family_initial_public prior.current.source.custody.namespaceState.graph anchor.visible anchor.visibleInitial
      rw [same, publicObject] at label
      cases label)
  have allocation := fun object => kernel.allocation_monotone (tick.before.project engine)
    tick.after.shared request observed object actual
  let next := prior.current.source.custody.advance descriptors lifetimes references
    (prior.current.source.custody.caps.retain tick.after.shared) prior.current.source.custody.catalogue
    state names (catalogue_retained_covers prior.current.source.custody.coverage)
    (catalogue_advance_valid prior.current.source.custody.valid allocation) owned .same
  have ownership : CustodyOwnershipStep next.catalogue tick prior.current.source.custody.caps.family next.caps.family :=
    nonremoving_ownership_step _ (by intro parent name object bound; rwa [entries]) (by intro object allocated; rfl)
  let nextSource := prior.current.source.advance next (by intro record member; exact member) ownership
  refine ⟨prior.sourceStep sdk lifetimes nextSource ?_ (unchanged_existing_labels _ _ _) rfl ownership ?_⟩
  · intro owner handles closeExec directory impossible
    rw [impossible] at action
    cases action
  · exact no_root_use_of_other_operation action (by rw [operation]; decide)

end LeanCage.Host.Kernel
