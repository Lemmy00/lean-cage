import FilesystemInitialDirectoryCustody

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: A real read/directory open under an owned private
-- parent inherits that same scope, including reserved artifact component spellings.
-- Unacknowledged descriptor births remain in the actual one-operation target relation.
theorem private_child_read_registered_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (namespaceLaws : PassiveNamespaceContract kernel) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} (targets : OpenTargetContract kernel semantics initial.allocated dataObjects)
    {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} {parent : Handle} {scope : ObjectId}
    (selected : all[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (opening : request.op = .openAt)
    (flags : request.second = directoryFlags ∨ request.second = readFlags)
    (parentLive : engine.references request.first = some parent)
    (component : Directories.component request.left = true)
    (notDot : request.left ≠ ".".toUTF8) (notUp : request.left ≠ "..".toUTF8)
    {foreignReferences : ForeignReferences} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    (parentPrivate : prior.current.source.custody.caps.family parent.object = some scope) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative) := by
  have actual := selected_filesystem_step tick action present
  have filesystem := selected_filesystem_action_family action
  have safe := selected_primitive_action_authority journal selected
  have passive : NamespacePassive request := by simpa only [NamespacePassive, opening] using flags.symm
  have requestSafe : AuthoritySafeRequest request := by intro setting; rw [opening] at setting; cases setting
  have entries := namespaceLaws.operation (tick.before.project engine) tick.after.shared request observed actual passive
  have state := source_unchanged_filesystem_custody accounts objects metadata actual filesystem safe requestSafe
    prior.current.source.custody.namespaceState.project entries
  have names := filesystem_registered_root_names lookup filesystem safe
    prior.current.source.custody.namespaceState.registry prior.current.source.custody.names
  have owned := opened_filesystem_references_owned targets action present opening prior.current.source.custody.consistent
    (unchanged_existing_labels _ _ _) (by intro record member; exact member) prior.current.source.custody.references (by
      intro object owner target label
      have sameScope := private_child_target_scope targets prior.current.source.custody.namespaceState.project.graph
        actual target opening flags parentLive parentPrivate component notDot notUp
      have same : scope = owner := Option.some.inj (sameScope.symm.trans label)
      subst owner
      exact prior.current.source.custody.references actor engine present request.first parent scope parentLive parentPrivate)
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
  · exact no_root_use_of_other_operation action (by rw [opening]; decide)

end LeanCage.Host.Kernel
