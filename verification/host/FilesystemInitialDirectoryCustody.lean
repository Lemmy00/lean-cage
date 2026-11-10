import FilesystemRegisteredCustody
import FilesystemPassiveCustody

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: Root and inherited-CWD opens have no guessed parent FD.
-- Their actual target is initialized root state or the same live actor's inherited CWD.
theorem initial_directory_target_public {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {native : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before native)
    (targets : OpenTargetContract kernel semantics initial.allocated dataObjects)
    {actor : ActorId} {engine : EngineState} (present : tick.before.actors actor = some engine)
    {request : Request} {observed : Option Reply} {object : ObjectId}
    (actual : kernel.step (tick.before.project engine) request observed tick.after.shared)
    (target : targets.target (tick.before.project engine) request observed tick.after.shared object)
    (opening : request.op = .openAt) (flags : request.second = directoryFlags)
    (base : request.first = cwd) (path : request.left = "/".toUTF8 ∨ request.left = ".".toUTF8) :
    prior.current.source.custody.caps.family object = none := by
  rcases path with rootPath | currentPath
  · have initialized := targets.root _ _ _ _ _ actual target opening flags base rootPath
    cases label : prior.current.source.custody.caps.family object with
    | none => rfl
    | some scope =>
      have young := prior.current.source.custody.namespaceState.graph.young _ _ label
      rw [initialized] at young
      cases young
  · have same := targets.cwd _ _ _ _ _ actual target opening flags base currentPath
    exact same ▸ prior.current.directoriesPublic actor engine present

-- §FS-host-boundary.acceptance: An initial directory open can introduce a descriptor on
-- error/loss. The exact target still derives public custody from this SAME actor and prefix.
theorem initial_directory_open_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    (namespaceLaws : PassiveNamespaceContract kernel) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (targets : OpenTargetContract kernel semantics initial.allocated dataObjects)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    {position : Nat} (selected : all[position]? = some tick) {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (opening : request.op = .openAt)
    (flags : request.second = directoryFlags) (base : request.first = cwd)
    (path : request.left = "/".toUTF8 ∨ request.left = ".".toUTF8) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative) := by
  have actual := selected_filesystem_step tick action present
  have filesystem := selected_filesystem_action_family action
  have safe := selected_primitive_action_authority journal selected
  have passive : NamespacePassive request := by simp only [NamespacePassive, opening]; exact .inr flags
  have requestSafe : AuthoritySafeRequest request := by intro setting; rw [opening] at setting; cases setting
  have entries := namespaceLaws.operation (tick.before.project engine) tick.after.shared request observed actual passive
  have state := source_unchanged_filesystem_custody accounts objects metadata actual filesystem safe requestSafe
    prior.current.source.custody.namespaceState.project entries
  have names := filesystem_registered_root_names lookup filesystem safe
    prior.current.source.custody.namespaceState.registry prior.current.source.custody.names
  have owned := opened_filesystem_references_owned targets action present opening
    prior.current.source.custody.consistent (unchanged_existing_labels _ _ _)
    (by intro record member; exact member) prior.current.source.custody.references
    (by
      intro object scope target label
      have publicObject := initial_directory_target_public prior targets present actual target opening flags base path
      change prior.current.source.custody.caps.family object = some scope at label
      rw [publicObject] at label
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
  · intro query handles closeExec directory impossible
    rw [impossible] at action
    cases action
  · exact no_root_use_of_other_operation action (by rw [opening]; decide)

end LeanCage.Host.Kernel
