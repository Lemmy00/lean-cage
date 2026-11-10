import FilesystemRegisteredCustody
import FilesystemSourceIntervals
import FilesystemOpenTargets
import FilesystemPassiveCustody

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: An exact earlier acknowledged root call selects its own
-- recorded birth. The caller's actual finite source suffix supplies the read/probe profile.
-- No current binding, owner, private-region frame, or unrelated RootBirth is an input.
theorem registered_root_current_nondestructive {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (lifetimes : LifetimeContract runtime)
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {population : Population} {native : NativeProcesses}
    (state : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed population native)
    {position : Nat} {tick : ActorTick runtime} (selected : processed[position]? = some tick)
    (use : PrimitiveRootUse runtime initial all tick) {engine : EngineState}
    (present : population.actors use.actor = some engine)
    (source : ∀ event ∈ engine.events.drop (use.engine.events.length + 1), NondestructiveEvent event) :
    ∃ (root : PrivateRoot) (birth : RootBirth runtime all root), birth.tick = tick ∧ birth.position = position ∧
      Sigma.mk root birth ∈ state.current.source.custody.catalogue ∧ root.actor = use.actor ∧
      root.parent = use.parent.object ∧ root.name = use.request.left ∧
      population.shared.entries use.parent.object use.request.left = some root.object ∧
      state.current.source.custody.caps.family root.object = some root.object ∧
      state.current.source.custody.caps.family use.parent.object = none ∧
      state.current.source.custody.catalogue.Owns use.actor root.object := by
  obtain ⟨root, birth, current, ordinal, member, owner, parent, name, cut⟩ := state.root_scope selected use
  obtain ⟨cut⟩ := cut
  obtain ⟨first, firstPresent, trace⟩ := source_event_after tick use.action use.present
  have presentAtBirth : birth.tick.after.actors use.actor = some first := by rwa [current]
  have count : first.events.length = use.engine.events.length + 1 := by
    simp only [trace, List.length_append, List.length_singleton]
  have actualSource := actor_interval_nondestructive_profile cut.ownership.actual presentAtBirth present
    (by rw [count]; exact source)
  have owned : state.current.source.custody.catalogue.Owns use.actor root.object :=
    ⟨Sigma.mk root birth, member, owner, rfl⟩
  obtain ⟨bound, label⟩ := cut.ownership.private_binding_retained_nondestructive lifetimes state.current.source.custody.valid owned
    birth.fresh.2 cut.privateRoot birth.bound actualSource
  exact ⟨root, birth, current, ordinal, member, owner, parent, name, by simpa only [parent, name] using bound,
    label, by simpa only [parent] using cut.parentPublic, owned⟩

-- §AR-host-boundary.interfaces: The original reopen consumer retains its exact type.
theorem registered_root_current {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (lifetimes : LifetimeContract runtime)
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {population : Population} {native : NativeProcesses}
    (state : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed population native)
    {position : Nat} {tick : ActorTick runtime} (selected : processed[position]? = some tick)
    (use : PrimitiveRootUse runtime initial all tick) {engine : EngineState}
    (present : population.actors use.actor = some engine)
    (source : ∀ event ∈ engine.events.drop (use.engine.events.length + 1), NamespacePassiveEvent event) :
    ∃ (root : PrivateRoot) (birth : RootBirth runtime all root), birth.tick = tick ∧ birth.position = position ∧
      Sigma.mk root birth ∈ state.current.source.custody.catalogue ∧ root.actor = use.actor ∧
      root.parent = use.parent.object ∧ root.name = use.request.left ∧
      population.shared.entries use.parent.object use.request.left = some root.object ∧
      state.current.source.custody.caps.family root.object = some root.object ∧
      state.current.source.custody.caps.family use.parent.object = none ∧
      state.current.source.custody.catalogue.Owns use.actor root.object := by
  apply registered_root_current_nondestructive lifetimes state selected use present
  intro event member
  have passive := source event member
  cases event with
  | @returned β effect reply =>
    cases effect <;> dsimp only [NondestructiveEvent] <;> first
      | exact namespace_passive_not_destructive passive
      | exact True.intro
  | @lost β effect =>
    cases effect <;> dsimp only [NondestructiveEvent] <;> first
      | exact namespace_passive_not_destructive passive
      | exact True.intro

-- §FS-host-boundary.lookup: The current stored binding and registered exact comparison
-- identify this real open target, including an introduced FD with an error or lost reply.
theorem root_reopen_target_owned {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime}
    {caps : Capabilities} {catalogue : Catalogue runtime all}
    (targets : OpenTargetContract kernel semantics initial.allocated dataObjects)
    (state : NamespaceCustody tick.before.shared caps hostUid initial.allocated dataObjects directories foreignReferences)
    (names : RegisteredRootNames caps semantics tick.before.shared)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {parent : Handle} {root : ObjectId}
    (actual : kernel.step (tick.before.project engine) request observed tick.after.shared)
    (opening : request.op = .openAt) (flags : request.second = directoryFlags)
    (reference : engine.references request.first = some parent)
    (component : Directories.component request.left = true)
    (notDot : request.left ≠ ".".toUTF8) (notUp : request.left ≠ "..".toUTF8)
    (bound : tick.before.shared.entries parent.object request.left = some root)
    (privateRoot : caps.family root = some root) (publicParent : caps.family parent.object = none)
    (owner : catalogue.Owns actor root) {object scope : ObjectId}
    (target : targets.target (tick.before.project engine) request observed tick.after.shared object)
    (privateObject : caps.family object = some scope) : catalogue.Owns actor scope := by
  have comparison := registered_boundaries_exact state.boundaries names _ _ _ _ bound privateRoot publicParent
  rcases targets.child _ _ _ _ _ _ actual target opening (.inl flags) reference component notDot notUp
      (state.graph.data object scope privateObject) with ⟨storedName, stored, sameName⟩ | old
  · have name := sameName comparison
    change tick.before.shared.entries parent.object storedName = some object at stored
    rw [name, bound] at stored
    have same := Option.some.inj stored
    subst object
    have scopeSame : scope = root := Option.some.inj (privateObject.symm.trans privateRoot)
    simpa only [scopeSame] using owner
  · have young := state.graph.young object scope privateObject
    rw [old] at young
    cases young

-- §FS-host-boundary.ownership: The real directory reopen consumes the actual earlier
-- source-registered mkdir and its read/probe-only suffix, then extends the common state.
-- Both hostile acknowledgement loss and an introduced descriptor remain in this case.
theorem root_reopen_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    {birthPosition : Nat} {birthTick : ActorTick runtime} (birthAt : processed[birthPosition]? = some birthTick)
    (use : PrimitiveRootUse runtime initial all birthTick)
    {position : Nat} (selected : all[position]? = some tick) {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor use.actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors use.actor = some engine) (opening : request.op = .openAt)
    (flags : request.second = directoryFlags) (sameName : request.left = use.request.left)
    (reference : engine.references request.first = some use.parent)
    (notDot : request.left ≠ ".".toUTF8) (notUp : request.left ≠ "..".toUTF8)
    (source : ∀ event ∈ engine.events.drop (use.engine.events.length + 1), NamespacePassiveEvent event) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative) := by
  obtain ⟨root, birth, current, ordinal, member, owner, parent, name, bound, privateRoot, publicParent, ownedRoot⟩ :=
    registered_root_current lifetimes prior birthAt use present source
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
  have component : Directories.component request.left = true := by rw [sameName]; exact use.component
  have owned := opened_filesystem_references_owned targets action present opening
    prior.current.source.custody.consistent (unchanged_existing_labels _ _ _)
    (by intro record member; exact member) prior.current.source.custody.references
    (fun object scope target label => root_reopen_target_owned targets prior.current.source.custody.namespaceState
      prior.current.source.custody.names actual opening flags reference component notDot notUp
      (by rwa [sameName]) privateRoot publicParent ownedRoot target label)
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
  · intro actor handles closeExec directory impossible
    rw [impossible] at action
    cases action
  · exact no_root_use_of_other_operation action (by rw [opening]; decide)

end LeanCage.Host.Kernel
