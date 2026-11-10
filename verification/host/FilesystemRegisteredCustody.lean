import FilesystemRootRegistrationHistory
import FilesystemCustodyState

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: The actual source fold constructs this state, including the
-- converse source-mkdir registration fact. It is never an assumed kernel/helper safety frame.
structure RegisteredCustodyState {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (all : List (ActorTick runtime)) (hostUid : Nat)
    (dataObjects directories : ObjectId → Prop) (semantics : NameSemanticsView)
    (foreignReferences : ForeignReferences) (processed : List (ActorTick runtime))
    (population : Population) (native : NativeProcesses) where
  current : CustodyState runtime initial all hostUid dataObjects directories semantics
    foreignReferences processed population native
  registrations : RootRegistrationHistory runtime initial all 0 Capabilities.empty [] processed
    current.source.custody.caps current.source.custody.catalogue

def initial_registered_custody {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (all : List (ActorTick runtime)) (hostUid : Nat)
    (dataObjects directories : ObjectId → Prop) (semantics : NameSemanticsView)
    (foreignReferences : ForeignReferences) (native : NativeProcesses)
    (wellFormed : NamespaceWellFormed initial)
    (live : ∀ object, foreignReferences object = true → initial.allocated object = true)
    (nativeLive : NativeReferencesLive native initial) :
    RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences [] (Population.empty initial) native :=
  ⟨initial_custody_state runtime initial all hostUid dataObjects directories semantics foreignReferences native
    wellFormed live nativeLive, .nil _ _ _⟩

def RegisteredCustodyState.creation {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignBefore foreignAfter : ForeignReferences} {tick : ActorTick runtime} {before after : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignBefore processed tick.before before)
    (next : CustodyState runtime initial all hostUid dataObjects directories semantics
      foreignAfter (processed ++ [tick]) tick.after after)
    (choice : CurrentRootCreation prior.current.source.custody.caps prior.current.source.custody.catalogue
      next.source.custody.caps next.source.custody.catalogue tick processed.length) :
    RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignAfter (processed ++ [tick]) tick.after after := by
  refine ⟨next, prior.registrations.append ?_⟩
  simp only [Nat.zero_add]
  exact .creation choice (.nil _ _ _)

def RegisteredCustodyState.other {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignBefore foreignAfter : ForeignReferences} {tick : ActorTick runtime} {before after : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignBefore processed tick.before before)
    (next : CustodyState runtime initial all hostUid dataObjects directories semantics
      foreignAfter (processed ++ [tick]) tick.after after)
    (source : ¬ Nonempty (PrimitiveRootUse runtime initial all tick))
    (catalogue : next.source.custody.catalogue = prior.current.source.custody.catalogue) :
    RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignAfter (processed ++ [tick]) tick.after after := by
  refine ⟨next, prior.registrations.append ?_⟩
  rw [catalogue]
  exact .other source (.nil _ _ _)

-- §FS-host-boundary.ownership: A derived non-root source case extends both histories;
-- native/foreign table updates retain their separate actual per-operation constructors.
def RegisteredCustodyState.sourceStep {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (sdk : RuntimeDescriptorContract runtime) (lifetimes : LifetimeContract runtime)
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignBefore foreignAfter : ForeignReferences} {tick : ActorTick runtime} {native : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignBefore processed tick.before native)
    (next : OwnershipPrefix runtime initial all hostUid dataObjects directories semantics
      foreignAfter (processed ++ [tick]) tick.after)
    (notLaunch : ∀ actor references closeExec directory, tick.action ≠ .launch actor references closeExec directory)
    (labels : ExistingLabels tick.before.shared tick.after.shared prior.current.source.custody.caps.family next.custody.caps.family)
    (catalogue : next.custody.catalogue = prior.current.source.custody.catalogue)
    (ownership : CustodyOwnershipStep next.custody.catalogue tick
      prior.current.source.custody.caps.family next.custody.caps.family)
    (source : ¬ Nonempty (PrimitiveRootUse runtime initial all tick)) :
    RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignAfter (processed ++ [tick]) tick.after native := by
  let state := prior.current.application sdk lifetimes next notLaunch labels
    (by rw [catalogue]; exact fun _ member => member)
    (by rw [catalogue]; exact fun _ member => .inl member) ownership
  exact prior.other state source catalogue

-- §FS-host-boundary.ownership: A later source use selects its own earlier real acknowledged
-- mkdir and obtains both its exact catalogue entry and the retained SAME-birth ownership cut.
theorem RegisteredCustodyState.root_scope {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {population : Population} {native : NativeProcesses}
    (state : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed population native)
    {position : Nat} {tick : ActorTick runtime} (selected : processed[position]? = some tick)
    (use : PrimitiveRootUse runtime initial all tick) :
    ∃ (root : PrivateRoot) (birth : RootBirth runtime all root), birth.tick = tick ∧ birth.position = position ∧
      Sigma.mk root birth ∈ state.current.source.custody.catalogue ∧
      root.actor = use.actor ∧ root.parent = use.parent.object ∧ root.name = use.request.left ∧
      Nonempty (BirthScopeAt runtime state.current.source.custody.catalogue processed population
        state.current.source.custody.caps.family (Sigma.mk root birth)) := by
  obtain ⟨root, birth, current, ordinal, member, actor, parent, name⟩ := state.registrations.registered selected use
  exact ⟨root, birth, current, by simpa only [Nat.zero_add] using ordinal, member, actor, parent, name,
    state.current.births _ member⟩

end LeanCage.Host.Kernel
