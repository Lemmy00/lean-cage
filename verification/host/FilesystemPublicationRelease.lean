import FilesystemCustodyExecution
import FilesystemCommitRoot

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: Unlinking owned contents does not publish a scope.
-- This source-produced event names the one actual rename and its recorded owner.
def OwnerPublication {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {all : List (ActorTick runtime)} (catalogue : Catalogue runtime all)
    (tick : ActorTick runtime) (scope : ObjectId) : Prop :=
  ∃ actor request observed,
    tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)) ∧
    request.op = .renameNew ∧ catalogue.Owns actor scope

def PublicationReleaseStep {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {all : List (ActorTick runtime)} (catalogue : Catalogue runtime all)
    (tick : ActorTick runtime) (before after : Family) : Prop :=
  ∀ object scope, tick.before.shared.allocated object = true → before object = some scope →
    after object ≠ some scope → OwnerPublication catalogue tick scope

theorem OwnerPublication.weaken {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {all : List (ActorTick runtime)} {before after : Catalogue runtime all}
    (included : ∀ record ∈ before, record ∈ after) {tick : ActorTick runtime} {scope : ObjectId}
    (source : OwnerPublication before tick scope) : OwnerPublication after tick scope := by
  obtain ⟨actor, request, observed, action, moving, record, member, owner, identity⟩ := source
  exact ⟨actor, request, observed, action, moving, record, included record member, owner, identity⟩

theorem PublicationReleaseStep.weaken {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {all : List (ActorTick runtime)} {before after : Catalogue runtime all}
    (included : ∀ record ∈ before, record ∈ after) {tick : ActorTick runtime} {first final : Family}
    (source : PublicationReleaseStep before tick first final) : PublicationReleaseStep after tick first final :=
  fun object scope allocated label released => (source object scope allocated label released).weaken included

theorem publication_release_unchanged {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {all : List (ActorTick runtime)} (catalogue : Catalogue runtime all) {tick : ActorTick runtime} {first final : Family}
    (same : ∀ object, tick.before.shared.allocated object = true → final object = first object) :
    PublicationReleaseStep catalogue tick first final := by
  intro object scope allocated label released
  exact False.elim (released ((same object allocated).trans label))

-- §FS-host-boundary.publication: Clearing a family is justified by THIS actual
-- source commit, not by an unlink, a failed helper, or a future acknowledged result.
theorem publication_release_commit {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {resources : PrimitiveCommitResources runtime initial all tick actor engine request observed}
    {family : Family} {catalogue : Catalogue runtime all} (root : CommitRootAt runtime resources family catalogue)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (moving : request.op = .renameNew) : PublicationReleaseStep catalogue tick family (clearFamily family root.root.object) := by
  intro object scope allocated label released
  have same : scope = root.root.object := by
    apply Classical.byContradiction
    intro different
    have distinct : family object ≠ some root.root.object := by
      intro actual
      exact different (Option.some.inj (label.symm.trans actual))
    apply released
    simp only [clearFamily, ite_eq_right distinct]
    exact label
  exact ⟨actor, request, observed, action, moving, same.symm ▸ root.owned⟩

private def native_step_tick {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {first last : NativeProcesses} {tick : ActorTick runtime}
    (_source : NativeExternalStep process child native hostUid before first tick after last) : ActorTick runtime := tick

-- §FS-host-boundary.ownership: Each release certificate is computed over the
-- adjacent snapshots in the SAME constructed execution, including its exact
-- native/source head. It is application induction evidence, not a primitive frame.
def PublicationReleaseExecution {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {initial : World} {all : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {before after : Processes} {first last : NativeProcesses} {ticks processed : List (ActorTick runtime)}
    {start finish : Population}
    {recording : NativeExternalJournal process child native hostUid before first ticks after last} :
    RegisteredCustodyExecution runtime initial all hostUid dataObjects directories semantics recording
      processed start finish → Prop
  | .nil _ => True
  | .cons current _ state tail =>
    (∀ record ∈ state.current.source.custody.catalogue, record ∈ tail.before.2.current.source.custody.catalogue) ∧
    PublicationReleaseStep tail.before.2.current.source.custody.catalogue (native_step_tick current) state.current.source.custody.caps.family
      tail.before.2.current.source.custody.caps.family ∧ PublicationReleaseExecution tail

-- §FS-host-boundary.ownership: The row journal retains exact family changes and
-- owner publications. It is built from the application step certificates above.
inductive PublicationReleaseJournal {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    {all : List (ActorTick runtime)} (catalogue : Catalogue runtime all) :
    Population → Family → List (ActorTick runtime) → Population → Family → Prop where
  | nil (population : Population) (family : Family) :
      PublicationReleaseJournal runtime catalogue population family [] population family
  | cons {tick : ActorTick runtime} {ticks : List (ActorTick runtime)} {after : Population}
      {first middle final : Family} (source : PublicationReleaseStep catalogue tick first middle)
      (tail : PublicationReleaseJournal runtime catalogue tick.after middle ticks after final) :
      PublicationReleaseJournal runtime catalogue tick.before first (tick :: ticks) after final

theorem PublicationReleaseJournal.weaken {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {all : List (ActorTick runtime)} {prior final : Catalogue runtime all}
    (included : ∀ record ∈ prior, record ∈ final)
    {before after : Population} {first last : Family} {ticks : List (ActorTick runtime)}
    (source : PublicationReleaseJournal runtime prior before first ticks after last) :
    PublicationReleaseJournal runtime final before first ticks after last := by
  induction source with
  | nil => exact .nil _ _
  | cons current tail ih => exact .cons (current.weaken included) ih

-- §FS-host-boundary.ownership: Ordinary owned cleanup can remove descendants while
-- keeping the root's private family. Releasing it requires the same owner's actual
-- publication event; no assertion that all cleanup calls are nondestructive is used.
theorem PublicationReleaseJournal.private_label_retained {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (lifetimes : LifetimeContract runtime) {all : List (ActorTick runtime)} {catalogue : Catalogue runtime all}
    {before after : Population} {first final : Family} {ticks : List (ActorTick runtime)}
    (journal : PublicationReleaseJournal runtime catalogue before first ticks after final)
    {observedWorld : World} (valid : catalogue.Valid observedWorld) {actor : ActorId} {object scope : ObjectId}
    (owned : catalogue.Owns actor scope) (old : before.shared.allocated object = true) (label : first object = some scope)
    (source : ∀ tick ∈ ticks, ∀ request observed,
      tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)) → request.op ≠ .renameNew) :
    final object = some scope := by
  induction journal with
  | nil => exact label
  | @cons tick ticks after first middle final current tail ih =>
    have kept : middle object = some scope := by
      apply Classical.byContradiction
      intro released
      obtain ⟨owner, request, observed, action, moving, mutation⟩ := current object scope old label released
      have same := catalogue_unique_owner valid mutation owned
      subst owner
      exact source tick (by simp) request observed action moving
    exact ih (actor_step_allocated lifetimes tick.operation object old) kept
      (by intro row member request observed action; exact source row (by simp [member]) request observed action)

end LeanCage.Host.Kernel
