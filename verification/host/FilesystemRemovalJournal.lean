import FilesystemRootCatalogue
import FilesystemSourceKinds

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

def DestructiveRequest (request : Request) : Prop := request.op = .unlinkAt ∨ request.op = .renameNew

-- §FS-host-boundary.ownership: This is application-produced provenance for one actual
-- destructive source call. A callback/native row cannot obtain it from an actor-role label.
def OwnerMutation {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {ticks : List (ActorTick runtime)} (catalogue : Catalogue runtime ticks)
    (tick : ActorTick runtime) (scope : ObjectId) : Prop :=
  ∃ actor request observed,
    tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)) ∧
    DestructiveRequest request ∧ catalogue.Owns actor scope

structure CustodyOwnershipStep {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {ticks : List (ActorTick runtime)} (catalogue : Catalogue runtime ticks)
    (tick : ActorTick runtime) (before after : Family) : Prop where
  removed : ∀ parent name object scope, tick.before.shared.entries parent name = some object →
    before object = some scope → tick.after.shared.entries parent name ≠ some object →
    OwnerMutation catalogue tick scope
  released : ∀ object scope, tick.before.shared.allocated object = true → before object = some scope →
    after object ≠ some scope → OwnerMutation catalogue tick scope

theorem OwnerMutation.weaken {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {ticks : List (ActorTick runtime)} {before after : Catalogue runtime ticks}
    (included : ∀ record ∈ before, record ∈ after) {tick : ActorTick runtime} {scope : ObjectId}
    (source : OwnerMutation before tick scope) : OwnerMutation after tick scope := by
  obtain ⟨actor, request, observed, selected, destructive, record, member, owner, identity⟩ := source
  exact ⟨actor, request, observed, selected, destructive, record, included record member, owner, identity⟩

theorem CustodyOwnershipStep.weaken {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {ticks : List (ActorTick runtime)} {before after : Catalogue runtime ticks}
    (included : ∀ record ∈ before, record ∈ after) {tick : ActorTick runtime} {first final : Family}
    (step : CustodyOwnershipStep before tick first final) : CustodyOwnershipStep after tick first final :=
  ⟨fun parent name object scope bound label removed =>
    (step.removed parent name object scope bound label removed).weaken included,
    fun object scope allocated label released =>
      (step.released object scope allocated label released).weaken included⟩

-- §FS-host-boundary.ownership: This journal is built by the source/physical custody fold.
-- It is not a runtime assumption that a complete helper preserves a private region.
inductive OwnershipJournal {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram)
    {all : List (ActorTick runtime)} (catalogue : Catalogue runtime all) :
    Population → Family → List (ActorTick runtime) → Population → Family → Prop where
  | nil (population : Population) (family : Family) :
      OwnershipJournal runtime catalogue population family [] population family
  | cons {tick : ActorTick runtime} {ticks : List (ActorTick runtime)} {after : Population}
      {first middle final : Family} (step : CustodyOwnershipStep catalogue tick first middle)
      (tail : OwnershipJournal runtime catalogue tick.after middle ticks after final) :
      OwnershipJournal runtime catalogue tick.before first (tick :: ticks) after final

theorem OwnershipJournal.weaken {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {all : List (ActorTick runtime)} {beforeCatalogue afterCatalogue : Catalogue runtime all}
    (included : ∀ record ∈ beforeCatalogue, record ∈ afterCatalogue)
    {before after : Population} {first final : Family} {ticks : List (ActorTick runtime)}
    (journal : OwnershipJournal runtime beforeCatalogue before first ticks after final) :
    OwnershipJournal runtime afterCatalogue before first ticks after final := by
  induction journal with
  | nil => exact .nil _ _
  | cons step tail ih => exact .cons (step.weaken included) ih

theorem OwnershipJournal.append {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {all : List (ActorTick runtime)} {catalogue : Catalogue runtime all}
    {before middle after : Population} {first between final : Family} {leading trailing : List (ActorTick runtime)}
    (initial : OwnershipJournal runtime catalogue before first leading middle between)
    (last : OwnershipJournal runtime catalogue middle between trailing after final) :
    OwnershipJournal runtime catalogue before first (leading ++ trailing) after final := by
  induction initial with
  | nil => exact last
  | cons step tail ih => exact .cons step (ih last)

theorem namespace_passive_not_destructive {request : Request} (passive : NamespacePassive request) :
    ¬ DestructiveRequest request := by
  intro destructive
  unfold NamespacePassive at passive
  rcases destructive with removing | moving
  · rw [removing] at passive; exact passive
  · rw [moving] at passive; exact passive

-- §FS-host-boundary.ownership: Only that recorded owner can retire a private binding or
-- release its scope. The owner's read/probe-only interval therefore keeps the SAME birth.
theorem OwnershipJournal.private_binding_retained_nondestructive {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (lifetimes : LifetimeContract runtime) {all : List (ActorTick runtime)} {catalogue : Catalogue runtime all}
    {before after : Population} {first final : Family} {ticks : List (ActorTick runtime)}
    (journal : OwnershipJournal runtime catalogue before first ticks after final)
    (valid : catalogue.Valid after.shared) {actor : ActorId} {parent object scope : ObjectId} {name : ByteArray}
    (owner : catalogue.Owns actor scope) (allocated : before.shared.allocated object = true)
    (privateObject : first object = some scope) (bound : before.shared.entries parent name = some object)
    (quiet : ∀ tick ∈ ticks, ∀ request observed,
      tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)) → ¬ DestructiveRequest request) :
    after.shared.entries parent name = some object ∧ final object = some scope := by
  have cannotMutate : ∀ tick ∈ ticks, ¬ OwnerMutation catalogue tick scope := by
    intro tick member mutation
    obtain ⟨query, request, observed, selected, destructive, otherOwner⟩ := mutation
    have same := catalogue_unique_owner valid otherOwner owner
    subst query
    exact quiet tick member request observed selected destructive
  induction journal with
  | nil => exact ⟨bound, privateObject⟩
  | @cons tick ticks after first middle final step tail ih =>
    have retainedBinding : tick.after.shared.entries parent name = some object := by
      by_cases kept : tick.after.shared.entries parent name = some object
      · exact kept
      · exact False.elim (cannotMutate tick (by simp) (step.removed parent name object scope bound privateObject kept))
    have retainedLabel : middle object = some scope := by
      by_cases kept : middle object = some scope
      · exact kept
      · exact False.elim (cannotMutate tick (by simp) (step.released object scope allocated privateObject kept))
    exact ih valid (actor_step_allocated lifetimes tick.operation object allocated) retainedLabel retainedBinding
      (by intro tick member request observed selected; exact quiet tick (by simp [member]) request observed selected)
      (by intro tick member; exact cannotMutate tick (by simp [member]))

-- §AR-host-boundary.interfaces: The original read/probe consumer is a specialization;
-- source-owned content creation and writes need only exclude actual removals/publication.
theorem OwnershipJournal.private_binding_retained {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (lifetimes : LifetimeContract runtime) {all : List (ActorTick runtime)} {catalogue : Catalogue runtime all}
    {before after : Population} {first final : Family} {ticks : List (ActorTick runtime)}
    (journal : OwnershipJournal runtime catalogue before first ticks after final)
    (valid : catalogue.Valid after.shared) {actor : ActorId} {parent object scope : ObjectId} {name : ByteArray}
    (owner : catalogue.Owns actor scope) (allocated : before.shared.allocated object = true)
    (privateObject : first object = some scope) (bound : before.shared.entries parent name = some object)
    (quiet : ∀ tick ∈ ticks, ∀ request observed,
      tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)) → NamespacePassive request) :
    after.shared.entries parent name = some object ∧ final object = some scope :=
  journal.private_binding_retained_nondestructive lifetimes valid owner allocated privateObject bound
    (fun tick member request observed selected =>
      namespace_passive_not_destructive (quiet tick member request observed selected))

-- §FS-host-boundary.ownership: Passive deltas and fresh births preserve every older binding
-- and label directly. They require no owner premise and include committed error/loss births.
theorem nonremoving_ownership_step {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {all : List (ActorTick runtime)} (catalogue : Catalogue runtime all) {tick : ActorTick runtime}
    {first final : Family}
    (entries : ∀ parent name object, tick.before.shared.entries parent name = some object →
      tick.after.shared.entries parent name = some object)
    (labels : ∀ object, tick.before.shared.allocated object = true → final object = first object) :
    CustodyOwnershipStep catalogue tick first final := by
  constructor
  · intro parent name object scope bound label missing
    exact False.elim (missing (entries parent name object bound))
  · intro object scope allocated label released
    exact False.elim (released ((labels object allocated).trans label))

end LeanCage.Host.Kernel
