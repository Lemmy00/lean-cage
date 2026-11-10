import FilesystemPrimitiveSelection
import FilesystemRootRegistration
import FilesystemLabelFlow

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.ownership: A scope keeps its actual birth even after its name is retired.
structure RootBirth {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) (ticks : List (ActorTick runtime))
    (root : PrivateRoot) where
  position : Nat
  tick : ActorTick runtime
  selected : ticks[position]? = some tick
  engine : EngineState
  present : tick.before.actors root.actor = some engine
  request : Request
  observed : Option Reply
  action : tick.action.eventFor root.actor = some (Program.filesystemPrefixEvent (request, observed))
  mkdir : request.op = .mkdirAt
  mode : request.second = 448
  component : Directories.component request.left = true
  reserved : PrivateNames.reservedBytes request.left = true
  parent : Handle
  reference : engine.references request.first = some parent
  parentObject : parent.object = root.parent
  name : request.left = root.name
  fresh : FreshBirth tick root.object
  absent : tick.before.shared.entries root.parent root.name = none
  bound : tick.after.shared.entries root.parent root.name = some root.object

abbrev Catalogue {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) (ticks : List (ActorTick runtime)) : Type 1 :=
  List (Sigma (RootBirth runtime ticks))

def Catalogue.Owns {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} {ticks : List (ActorTick runtime)}
    (catalogue : Catalogue runtime ticks) (actor : ActorId) (object : ObjectId) : Prop :=
  ∃ record ∈ catalogue, record.1.actor = actor ∧ record.1.object = object

def Catalogue.Covers {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} {ticks : List (ActorTick runtime)}
    (catalogue : Catalogue runtime ticks) (caps : Capabilities) : Prop :=
  ∀ root ∈ caps.roots, ∃ record ∈ catalogue, record.1 = root

structure Catalogue.Valid {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} {ticks : List (ActorTick runtime)}
    (catalogue : Catalogue runtime ticks) (world : World) : Prop where
  allocated : ∀ record ∈ catalogue, world.allocated record.1.object = true
  owner : ∀ left ∈ catalogue, ∀ right ∈ catalogue, left.1.object = right.1.object → left.1.actor = right.1.actor

-- §FS-host-boundary.ownership: These facts come from the actual source action and physical delta.
theorem root_birth_source_for {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final) {root : PrivateRoot}
    (birth : RootBirth runtime ticks root) :
    Program.Prefix sourceProgram
      (birth.engine.events ++ [Program.filesystemPrefixEvent (birth.request, birth.observed)]) ∧
    kernel.step (birth.tick.before.project birth.engine) birth.request birth.observed birth.tick.after.shared :=
  ⟨selected_source_prefix_for journal birth.selected birth.action birth.present,
    selected_filesystem_step birth.tick birth.action birth.present⟩

-- §AR-host-boundary.interfaces: Preserve the original logical-source specialization.
theorem root_birth_source {kernel : Contract} {runtime : ActorRuntime kernel}
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final) {root : PrivateRoot}
    (birth : RootBirth runtime ticks root) :
    Program.Prefix Entrypoint.run
      (birth.engine.events ++ [Program.filesystemPrefixEvent (birth.request, birth.observed)]) ∧
    kernel.step (birth.tick.before.project birth.engine) birth.request birth.observed birth.tick.after.shared :=
  root_birth_source_for journal birth

theorem root_birth_not_initial {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (lifetimes : LifetimeContract runtime) {initial : World} {final : Population}
    {ticks : List (ActorTick runtime)} (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {root : PrivateRoot} (birth : RootBirth runtime ticks root) : initial.allocated root.object = false := by
  obtain ⟨leading, trailing, shape⟩ := selected_tick_split birth.selected
  exact journal_birth_not_initial lifetimes journal shape birth.fresh

theorem catalogue_empty_covers {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) (ticks : List (ActorTick runtime)) :
    (Catalogue.Covers ([] : Catalogue runtime ticks) Capabilities.empty) := by
  intro root impossible
  cases impossible

theorem catalogue_add_covers {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} {ticks : List (ActorTick runtime)}
    {catalogue : Catalogue runtime ticks} {caps : Capabilities} {root : PrivateRoot}
    (covered : catalogue.Covers caps) (birth : RootBirth runtime ticks root) :
    Catalogue.Covers (Sigma.mk root birth :: catalogue) (caps.addRoot root) := by
  intro query member
  rcases List.mem_cons.mp member with rfl | old
  · exact ⟨⟨query, birth⟩, by simp, rfl⟩
  · obtain ⟨record, member, same⟩ := covered query old
    exact ⟨record, by simp [member], same⟩

theorem catalogue_retained_covers {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {ticks : List (ActorTick runtime)} {catalogue : Catalogue runtime ticks} {caps : Capabilities} {world : World}
    (covered : catalogue.Covers caps) : catalogue.Covers (caps.retain world) := by
  intro root member
  exact covered root (List.mem_filter.mp member).1

theorem catalogue_descendant_covers {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {ticks : List (ActorTick runtime)} {catalogue : Catalogue runtime ticks} {caps : Capabilities}
    {object scope : ObjectId} (covered : catalogue.Covers caps) : catalogue.Covers (caps.addDescendant object scope) :=
  covered

theorem catalogue_published_covers {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {ticks : List (ActorTick runtime)} {catalogue : Catalogue runtime ticks} {caps : Capabilities}
    {object : ObjectId} {world : World} (covered : catalogue.Covers caps) : catalogue.Covers (caps.published world object) :=
  catalogue_retained_covers covered

-- §FS-host-boundary.ownership: Retiring a name does not transfer the old scope to another actor.
theorem catalogue_scope_owner {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {ticks : List (ActorTick runtime)} {catalogue : Catalogue runtime ticks} {caps : Capabilities}
    {root : PrivateRoot} (covered : catalogue.Covers caps) (member : root ∈ caps.roots) :
    catalogue.Owns root.actor root.object := by
  obtain ⟨record, present, same⟩ := covered root member
  exact ⟨record, present, by rw [same], by rw [same]⟩

theorem catalogue_empty_valid {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) (ticks : List (ActorTick runtime))
    (world : World) : Catalogue.Valid ([] : Catalogue runtime ticks) world := by
  constructor <;> intro record impossible <;> cases impossible

theorem catalogue_advance_valid {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {ticks : List (ActorTick runtime)} {catalogue : Catalogue runtime ticks} {before after : World}
    (valid : catalogue.Valid before)
    (allocation : ∀ object, before.allocated object = true → after.allocated object = true) :
    catalogue.Valid after :=
  ⟨fun record member => allocation _ (valid.allocated record member), valid.owner⟩

-- §FS-host-boundary.ownership: Same-name collisions cannot replace an older lifetime's owner.
theorem catalogue_add_valid {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (lifetimes : LifetimeContract runtime) {ticks : List (ActorTick runtime)}
    {catalogue : Catalogue runtime ticks} {root : PrivateRoot} (birth : RootBirth runtime ticks root)
    (valid : catalogue.Valid birth.tick.before.shared) :
    Catalogue.Valid (Sigma.mk root birth :: catalogue) birth.tick.after.shared := by
  have different : ∀ record ∈ catalogue, root.object ≠ record.1.object := by
    intro record member same
    have allocated := valid.allocated record member
    rw [← same, birth.fresh.1] at allocated
    cases allocated
  constructor
  · intro record member
    rcases List.mem_cons.mp member with rfl | old
    · exact birth.fresh.2
    · exact actor_step_allocated lifetimes birth.tick.operation _ (valid.allocated record old)
  · intro left leftMember right rightMember sameObject
    rcases List.mem_cons.mp leftMember with rfl | leftOld
    · rcases List.mem_cons.mp rightMember with rfl | rightOld
      · rfl
      · exact False.elim (different right rightOld sameObject)
    · rcases List.mem_cons.mp rightMember with rfl | rightOld
      · exact False.elim (different left leftOld sameObject.symm)
      · exact valid.owner left leftOld right rightOld sameObject

theorem catalogue_unique_owner {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {ticks : List (ActorTick runtime)} {catalogue : Catalogue runtime ticks} {world : World}
    {first second : ActorId} {object : ObjectId} (valid : catalogue.Valid world)
    (left : catalogue.Owns first object) (right : catalogue.Owns second object) : first = second := by
  obtain ⟨leftRecord, leftMember, leftOwner, leftObject⟩ := left
  obtain ⟨rightRecord, rightMember, rightOwner, rightObject⟩ := right
  have same := valid.owner leftRecord leftMember rightRecord rightMember (leftObject.trans rightObject.symm)
  exact leftOwner.symm.trans (same.trans rightOwner)

end LeanCage.Host.Kernel
