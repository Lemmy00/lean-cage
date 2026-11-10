import FilesystemRootCatalogue
import FilesystemIntervals
import FilesystemNativeMetadata
import FilesystemBoundaries

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.ownership: A currently allocated lifetime cannot have its first actual
-- birth at this or a later global position. No ordering of finite inode numbers is used.
theorem RootBirth.precedes_allocated {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (lifetimes : LifetimeContract runtime) {initial final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime initial ticks final) {root : PrivateRoot} (birth : RootBirth runtime ticks root)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick)
    (allocated : tick.before.shared.allocated root.object = true) : birth.position < position := by
  apply Classical.byContradiction
  intro notEarlier
  have order : position ≤ birth.position := by omega
  obtain ⟨leading, inside, trailing, shape, region⟩ := journal_between_selected journal selected birth.selected order
  have later := actor_journal_allocated lifetimes region root.object allocated
  rw [birth.fresh.1] at later
  cases later

-- §FS-host-boundary.ownership: A still-bound actual private birth keeps its parent active
-- even after unknown-child handling has released every source raw descriptor.
structure BoundaryParentLease {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram)
    (ticks : List (ActorTick runtime)) (position : Nat) (population : Population) (hostUid : Nat) (object : ObjectId) where
  root : PrivateRoot
  birth : RootBirth runtime ticks root
  earlier : birth.position < position
  parent : root.parent = object
  bound : population.shared.entries root.parent root.name = some root.object
  information : Stat
  known : population.shared.information object = some information
  trusted : Directories.trusted hostUid information = true

-- §FS-host-boundary.ownership: The lease is constructed from the actual birth catalogue and
-- current namespace/authority induction state; an external caller cannot invent its role.
theorem actual_boundary_parent_lease {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (lifetimes : LifetimeContract runtime) {initial final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime initial ticks final)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick)
    {caps : Capabilities} (catalogue : Catalogue runtime ticks) (covered : catalogue.Covers caps)
    (valid : caps.Valid tick.before.shared) {hostUid : Nat}
    (authorities : RootAuthorities caps tick.before.shared hostUid) {root : PrivateRoot}
    (member : root ∈ caps.roots) :
    Nonempty (BoundaryParentLease runtime ticks position tick.before hostUid root.parent) := by
  obtain ⟨record, belongs, sameRoot⟩ := covered root member
  obtain ⟨childInfo, parentInfo, childKnown, parentKnown, owner, mode, directory, trusted⟩ := authorities root member
  have birth : RootBirth runtime ticks root := sameRoot ▸ record.2
  exact ⟨⟨root, birth, birth.precedes_allocated lifetimes journal selected (valid.1 root member).1,
    rfl, (valid.1 root member).2.2.1, parentInfo, parentKnown, trusted⟩⟩

-- §FS-host-boundary.ownership: Profile1 excludes only actual authority changes at this same
-- active boundary parent. Public content/name operations and harmless setters remain possible.
def NativeBoundaryAuthorityProfile {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (native : NativePrimitive kernel) (ticks : List (ActorTick runtime)) (hostUid : Nat) : Prop :=
  ∀ (position : Nat) (tick : ActorTick runtime), ticks[position]? = some tick → ∀ before after
    (call : NativeCallAt native tick before after) object information later,
    Nonempty (BoundaryParentLease runtime ticks position tick.before hostUid object) →
    NativeCallAuthorityTarget call object →
    tick.before.shared.information object = some information →
    tick.after.shared.information object = some later → SameAuthority information later

theorem native_boundary_parent_authority {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {native : NativePrimitive kernel} (laws : NativeMetadataContract native)
    {ticks : List (ActorTick runtime)} {hostUid : Nat} (profile : NativeBoundaryAuthorityProfile native ticks hostUid)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick)
    {before after : NativeProcesses} (call : NativeCallAt native tick before after) {object : ObjectId}
    (lease : BoundaryParentLease runtime ticks position tick.before hostUid object)
    (held : GloballyHeld tick.after object) {information : Stat}
    (known : tick.before.shared.information object = some information) :
    ∃ later, tick.after.shared.information object = some later ∧ SameAuthority information later := by
  obtain ⟨later, current, same | target⟩ := laws.existing call object information held known
  · exact ⟨later, current, same⟩
  · exact ⟨later, current, profile position tick selected before after call object information later ⟨lease⟩ target known current⟩

end LeanCage.Host.Kernel
