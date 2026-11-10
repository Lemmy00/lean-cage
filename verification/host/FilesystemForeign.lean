import FilesystemActors

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: Metadata belongs to a live lifetime, independent of inode reuse.
def ObjectAlive (world : World) (object : ObjectId) : Prop :=
  ∃ information, world.information object = some information

-- §AR-host-boundary.primitives: Removing an existing binding requires the actual Linux checks.
structure ForeignContract {kernel : Contract} {sourceProgram : Program UInt32}
    (runtime : ActorRuntime kernel sourceProgram) : Prop where
  remove_permission : ∀ caller before after parent name object,
    runtime.foreign caller before after → before.entries parent name = some object →
    after.entries parent name ≠ some object →
    ∃ parentInfo childInfo, before.information parent = some parentInfo ∧
      before.information object = some childInfo ∧ CanRemove caller parentInfo childInfo
  attribute_permission : ∀ caller before after object name value,
    runtime.foreign caller before after → ObjectAlive after object →
    before.attributes object name = some value → after.attributes object name ≠ some value →
    ∃ information, before.information object = some information ∧ CanWrite caller information

def OrdinaryForeign (caller : Credentials) (hostUid : Nat) : Prop :=
  caller.uid ≠ hostUid ∧ caller.uid ≠ 0 ∧ caller.bypassDac = false ∧ caller.bypassOwner = false

-- §FS-host-boundary.ownership: Shared-parent mutation remains allowed except where DAC denies it.
theorem foreign_cannot_remove_private_child {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : ForeignContract runtime) (hostUid : Nat) (caller : Credentials)
    {before after : World} {parent child : ObjectId} {name : ByteArray} {parentInfo childInfo : Stat}
    (step : runtime.foreign caller before after) (ordinary : OrdinaryForeign caller hostUid)
    (bound : before.entries parent name = some child)
    (parentActual : before.information parent = some parentInfo)
    (childActual : before.information child = some childInfo)
    (trusted : Directories.trusted hostUid parentInfo = true) (owned : childInfo.uid = hostUid) :
    after.entries parent name = some child := by
  apply Classical.byContradiction
  intro removed
  obtain ⟨parentObserved, childObserved, parentSame, childSame, permission⟩ :=
    laws.remove_permission caller before after parent name child step bound removed
  have sameParent := Option.some.inj (parentActual.symm.trans parentSame)
  have sameChild := Option.some.inj (childActual.symm.trans childSame)
  subst parentObserved
  subst childObserved
  exact trusted_parent_no_remove caller hostUid parentInfo childInfo ordinary.1 ordinary.2.1
    ordinary.2.2.1 ordinary.2.2.2 trusted owned permission

theorem foreign_cannot_mutate_private_directory {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : ForeignContract runtime) (caller : Credentials)
    {before after : World} {parent child : ObjectId} {name : ByteArray} {parentInfo : Stat}
    (step : runtime.foreign caller before after)
    (ordinary : caller.bypassDac = false) (foreign : caller.uid ≠ parentInfo.uid)
    (bound : before.entries parent name = some child)
    (parentActual : before.information parent = some parentInfo)
    (privateMode : parentInfo.mode &&& 511 = 448) : after.entries parent name = some child := by
  apply Classical.byContradiction
  intro removed
  obtain ⟨parentObserved, childObserved, parentSame, childSame, permission⟩ :=
    laws.remove_permission caller before after parent name child step bound removed
  have sameParent := Option.some.inj (parentActual.symm.trans parentSame)
  subst parentObserved
  exact private_no_write caller parentInfo foreign ordinary privateMode permission.1

-- §FS-host-boundary.publication: The secret marker cannot be cleared through foreign DAC rights.
theorem foreign_cannot_clear_private_attribute_for {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram}
    (laws : ForeignContract runtime) (caller : Credentials)
    {before after : World} {object : ObjectId} {name value : ByteArray} {information : Stat}
    (step : runtime.foreign caller before after) (ordinary : caller.bypassDac = false)
    (foreign : caller.uid ≠ information.uid) (noGroupOtherWrite : information.mode &&& 18 = 0)
    (actual : before.information object = some information)
    (marked : before.attributes object name = some value) (alive : ObjectAlive after object) :
    after.attributes object name = some value := by
  apply Classical.byContradiction
  intro changed
  obtain ⟨observed, observedActual, permission⟩ :=
    laws.attribute_permission caller before after object name value step alive marked changed
  have same := Option.some.inj (actual.symm.trans observedActual)
  subst observed
  have group := masked_bits information.mode 18 16 0 (by decide) noGroupOtherWrite
  have other := masked_bits information.mode 18 2 0 (by decide) noGroupOtherWrite
  have groupZero : information.mode &&& 16 = 0 := by simpa using group
  have otherZero : information.mode &&& 2 = 0 := by simpa using other
  simp [CanWrite, ordinary, foreign, groupZero, otherZero] at permission

-- §AR-host-boundary.interfaces: Preserve the original logical-source specialization.
theorem foreign_cannot_clear_private_attribute {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : ForeignContract runtime) (caller : Credentials)
    {before after : World} {object : ObjectId} {name value : ByteArray} {information : Stat}
    (step : runtime.foreign caller before after) (ordinary : caller.bypassDac = false)
    (foreign : caller.uid ≠ information.uid) (noGroupOtherWrite : information.mode &&& 18 = 0)
    (actual : before.information object = some information)
    (marked : before.attributes object name = some value) (alive : ObjectAlive after object) :
    after.attributes object name = some value :=
  foreign_cannot_clear_private_attribute_for laws caller step ordinary foreign noGroupOtherWrite actual marked alive

end LeanCage.Host.Kernel
