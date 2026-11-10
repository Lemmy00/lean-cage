import FilesystemPrefixes
import FilesystemDescriptors

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: These are individual Linux DAC and sticky-directory checks.
structure Credentials where
  -- §AR-host-boundary.primitives: Use the actual filesystem UID at this operation's VFS check.
  uid : Nat
  groups : List Nat
  bypassDac : Bool
  bypassOwner : Bool

-- §AR-host-boundary.primitives: Group-class bits upper-bound named ACL rights for any other user.
def CanSearch (caller : Credentials) (directory : Stat) : Prop :=
  caller.bypassDac = true ∨
    (caller.uid = directory.uid ∧ directory.mode &&& 64 ≠ 0) ∨
    (caller.uid ≠ directory.uid ∧ (directory.mode &&& 8 ≠ 0 ∨ directory.mode &&& 1 ≠ 0))

def CanWrite (caller : Credentials) (directory : Stat) : Prop :=
  caller.bypassDac = true ∨
    (caller.uid = directory.uid ∧ directory.mode &&& 128 ≠ 0) ∨
    (caller.uid ≠ directory.uid ∧ (directory.mode &&& 16 ≠ 0 ∨ directory.mode &&& 2 ≠ 0))

def CanRemove (caller : Credentials) (parent child : Stat) : Prop :=
  CanWrite caller parent ∧ CanSearch caller parent ∧
    (parent.mode &&& 512 = 0 ∨ caller.uid = parent.uid ∨ caller.uid = child.uid ∨
      caller.bypassOwner = true)

theorem masked_bits (value mask bit expected : Nat) (inside : mask &&& bit = bit)
    (observed : value &&& mask = expected) : value &&& bit = expected &&& bit := by
  calc
    value &&& bit = (value &&& mask) &&& bit := by rw [Nat.and_assoc, inside]
    _ = expected &&& bit := by rw [observed]

-- §FS-host-boundary.ownership: Private mode excludes group/other traversal, including ACL masks.
theorem private_no_search (caller : Credentials) (directory : Stat)
    (foreign : caller.uid ≠ directory.uid) (ordinary : caller.bypassDac = false)
    (mode : directory.mode &&& 511 = 448) : ¬ CanSearch caller directory := by
  have group := masked_bits directory.mode 511 8 448 (by decide) mode
  have other := masked_bits directory.mode 511 1 448 (by decide) mode
  have groupZero : directory.mode &&& 8 = 0 := by simpa using group
  have otherZero : directory.mode &&& 1 = 0 := by simpa using other
  simp [CanSearch, ordinary, foreign, groupZero, otherZero]

theorem private_no_write (caller : Credentials) (directory : Stat)
    (foreign : caller.uid ≠ directory.uid) (ordinary : caller.bypassDac = false)
    (mode : directory.mode &&& 511 = 448) : ¬ CanWrite caller directory := by
  have group := masked_bits directory.mode 511 16 448 (by decide) mode
  have other := masked_bits directory.mode 511 2 448 (by decide) mode
  have groupZero : directory.mode &&& 16 = 0 := by simpa using group
  have otherZero : directory.mode &&& 2 = 0 := by simpa using other
  simp [CanWrite, ordinary, foreign, groupZero, otherZero]

theorem trusted_parent_no_remove (caller : Credentials) (hostUid : Nat) (parent child : Stat)
    (foreign : caller.uid ≠ hostUid) (nonroot : caller.uid ≠ 0)
    (ordinary : caller.bypassDac = false) (owner : caller.bypassOwner = false)
    (trusted : Directories.trusted hostUid parent = true) (childOwner : child.uid = hostUid) :
    ¬ CanRemove caller parent child := by
  have facts : parent.directory = true ∧ (parent.uid = hostUid ∨ parent.uid = 0) ∧
      (parent.mode &&& 18 = 0 ∨ (parent.uid = 0 ∧ parent.mode &&& 512 ≠ 0)) := by
    simpa [Directories.trusted, and_assoc] using trusted
  have parentForeign : caller.uid ≠ parent.uid := by
    rcases facts.2.1 with host | root
    · simpa only [host] using foreign
    · simpa only [root] using nonroot
  rcases facts.2.2 with restricted | sticky
  · have group := masked_bits parent.mode 18 16 0 (by decide) restricted
    have other := masked_bits parent.mode 18 2 0 (by decide) restricted
    have groupZero : parent.mode &&& 16 = 0 := by simpa using group
    have otherZero : parent.mode &&& 2 = 0 := by simpa using other
    have cannotWrite : ¬ CanWrite caller parent := by
      simp [CanWrite, ordinary, parentForeign, groupZero, otherZero]
    exact fun allowed => cannotWrite allowed.1
  · simp [CanRemove, sticky.2, parentForeign, childOwner, foreign, owner]

-- §FS-host-boundary.ownership: Apply the permission result to the real newChild producer.
theorem actual_new_child_private (uid : Nat) (parent : UInt64) (prefixName : String)
    {events : List (Request × Reply)} {child : Directories.NewDirectory}
    (run : Returns (Directories.newChild uid parent prefixName) events (.ok child))
    (caller : Credentials) (foreign : caller.uid ≠ uid) (ordinary : caller.bypassDac = false) :
    ¬ CanSearch caller child.directory.information ∧ ¬ CanWrite caller child.directory.information := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, actualUid, mode⟩ :=
    Publication.newChild_source uid parent prefixName run
  have foreign : caller.uid ≠ child.directory.information.uid := by rw [actualUid]; exact foreign
  exact ⟨private_no_search caller _ foreign ordinary mode,
    private_no_write caller _ foreign ordinary mode⟩

end LeanCage.Host.Kernel
