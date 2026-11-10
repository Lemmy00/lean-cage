import FilesystemInitialAnchors
import FilesystemNativeAuthority
import FilesystemLookupAuthority

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.ownership: This is the application argument obligation for a single
-- destructive syscall; it supplies neither an operation result nor a private-region frame.
def AnchorOperandSafe {initial : World} (anchor : TemporaryAnchor initial)
    (world : World) (request : Request) : Prop :=
  request.op = .unlinkAt ∨ request.op = .renameNew →
    ¬ NamesEntry world request.first request.left anchor.root "tmp".toUTF8

theorem anchor_operand_nondestructive {initial : World} {anchor : TemporaryAnchor initial}
    {world : World} {request : Request} (unlink : request.op ≠ .unlinkAt)
    (rename : request.op ≠ .renameNew) : AnchorOperandSafe anchor world request := by
  rintro (removing | moving)
  · exact False.elim (unlink removing)
  · exact False.elim (rename moving)

theorem anchor_operand_other_name {initial : World} {anchor : TemporaryAnchor initial}
    {world : World} {request : Request} (different : request.left ≠ "tmp".toUTF8) :
    AnchorOperandSafe anchor world request := by
  intro destructive touched
  exact different touched.choose_spec.2.2

theorem anchor_operand_reserved {initial : World} {anchor : TemporaryAnchor initial}
    {world : World} {request : Request} (reserved : PrivateNames.reservedBytes request.left = true) :
    AnchorOperandSafe anchor world request := by
  apply anchor_operand_other_name
  intro same
  have ordinary : PrivateNames.reservedBytes "tmp".toUTF8 = false := by decide
  rw [same, ordinary] at reserved
  cases reserved

theorem anchor_operand_private_parent {initial : World} {anchor : TemporaryAnchor initial}
    {world : World} {request : Request} {family : Family} {dataObjects : ObjectId → Prop}
    (graph : FamilyGraph world family initial.allocated dataObjects) {parent : Handle} {scope : ObjectId}
    (reference : world.handles request.first = some parent) (privateParent : family parent.object = some scope) :
    AnchorOperandSafe anchor world request := by
  intro destructive touched
  obtain ⟨other, otherReference, sameRoot, sameName⟩ := touched
  have same : other = parent := Option.some.inj (otherReference.symm.trans reference)
  subst other
  have publicRoot := family_initial_public graph anchor.root anchor.rootInitial
  rw [sameRoot, publicRoot] at privateParent
  cases privateParent

def ChildAnchorOperandSafe {initial : World} (anchor : TemporaryAnchor initial)
    (references : ChildReferences) (world : World) : ChildOperation → Prop
  | .adapted request => AnchorOperandSafe anchor (references.project world) request
  | .unixSocket _ | .bindUnix _ _ => True

-- §AR-host-boundary.primitives: Only this initialized system binding is observed here. Its
-- comparison premise is current; all other public namespace mutations remain unconstrained.
structure AnchorOperationContract {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram)
    (child : ChildPrimitive kernel) (semantics : NameSemanticsView) {initial : World}
    (anchor : TemporaryAnchor initial) : Prop where
  filesystem : ∀ before after request observed,
    kernel.step before request observed after → anchor.At before →
    (semantics.at before anchor.root).byteExact → AnchorOperandSafe anchor before request →
    anchor.At after
  sdk : ∀ {β : Type} actor (effect : Effect β) observed before after,
    runtime.other actor effect observed before after → anchor.At before → anchor.At after
  retirement : ∀ {before after : Population} {action : ActorAction},
    ActorStep runtime action before after → actionFamily action = .retirement →
    anchor.At before.shared → anchor.At after.shared
  child : ∀ {before after : Processes} {tick : ActorTick runtime}
    (call : ChildCallAt child tick before after), anchor.At tick.before.shared →
    (semantics.at tick.before.shared anchor.root).byteExact →
    ChildAnchorOperandSafe anchor call.beforeReferences tick.before.shared call.operation →
    anchor.At tick.after.shared
  ordinary : ∀ {before after : Population} {caller : Credentials} object,
    ActorStep runtime (.foreign caller) before after →
    before.shared.entries anchor.root "tmp".toUTF8 = some object →
    after.shared.entries anchor.root "tmp".toUTF8 ≠ some object →
    ∃ parentInformation childInformation,
      before.shared.information anchor.root = some parentInformation ∧
      before.shared.information object = some childInformation ∧
      CanRemove caller parentInformation childInformation

-- §FS-host-boundary.ownership: The state contains only initial system-anchor observations.
-- It does not identify any run, authorize a child path or assert a private-family invariant.
structure SystemAnchorState {initial : World} (anchor : TemporaryAnchor initial)
    (semantics : NameSemanticsView) (world : World) : Type where
  bound : anchor.At world
  rootLive : world.allocated anchor.root = true
  information : Stat
  known : world.information anchor.root = some information
  owner : information.uid = 0
  permissions : information.mode &&& 18 = 0
  names : (semantics.at world anchor.root).byteExact

-- §FS-host-boundary.ownership: Different-UID DAC is a genuine per-operation derivation,
-- including when the verified host itself runs as UID0.
theorem ordinary_anchor_preserved {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {child : ChildPrimitive kernel} {semantics : NameSemanticsView} {initial : World}
    {anchor : TemporaryAnchor initial} (laws : AnchorOperationContract runtime child semantics anchor)
    {before after : Population} {caller : Credentials} {hostUid : Nat}
    (actual : ActorStep runtime (.foreign caller) before after) (ordinary : OrdinaryForeign caller hostUid)
    (state : SystemAnchorState anchor semantics before.shared) : anchor.At after.shared := by
  apply Classical.byContradiction
  intro changed
  obtain ⟨parentInformation, childInformation, parentKnown, childKnown, permission⟩ :=
    laws.ordinary anchor.entry actual state.bound changed
  have same := Option.some.inj (parentKnown.symm.trans state.known)
  subst parentInformation
  have group := masked_bits state.information.mode 18 16 0 (by decide) state.permissions
  have other := masked_bits state.information.mode 18 2 0 (by decide) state.permissions
  have groupZero : state.information.mode &&& 16 = 0 := by simpa using group
  have otherZero : state.information.mode &&& 2 = 0 := by simpa using other
  have foreignOwner : caller.uid ≠ state.information.uid := by simpa only [state.owner] using ordinary.2.1
  have denied : ¬ CanWrite caller state.information := by
    simp [CanWrite, ordinary.2.2.1, foreignOwner, groupZero, otherZero]
  exact denied permission.1

-- §FS-host-boundary.ownership: These are the explicit operator/host-code exclusions at a
-- fixed system anchor, one real native operation at a time. No new private object occurs here.
structure NativeAnchorProfile {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (native : NativePrimitive kernel) {initial : World} (anchor : TemporaryAnchor initial)
    (semantics : NameSemanticsView) (ticks : List (ActorTick runtime)) : Prop where
  binding : ∀ (position : Nat) (tick : ActorTick runtime), ticks[position]? = some tick → ∀ before after
    (_call : NativeCallAt native tick before after), anchor.At tick.before.shared → anchor.At tick.after.shared
  authority : ∀ (position : Nat) (tick : ActorTick runtime), ticks[position]? = some tick → ∀ before after
    (call : NativeCallAt native tick before after) information later,
    SystemAnchorState anchor semantics tick.before.shared →
    tick.before.shared.information anchor.root = some information →
    tick.after.shared.information anchor.root = some later →
    NativeCallAuthorityTarget call anchor.root →
    SameAuthority information later
  lookup : ∀ (position : Nat) (tick : ActorTick runtime), ticks[position]? = some tick → ∀ before after
    (call : NativeCallAt native tick before after), SystemAnchorState anchor semantics tick.before.shared →
    NativeLookupTarget call.beforeReferences call.operation anchor.root →
    LookupBitsEqual tick.before.shared tick.after.shared anchor.root

end LeanCage.Host.Kernel
