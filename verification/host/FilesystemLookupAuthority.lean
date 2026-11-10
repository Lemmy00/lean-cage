import FilesystemNativeAuthority
import FilesystemLookupSemantics

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

def LookupBitsEqual (before after : World) (object : ObjectId) : Prop :=
  after.inodeFlags object &&& (Lookup.casefoldFlag ||| Lookup.encryptionFlag) =
    before.inodeFlags object &&& (Lookup.casefoldFlag ||| Lookup.encryptionFlag)

theorem lookup_bits_trans {first middle last : World} {object : ObjectId}
    (before : LookupBitsEqual first middle object) (after : LookupBitsEqual middle last object) :
    LookupBitsEqual first last object := after.trans before

theorem byte_exact_after_lookup_bits {view : NameSemanticsView} {before after : World} {object : ObjectId}
    (known : (view.at before object).byteExact) (same : LookupBitsEqual before after object) :
    (view.at after object).byteExact := by
  rcases known with temporary | ⟨ext, unflagged⟩
  · exact .inl temporary
  · exact .inr ⟨ext, same.trans unflagged⟩

-- §AR-host-boundary.primitives: These exceptions name actual ioctl/xattr targets. Public input
-- flag changes remain possible; an observation is never interpreted as a directory lock.
inductive NativeLookupTarget (references : NativeReferences) : NativeOperation → ObjectId → Prop where
  | flags {fd value object} (target : NativeFdObject references fd object) :
      NativeLookupTarget references (.vfs (.setInodeFlags fd value)) object
  | encryption {fd policy object} (target : NativeFdObject references fd object) :
      NativeLookupTarget references (.vfs (.setEncryptionPolicy fd policy)) object
  | attribute {fd name value flags object} (target : NativeFdObject references fd object) :
      NativeLookupTarget references (.vfs (.setAttribute fd name value flags)) object
  | removeAttribute {fd name object} (target : NativeFdObject references fd object) :
      NativeLookupTarget references (.vfs (.removeAttribute fd name)) object
  | adaptedAttribute {request object} (setting : request.op = .setAttribute)
      (target : NativeFdObject references request.first object) :
      NativeLookupTarget references (.vfs (.adapted request)) object

-- §AR-host-boundary.primitives: Every rule concerns one actual operation and existing inode.
-- Native callbacks retain their actual target exceptions and foreign UID permission checks.
structure LookupMutationContract {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (child : ChildPrimitive kernel) (native : NativePrimitive kernel) : Prop where
  filesystem : ∀ {before after : Population} {action : ActorAction} object,
    ActorStep runtime action before after → actionFamily action = .filesystem → AuthoritySafeAction action →
    before.shared.allocated object = true → GloballyHeld after object → LookupBitsEqual before.shared after.shared object
  sdk : ∀ {before after : Population} {action : ActorAction} object,
    ActorStep runtime action before after → actionFamily action = .runtime →
    before.shared.allocated object = true → GloballyHeld after object → LookupBitsEqual before.shared after.shared object
  retirement : ∀ {before after : Population} {action : ActorAction} object,
    ActorStep runtime action before after → actionFamily action = .retirement →
    before.shared.allocated object = true → GloballyHeld after object → LookupBitsEqual before.shared after.shared object
  child : ∀ {before after : Processes} {tick : ActorTick runtime}
    (call : ChildCallAt child tick before after) object,
    ChildAuthoritySafe call.operation → tick.before.shared.allocated object = true →
    GloballyHeld tick.after object → LookupBitsEqual tick.before.shared tick.after.shared object
  ordinary : ∀ {before after : Population} {caller : Credentials} object information,
    ActorStep runtime (.foreign caller) before after → before.shared.allocated object = true →
    GloballyHeld after object → before.shared.information object = some information →
    LookupBitsEqual before.shared after.shared object ∨ CanChangeAuthority caller information
  native : ∀ {before after : NativeProcesses} {tick : ActorTick runtime}
    (call : NativeCallAt native tick before after) object,
    tick.before.shared.allocated object = true → GloballyHeld tick.after object →
    LookupBitsEqual tick.before.shared tick.after.shared object ∨
      NativeLookupTarget call.beforeReferences call.operation object

-- §FS-host-boundary.lookup: The initialized profile forbids actual lookup-semantics
-- reconfiguration only while the same checked trusted-parent lease remains active.
def NativeLookupProfile {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (native : NativePrimitive kernel) (ticks : List (ActorTick runtime)) (hostUid : Nat) : Prop :=
  ∀ (position : Nat) (tick : ActorTick runtime), ticks[position]? = some tick → ∀ before after
    (call : NativeCallAt native tick before after) object,
    Nonempty (ActiveParentLease runtime ticks tick.before hostUid object) →
    NativeLookupTarget call.beforeReferences call.operation object →
    LookupBitsEqual tick.before.shared tick.after.shared object

-- §AR-host-boundary.primitives: Pinned ext4 checks emptiness under the inode lock when changing
-- CASEFOLD or installing encryption. This rule preserves a nonempty boundary, not an empty one.
structure NativeNonemptyLookupContract {kernel : Contract} (native : NativePrimitive kernel)
    (view : NameSemanticsView) : Prop where
  existing : ∀ {program : Program UInt32} {runtime : ActorRuntime kernel program}
    {before after : NativeProcesses} {tick : ActorTick runtime}
    (_call : NativeCallAt native tick before after) object name child,
    tick.before.shared.entries object name = some child → view.filesystemType object = Lookup.extMagic →
    LookupBitsEqual tick.before.shared tick.after.shared object

theorem native_step_lookup_bits {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    (laws : LookupMutationContract (runtime := runtime) child native)
    {all : List (ActorTick runtime)} (profile : NativeLookupProfile native all hostUid)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {before after : Processes} {callers next : NativeProcesses}
    (source : NativeExternalStep process child native hostUid before callers tick after next)
    (safe : NativeAuthoritySafe source) {object : ObjectId} {information : Stat}
    (lease : ActiveParentLease runtime all tick.before hostUid object)
    (known : tick.before.shared.information object = some information)
    (owner : information.uid = hostUid ∨ information.uid = 0)
    (old : tick.before.shared.allocated object = true) (held : GloballyHeld tick.after object) :
    LookupBitsEqual tick.before.shared tick.after.shared object := by
  cases source with
  | application recorded notForeign notLaunch =>
    rcases tick with ⟨action, before, after, actual⟩
    cases action with
    | launch actor references closeExec cwd => exact False.elim (notLaunch _ _ _ _ rfl)
    | returned actor effect reply =>
      cases effect with
      | filesystem request => exact laws.filesystem _ actual rfl safe old held
      | spawn | read | wait | terminate | tryWait | descriptor => exact laws.sdk _ actual rfl old held
    | lost actor effect =>
      cases effect with
      | filesystem request => exact laws.filesystem _ actual rfl safe old held
      | spawn | read | wait | terminate | tryWait | descriptor => exact laws.sdk _ actual rfl old held
    | foreign caller => exact False.elim (notForeign caller rfl)
    | retire actor observation | nativeRetire actor observation _ _ =>
      exact laws.retirement _ actual rfl old held
  | launch recorded handoff =>
    have unchanged : ∀ {actor : ActorId} {references : UInt64 → Option Handle}
        {closeExec : UInt64 → Bool} {cwd : ObjectId} {before after : Population},
        ActorStep runtime (.launch actor references closeExec cwd) before after → after.shared = before.shared := by
      intro actor references closeExec cwd before after actual
      cases actual
      rfl
    have actual : ActorStep runtime (.launch handoff.actor handoff.execution.references.rawProjection.handles
        handoff.execution.references.rawProjection.closeOnExec handoff.execution.references.workingDirectory)
        tick.before tick.after := handoff.action ▸ tick.operation
    have same := unchanged actual
    change tick.after.shared.inodeFlags object &&& _ = tick.before.shared.inodeFlags object &&& _
    rw [same]
  | ordinary caller recorded action allowed =>
    have actual : ActorStep runtime (.foreign caller) tick.before tick.after := action ▸ tick.operation
    rcases laws.ordinary object information actual old held known with same | permission
    · exact same
    · rcases permission with owns | bypass
      · rcases owner with host | root
        · exact False.elim (allowed.1 (owns.trans host))
        · exact False.elim (allowed.2.1 (owns.trans root))
      · rw [allowed.2.2.2] at bypass
        cases bypass
  | child recorded call => exact laws.child call object safe old held
  | retiring recorded exit =>
    have actual : ActorStep runtime (.nativeRetire exit.token exit.observation exit.beforeResources exit.afterResources)
        tick.before tick.after := exit.action ▸ tick.operation
    exact laws.retirement _ actual rfl old held
  | native recorded call retirementFrame =>
    rcases laws.native call object old held with same | target
    · exact same
    · exact profile position tick selected callers next call object ⟨lease⟩ target

end LeanCage.Host.Kernel
