import FilesystemNativeEffects
import FilesystemGlobalAuthority

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

def NativeFdObject (references : NativeReferences) (fd : UInt64) (object : ObjectId) : Prop :=
  ∃ handle, references.handles fd = some handle ∧ handle.object = object

def AuthorityAttribute (name : ByteArray) : Prop := name = "system.posix_acl_access".toUTF8

-- §AR-host-boundary.primitives: Exceptions name the actual metadata-changing syscall target.
-- Other public data/name operations do not receive a blanket private-state frame.
inductive NativeAuthorityTarget (references : NativeReferences) : NativeOperation → ObjectId → Prop where
  | chmod {fd mode object} (target : NativeFdObject references fd object) :
      NativeAuthorityTarget references (.vfs (.fchmod fd mode)) object
  | chown {fd owner group object} (target : NativeFdObject references fd object) :
      NativeAuthorityTarget references (.vfs (.fchown fd owner group)) object
  | aclSet {fd name value flags object} (acl : AuthorityAttribute name)
      (target : NativeFdObject references fd object) :
      NativeAuthorityTarget references (.vfs (.setAttribute fd name value flags)) object
  | aclRemove {fd name object} (acl : AuthorityAttribute name)
      (target : NativeFdObject references fd object) :
      NativeAuthorityTarget references (.vfs (.removeAttribute fd name)) object
  | adaptedAcl {request object} (setting : request.op = .setAttribute) (acl : AuthorityAttribute request.left)
      (target : NativeFdObject references request.first object) :
      NativeAuthorityTarget references (.vfs (.adapted request)) object

def NativeCallAuthorityTarget {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {primitive : NativePrimitive kernel} {tick : ActorTick runtime} {before after : NativeProcesses}
    (call : NativeCallAt primitive tick before after) (object : ObjectId) : Prop :=
  NativeAuthorityTarget call.beforeReferences call.operation object ∨ NativeCallPathTarget call object

theorem path_setter_not_fd_target (references : NativeReferences) {operation : NativeOperation} {object : ObjectId}
    (setter : NativePathSetter operation) : ¬ NativeAuthorityTarget references operation object := by
  cases setter <;> intro target <;> cases target

-- §AR-host-boundary.primitives: A path setter can use only its SAME resolved-operation target,
-- rather than granting an exception merely because its directory FD happens to be protected.
theorem NativeCallAuthorityTarget.path_iff {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {primitive : NativePrimitive kernel} {tick : ActorTick runtime} {before after : NativeProcesses}
    {call : NativeCallAt primitive tick before after} {object : ObjectId}
    (setter : NativePathSetter call.operation) :
    NativeCallAuthorityTarget call object ↔ NativeCallPathTarget call object := by
  constructor
  · intro target
    rcases target with descriptor | path
    · exact False.elim (path_setter_not_fd_target call.beforeReferences setter descriptor)
    · exact path
  · exact Or.inr

-- §AR-host-boundary.primitives: This law describes one actual native operation. Genuine inode
-- retirement remains possible; the held-reference premise names a live global reference.
structure NativeMetadataContract {kernel : Contract} (primitive : NativePrimitive kernel) : Prop where
  existing : ∀ {program : Program UInt32} {runtime : ActorRuntime kernel program}
    {tick : ActorTick runtime} {before after : NativeProcesses}
    (call : NativeCallAt primitive tick before after) object information,
    GloballyHeld tick.after object → tick.before.shared.information object = some information →
    ∃ later, tick.after.shared.information object = some later ∧
      (SameAuthority information later ∨ NativeCallAuthorityTarget call object)

-- §FS-host-boundary.ownership: Protection starts with a real prior source fstat and the SAME
-- still-retained engine reference. It does not make every host-owned pathname private.
structure ActiveParentLease {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram)
    (ticks : List (ActorTick runtime)) (population : Population) (hostUid : Nat) (object : ObjectId) where
  actor : ActorId
  engine : EngineState
  descriptor : UInt64
  handle : Handle
  present : population.actors actor = some engine
  live : engine.references descriptor = some handle
  identity : handle.object = object
  ordinal : Nat
  before : World
  after : World
  reply : Reply
  information : Stat
  sampled : SourceReturnAt runtime ticks actor ordinal Reply (.filesystem {op := .stat, first := descriptor}) reply before after
  held : before.handles descriptor = some handle
  parsed : parseStat reply = some information
  trusted : Directories.trusted hostUid information = true
  earlier : ordinal < engine.events.length

-- §FS-host-boundary.ownership: Profile 1 excludes actual UID/mode/ACL reconfiguration of an
-- active checked parent. No-op setters and permitted public name/data operations remain.
def NativeAuthorityProfile {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (primitive : NativePrimitive kernel) (ticks : List (ActorTick runtime)) (hostUid : Nat) : Prop :=
  ∀ (position : Nat) (tick : ActorTick runtime), ticks[position]? = some tick → ∀ before after
    (call : NativeCallAt primitive tick before after) object information later,
    Nonempty (ActiveParentLease runtime ticks tick.before hostUid object) →
    NativeCallAuthorityTarget call object →
    tick.before.shared.information object = some information →
    tick.after.shared.information object = some later → SameAuthority information later

theorem native_active_parent_authority {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {primitive : NativePrimitive kernel} (laws : NativeMetadataContract primitive)
    {ticks : List (ActorTick runtime)} {hostUid : Nat} (profile : NativeAuthorityProfile primitive ticks hostUid)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick)
    {before after : NativeProcesses} (call : NativeCallAt primitive tick before after)
    {object : ObjectId} {information : Stat}
    (lease : ActiveParentLease runtime ticks tick.before hostUid object)
    (held : GloballyHeld tick.after object) (known : tick.before.shared.information object = some information) :
    ∃ later, tick.after.shared.information object = some later ∧ SameAuthority information later := by
  obtain ⟨later, current, same | target⟩ := laws.existing call object information held known
  · exact ⟨later, current, same⟩
  · exact ⟨later, current, profile position tick selected before after call object information later
      ⟨lease⟩ target known current⟩

end LeanCage.Host.Kernel
