import GatewayChannelPair

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

def AliasesCloseExec (object : ObjectId) (references : NativeReferences) : Prop :=
  ∀ fd handle, references.handles fd = some handle → handle.object = object →
    references.closeOnExec fd = true

-- §FS-host-boundary.ownership: Every pre-birth alias is excluded by the actual
-- allocated-lifetime map and current live-reference receipt, not by a UID role.
theorem fresh_native_reference_absent {processes : NativeProcesses} {world : World}
    (live : NativeReferencesLive processes world) {object : ObjectId}
    (fresh : world.allocated object = false) {token : NativeToken} {references : NativeReferences}
    (present : processes.references token = some references) {fd : UInt64} {handle : Handle}
    (input : references.handles fd = some handle) : handle.object ≠ object := by
  intro same
  have allocated := live object (.inl ⟨token, references, present, .inl ⟨fd, handle, input, same⟩⟩)
  rw [fresh] at allocated
  cases allocated

-- §FS-host-boundary.ownership: The first alias invariant is produced by one
-- actual socketpair. Its two real copyout endpoints start close-on-exec.
theorem pair_caller_aliases_close_exec {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {native : NativePrimitive kernel} {tick : ActorTick runtime} {before after : NativeProcesses}
    {ipc : ObjectId → Prop} {call : NativeCallAt native tick before after} {first second : UInt64}
    (allocation : PairAllocation ipc call first second)
    (live : NativeReferencesLive before tick.before.shared) :
    AliasesCloseExec allocation.left.object call.afterReferences := by
  intro fd handle found same
  by_cases left : fd = first
  · subst fd
    exact allocation.leftCloseExec
  · by_cases right : fd = second
    · subst fd
      have identity := Option.some.inj (allocation.rightOutput.symm.trans found)
      subst handle
      exact False.elim (allocation.objectsSeparate same.symm)
    · have original := (allocation.otherOutputs fd left right).symm.trans found
      exact False.elim (fresh_native_reference_absent live allocation.leftFresh call.inputTable original same)

-- §AR-host-boundary.primitives: These are individual raw descriptor edits.
-- They allow clearing CLOEXEC; the actual source/callback authority must rule
-- out that edit on a protected endpoint rather than erase the transition.
inductive DescriptorEdit : NativeReferences → NativeReferences → Type where
  | retained {before after : NativeReferences}
      (handles : after.handles = before.handles) (flags : after.closeOnExec = before.closeOnExec) :
      DescriptorEdit before after
  | close {before after : NativeReferences} (fd : UInt64)
      (closed : after.handles fd = none)
      (other : ∀ query, query ≠ fd → after.handles query = before.handles query)
      (flags : ∀ query, query ≠ fd → after.closeOnExec query = before.closeOnExec query) :
      DescriptorEdit before after
  | inserted {before after : NativeReferences} (fd : UInt64) (handle : Handle) (closeExec : Bool)
      (output : after.handles fd = some handle) (flag : after.closeOnExec fd = closeExec)
      (other : ∀ query, query ≠ fd → after.handles query = before.handles query)
      (flags : ∀ query, query ≠ fd → after.closeOnExec query = before.closeOnExec query) :
      DescriptorEdit before after
  | changedFlag {before after : NativeReferences} (fd : UInt64) (closeExec : Bool)
      (handles : after.handles = before.handles) (flag : after.closeOnExec fd = closeExec)
      (flags : ∀ query, query ≠ fd → after.closeOnExec query = before.closeOnExec query) :
      DescriptorEdit before after

def DescriptorEdit.allowed {before after : NativeReferences} (object : ObjectId)
    (edit : DescriptorEdit before after) : Prop :=
  match edit with
  | .retained .. | .close .. => True
  | .inserted _ handle closeExec .. => handle.object = object → closeExec = true
  | .changedFlag fd closeExec .. =>
      ∀ handle, before.handles fd = some handle → handle.object = object → closeExec = true

theorem DescriptorEdit.close_exec {before after : NativeReferences} {object : ObjectId}
    (edit : DescriptorEdit before after) (allowed : edit.allowed object)
    (initial : AliasesCloseExec object before) : AliasesCloseExec object after := by
  intro fd handle found same
  cases edit with
  | retained handles flags => rw [flags]; exact initial fd handle (handles ▸ found) same
  | close closedFd closed other flags =>
    by_cases selected : fd = closedFd
    · subst fd
      rw [closed] at found
      cases found
    · rw [flags fd selected]
      exact initial fd handle ((other fd selected).symm.trans found) same
  | inserted target inserted closeExec output flag other flags =>
    by_cases selected : fd = target
    · subst fd
      have identity := Option.some.inj (output.symm.trans found)
      subst handle
      exact flag.trans (allowed same)
    · rw [flags fd selected]
      exact initial fd handle ((other fd selected).symm.trans found) same
  | changedFlag target closeExec handles flag flags =>
    by_cases selected : fd = target
    · subst fd
      exact flag.trans (allowed handle (handles ▸ found) same)
    · rw [flags fd selected]
      exact initial fd handle (handles ▸ found) same

end LeanCage.Host.PrivateStreams
