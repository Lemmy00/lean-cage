import FilesystemNamespaceState

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: Stored positive bindings refer to real live inode metadata.
def LiveNamespace (world : World) : Prop :=
  ∀ parent name child, world.entries parent name = some child →
    ObjectAlive world parent ∧ ObjectAlive world child

-- §AR-host-boundary.primitives: These are heap-coherence laws for individual actual operations.
-- They preserve neither names nor contents and permit removal, inode retirement and loss.
structure NamespaceMetadataContract {kernel : Contract} (runtime : ActorRuntime kernel) : Prop where
  filesystem : ∀ before after request observed,
    kernel.step before request observed after → LiveNamespace after
  sdk : ∀ {β : Type} actor (effect : Effect β) observed before after,
    runtime.other actor effect observed before after → LiveNamespace after
  ordinary : ∀ caller before after, runtime.foreign caller before after → LiveNamespace after
  retirement : ∀ {before after : Population} {action : ActorAction},
    ActorStep runtime action before after → actionFamily action = .retirement → LiveNamespace after.shared

theorem actor_operation_live_namespace {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : NamespaceMetadataContract runtime)
    {β : Type} {actor : ActorId} {effect : Effect β} {observed : Option β} {before after : World}
    (actual : ActorOperation runtime actor effect observed before after) : LiveNamespace after := by
  cases effect with
  | filesystem request => exact laws.filesystem _ _ _ _ actual
  | spawn arguments => exact laws.sdk _ _ _ _ _ actual
  | read stream amount => exact laws.sdk _ _ _ _ _ actual
  | wait child => exact laws.sdk _ _ _ _ _ actual
  | terminate child => exact laws.sdk _ _ _ _ _ actual
  | tryWait child => exact laws.sdk _ _ _ _ _ actual
  | descriptor stream => exact laws.sdk _ _ _ _ _ actual

theorem actor_step_live_namespace {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : NamespaceMetadataContract runtime)
    {action : ActorAction} {before after : Population} (actual : ActorStep runtime action before after)
    (initial : LiveNamespace before.shared) : LiveNamespace after.shared := by
  cases actual with
  | launch => exact initial
  | returned present alive head operation => exact actor_operation_live_namespace laws operation
  | lost present alive head operation => exact actor_operation_live_namespace laws operation
  | foreign operation => exact laws.ordinary _ _ _ operation
  | retire present operation => exact laws.retirement (.retire present operation) rfl
  | nativeRetire operation => exact laws.retirement (.nativeRetire operation) rfl

-- §FS-host-boundary.ownership: Retained actual root bindings supply both parent/child liveness.
theorem external_retained_root_authorities {kernel : Contract} {runtime : ActorRuntime kernel}
    {process : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    (metadata : LiveMetadataContract runtime primitive) {prior next : Processes} {tick : ActorTick runtime}
    (source : ExternalStep process primitive hostUid prior tick next) (safe : ExternalAuthoritySafe source)
    {caps : Capabilities} (authorities : RootAuthorities caps tick.before.shared hostUid)
    (live : LiveNamespace tick.after.shared) : RootAuthorities (caps.retain tick.after.shared) tick.after.shared hostUid := by
  intro root kept
  have member := List.mem_filter.mp kept
  have bound : tick.after.shared.entries root.parent root.name = some root.object := by simpa using member.2
  obtain ⟨childInfo, parentInfo, childKnown, parentKnown, owner, mode, directory, trusted⟩ :=
    authorities root member.1
  have parentOwners : parentInfo.uid = hostUid ∨ parentInfo.uid = 0 := by
    have fields : parentInfo.directory = true ∧ (parentInfo.uid = hostUid ∨ parentInfo.uid = 0) ∧
        (parentInfo.mode &&& 18 = 0 ∨ (parentInfo.uid = 0 ∧ parentInfo.mode &&& 512 ≠ 0)) := by
      simpa [Directories.trusted, and_assoc] using trusted
    exact fields.2.1
  obtain ⟨laterChild, laterChildKnown, childSame⟩ := external_step_live_authority metadata source safe childKnown
    (.inl owner) (live _ _ _ bound).2
  obtain ⟨laterParent, laterParentKnown, parentSame⟩ := external_step_live_authority metadata source safe parentKnown
    parentOwners (live _ _ _ bound).1
  exact ⟨laterChild, laterParent, laterChildKnown, laterParentKnown, childSame.1.trans owner,
    (same_authority_mask childSame 63 (by decide)).trans mode, (same_authority_directory childSame).trans directory,
    (same_authority_trusted hostUid parentSame).trans trusted⟩

end LeanCage.Host.Kernel
