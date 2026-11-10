import FilesystemLiveMetadata

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: One create-only user-xattr operation cannot replace an old tag.
-- The liveness condition preserves actual retirement, and no pathname/byte-region frame is used.
structure ExistingAttributeContract {kernel : Contract} {sourceProgram : Program UInt32}
    (runtime : ActorRuntime kernel sourceProgram)
    (primitive : ChildPrimitive kernel) : Prop where
  filesystem : ∀ before after request observed object name value,
    kernel.step before request observed after → AuthoritySafeRequest request → TrackedAttribute name →
    before.allocated object = true → ObjectAlive after object →
    before.attributes object name = some value → after.attributes object name = some value
  sdk : ∀ {β : Type} actor (effect : Effect β) observed before after object name value,
    runtime.other actor effect observed before after → TrackedAttribute name →
    before.allocated object = true → ObjectAlive after object →
    before.attributes object name = some value → after.attributes object name = some value
  retirement : ∀ {before after : Population} {action : ActorAction} object name value,
    ActorStep runtime action before after → actionFamily action = .retirement → TrackedAttribute name →
    before.shared.allocated object = true → ObjectAlive after.shared object →
    before.shared.attributes object name = some value → after.shared.attributes object name = some value
  child : ∀ {before after : Processes} {tick : ActorTick runtime}
    (call : ChildCallAt primitive tick before after) object name value,
    ChildAuthoritySafe call.operation → TrackedAttribute name →
    tick.before.shared.allocated object = true → ObjectAlive tick.after.shared object →
    tick.before.shared.attributes object name = some value → tick.after.shared.attributes object name = some value

def ProtectedMarker (world : World) (hostUid : Nat) (object : ObjectId) (value : ByteArray) : Prop :=
  ∃ information, world.information object = some information ∧ information.uid = hostUid ∧
    information.mode &&& 18 = 0 ∧ world.attributes object PrivateNames.attributeName = some value

private theorem operation_existing_attribute {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram}
    {primitive : ChildPrimitive kernel} (laws : ExistingAttributeContract runtime primitive)
    {β : Type} {actor : ActorId} {effect : Effect β} {observed : Option β} {before after : World}
    {object : ObjectId} {name value : ByteArray} (actual : ActorOperation runtime actor effect observed before after)
    (safe : AuthoritySafeEffect effect) (tracked : TrackedAttribute name) (old : before.allocated object = true)
    (alive : ObjectAlive after object) (marked : before.attributes object name = some value) :
    after.attributes object name = some value := by
  cases effect with
  | filesystem request => exact laws.filesystem _ _ _ _ _ _ _ actual safe tracked old alive marked
  | spawn arguments => exact laws.sdk _ _ _ _ _ _ _ _ actual tracked old alive marked
  | read stream amount => exact laws.sdk _ _ _ _ _ _ _ _ actual tracked old alive marked
  | wait child => exact laws.sdk _ _ _ _ _ _ _ _ actual tracked old alive marked
  | terminate child => exact laws.sdk _ _ _ _ _ _ _ _ actual tracked old alive marked
  | tryWait child => exact laws.sdk _ _ _ _ _ _ _ _ actual tracked old alive marked
  | descriptor stream => exact laws.sdk _ _ _ _ _ _ _ _ actual tracked old alive marked

private theorem returned_effect_safe {β : Type} (actor : ActorId) (effect : Effect β) (reply : β)
    (safe : AuthoritySafeAction (.returned actor effect reply)) : AuthoritySafeEffect effect := by
  cases effect <;> exact safe

private theorem lost_effect_safe {β : Type} (actor : ActorId) (effect : Effect β)
    (safe : AuthoritySafeAction (.lost actor effect)) : AuthoritySafeEffect effect := by
  cases effect <;> exact safe

theorem application_existing_attribute_for {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram}
    {primitive : ChildPrimitive kernel} (laws : ExistingAttributeContract runtime primitive)
    (tick : ActorTick runtime) (notForeign : ∀ caller, tick.action ≠ .foreign caller)
    (safe : AuthoritySafeAction tick.action) {object : ObjectId} {name value : ByteArray}
    (tracked : TrackedAttribute name) (old : tick.before.shared.allocated object = true)
    (alive : ObjectAlive tick.after.shared object) (marked : tick.before.shared.attributes object name = some value) :
    tick.after.shared.attributes object name = some value := by
  rcases tick with ⟨action, before, after, actual⟩
  cases actual with
  | launch => exact marked
  | returned present running head operation =>
    have retained := operation_existing_attribute laws operation (returned_effect_safe _ _ _ safe) tracked old alive marked
    exact retained
  | lost present running head operation =>
    have retained := operation_existing_attribute laws operation (lost_effect_safe _ _ safe) tracked old alive marked
    exact retained
  | @foreign before caller world actual => exact False.elim (notForeign caller rfl)
  | retire present operation => exact laws.retirement _ _ _ (.retire present operation) rfl tracked old alive marked
  | nativeRetire operation => exact laws.retirement _ _ _ (.nativeRetire operation) rfl tracked old alive marked

private theorem foreign_shared_step {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram}
    {caller : Credentials} {before after : Population} (actual : ActorStep runtime (.foreign caller) before after) :
    runtime.foreign caller before.shared after.shared := by
  cases actual with
  | foreign operation => exact operation

-- §FS-host-boundary.publication: Only genuine still-live inode tags are retained across this step.
theorem external_step_protected_marker_for {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram}
    {contract : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    (metadata : LiveMetadataContract runtime primitive) (attributes : ExistingAttributeContract runtime primitive)
    (foreign : ForeignContract runtime) {before after : Processes} {tick : ActorTick runtime}
    (source : ExternalStep contract primitive hostUid before tick after) (safe : ExternalAuthoritySafe source)
    {object : ObjectId} {value : ByteArray} (old : tick.before.shared.allocated object = true)
    (alive : ObjectAlive tick.after.shared object)
    (markedState : ProtectedMarker tick.before.shared hostUid object value) :
    ProtectedMarker tick.after.shared hostUid object value := by
  obtain ⟨information, known, owner, mask, marked⟩ := markedState
  obtain ⟨later, laterKnown, same⟩ := external_step_live_authority_for metadata source safe known (.inl owner) alive
  have marker : tick.after.shared.attributes object PrivateNames.attributeName = some value := by
    cases source with
    | application recorded notForeign =>
      exact application_existing_attribute_for attributes tick notForeign safe (.inl rfl) old alive marked
    | ordinary caller recorded action allowed =>
      have actual : ActorStep runtime (.foreign caller) tick.before tick.after := action ▸ tick.operation
      exact foreign_cannot_clear_private_attribute_for foreign caller (foreign_shared_step actual) allowed.2.2.1
        (by rw [owner]; exact allowed.1) mask known marked alive
    | child recorded call => exact attributes.child call _ _ _ safe (.inl rfl) old alive marked
    | native recorded native impossible call => cases impossible
  exact ⟨later, laterKnown, same.1.trans owner,
    (same_authority_mask same 18 (by decide)).trans mask, marker⟩

-- §AR-host-boundary.interfaces: Preserve the original logical-source theorem type.
theorem external_step_protected_marker {kernel : Contract} {runtime : ActorRuntime kernel}
    {contract : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    (metadata : LiveMetadataContract runtime primitive) (attributes : ExistingAttributeContract runtime primitive)
    (foreign : ForeignContract runtime) {before after : Processes} {tick : ActorTick runtime}
    (source : ExternalStep contract primitive hostUid before tick after) (safe : ExternalAuthoritySafe source)
    {object : ObjectId} {value : ByteArray} (old : tick.before.shared.allocated object = true)
    (alive : ObjectAlive tick.after.shared object)
    (markedState : ProtectedMarker tick.before.shared hostUid object value) :
    ProtectedMarker tick.after.shared hostUid object value :=
  external_step_protected_marker_for metadata attributes foreign source safe old alive markedState

-- §FS-host-boundary.ownership: Late observation derives every required earlier live snapshot.
theorem external_journal_protected_marker {kernel : Contract} {runtime : ActorRuntime kernel}
    {contract : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    (lifetimes : LifetimeContract runtime) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime primitive) (attributes : ExistingAttributeContract runtime primitive)
    (foreign : ForeignContract runtime) {initial final : Processes} {before after : Population}
    {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after)
    (recording : ExternalJournal contract primitive hostUid initial ticks final)
    (safe : ExternalAuthorityJournal recording) {object : ObjectId} {value : ByteArray}
    (old : before.shared.allocated object = true) (alive : ObjectAlive after.shared object)
    (markedState : ProtectedMarker before.shared hostUid object value) :
    ProtectedMarker after.shared hostUid object value := by
  induction journal generalizing initial with
  | nil => exact markedState
  | @cons tick ticks after tail ih =>
    cases recording with
    | cons current remaining =>
      have nextOld := actor_step_allocated lifetimes tick.operation object old
      have nextLive := actor_journal_live_backward lifetimes objects tail nextOld alive
      have next := external_step_protected_marker metadata attributes foreign current safe.1 old nextLive markedState
      exact ih remaining safe.2 nextOld alive next

end LeanCage.Host.Kernel
