import FilesystemMarkerLifetime
import FilesystemNativeCustody
import FilesystemPrimitiveReads
import FilesystemRecordedAuthority

namespace LeanCage.Host.Kernel
open Filesystem PrivateStreams

variable {sourceProgram : Program UInt32}

-- §AR-host-boundary.primitives: An exception identifies only this actual attribute syscall's
-- FD/object/name. Path metadata setters remain represented by NativeCallAuthorityTarget.
inductive NativeAttributeTarget (references : NativeReferences) : NativeOperation → ObjectId → ByteArray → Prop where
  | set {fd name value flags object} (target : NativeFdObject references fd object) :
      NativeAttributeTarget references (.vfs (.setAttribute fd name value flags)) object name
  | remove {fd name object} (target : NativeFdObject references fd object) :
      NativeAttributeTarget references (.vfs (.removeAttribute fd name)) object name
  | adapted {request object} (setting : request.op = .setAttribute)
      (target : NativeFdObject references request.first object) :
      NativeAttributeTarget references (.vfs (.adapted request)) object request.left

structure NativeExistingAttributeContract {kernel : Contract} (primitive : NativePrimitive kernel) : Prop where
  existing : ∀ {program : Program UInt32} {runtime : ActorRuntime kernel program}
    {before after : NativeProcesses} {tick : ActorTick runtime}
    (call : NativeCallAt primitive tick before after) object name value,
    TrackedAttribute name → tick.before.shared.allocated object = true → ObjectAlive tick.after.shared object →
    tick.before.shared.attributes object name = some value →
    tick.after.shared.attributes object name = some value ∨
      NativeAttributeTarget call.beforeReferences call.operation object name

-- §DA-host-engine.hostcode: Profile 1 excludes actual bootstrap-private acquisition and
-- authority setters by external host code. It does not frame a callback or public filesystem.
structure NativeProtectedKeyProfile {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (primitive : NativePrimitive kernel) (ticks : List (ActorTick runtime)) (keys : ObjectId → Prop) : Prop where
  authority : ∀ (position : Nat) (tick : ActorTick runtime), ticks[position]? = some tick →
    ∀ before after (call : NativeCallAt primitive tick before after) object,
      keys object → ¬ NativeCallAuthorityTarget call object
  attributeTarget : ∀ (position : Nat) (tick : ActorTick runtime), ticks[position]? = some tick →
    ∀ before after (call : NativeCallAt primitive tick before after) object,
      keys object → ¬ NativeAttributeTarget call.beforeReferences call.operation object PrivateNames.attributeName

-- §FS-host-boundary.snapshot: Key-marker preservation uses the real source/kernel operation
-- and permits object retirement. Native changes are handled by their precise actual targets.
theorem native_step_protected_marker {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    (metadata : LiveMetadataContract runtime child) (attributes : ExistingAttributeContract runtime child)
    (foreign : ForeignContract runtime) (nativeMetadata : NativeLiveMetadataContract native)
    (nativeAttributes : NativeExistingAttributeContract native)
    {all : List (ActorTick runtime)} {keys : ObjectId → Prop} (profile : NativeProtectedKeyProfile native all keys)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {before after : Processes} {callers next : NativeProcesses}
    (source : NativeExternalStep process child native hostUid before callers tick after next)
    (safe : NativeAuthoritySafe source) {object : ObjectId} {value : ByteArray}
    (key : keys object) (old : tick.before.shared.allocated object = true)
    (alive : ObjectAlive tick.after.shared object)
    (markedState : ProtectedMarker tick.before.shared hostUid object value) :
    ProtectedMarker tick.after.shared hostUid object value := by
  cases source with
  | application recorded notForeign notLaunch notRetiring =>
    exact external_step_protected_marker_for (hostUid := hostUid) metadata attributes foreign (.application recorded notForeign)
      safe old alive markedState
  | launch recorded handoff =>
    have notForeign : ∀ caller, tick.action ≠ .foreign caller := by
      intro caller impossible
      rw [handoff.action] at impossible
      cases impossible
    exact external_step_protected_marker_for (hostUid := hostUid) metadata attributes foreign (.application recorded notForeign)
      (by change AuthoritySafeAction tick.action; rw [handoff.action]; exact True.intro) old alive markedState
  | ordinary caller recorded action allowed =>
    exact external_step_protected_marker_for (hostUid := hostUid) metadata attributes foreign (.ordinary caller recorded action allowed)
      True.intro old alive markedState
  | child recorded call =>
    exact external_step_protected_marker_for (hostUid := hostUid) metadata attributes foreign (.child recorded call) safe old alive markedState
  | retiring recorded exit =>
    have notForeign : ∀ caller, tick.action ≠ .foreign caller := by
      intro caller impossible
      rw [exit.action] at impossible
      cases impossible
    exact external_step_protected_marker_for (hostUid := hostUid) metadata attributes foreign (.application recorded notForeign)
      (by change AuthoritySafeAction tick.action; rw [exit.action]; exact True.intro) old alive markedState
  | native recorded call retirementFrame otherReferences =>
    obtain ⟨information, known, owner, mode, marked⟩ := markedState
    obtain ⟨later, current, same | target⟩ := nativeMetadata.existing call object information alive known
    · have retained : tick.after.shared.attributes object PrivateNames.attributeName = some value := by
        rcases nativeAttributes.existing call object PrivateNames.attributeName value (.inl rfl) old alive marked
          with kept | target
        · exact kept
        · exact False.elim (profile.attributeTarget position tick selected callers next call object key target)
      exact ⟨later, current, same.1.trans owner, (same_authority_mask same 18 (by decide)).trans mode, retained⟩
    · exact False.elim (profile.authority position tick selected callers next call object key target)

-- §FS-host-boundary.publication: A late live reference derives all earlier live key states
-- in this SAME global native/engine journal, rather than assuming a marker at the read guard.
theorem native_journal_protected_marker {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    (lifetimes : LifetimeContract runtime) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child) (attributes : ExistingAttributeContract runtime child)
    (foreign : ForeignContract runtime) (nativeMetadata : NativeLiveMetadataContract native)
    (nativeAttributes : NativeExistingAttributeContract native)
    {all : List (ActorTick runtime)} {keys : ObjectId → Prop} (profile : NativeProtectedKeyProfile native all keys)
    {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) (included : ∀ tick ∈ ticks, tick ∈ all)
    {first last : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid first callers ticks last next)
    (safe : NativeAuthorityJournal recording) {object : ObjectId} {value : ByteArray}
    (key : keys object) (old : before.shared.allocated object = true) (alive : ObjectAlive after.shared object)
    (markedState : ProtectedMarker before.shared hostUid object value) :
    ProtectedMarker after.shared hostUid object value := by
  induction journal generalizing first callers with
  | nil => exact markedState
  | @cons tick ticks after tail ih =>
    cases recording with
    | cons current remaining =>
      have nextOld := actor_step_allocated lifetimes tick.operation object old
      have nextLive := actor_journal_live_backward_for lifetimes objects tail nextOld alive
      obtain ⟨position, bound, same⟩ := List.mem_iff_getElem.mp (included tick (by simp))
      have selected : all[position]? = some tick := List.getElem?_eq_some_iff.mpr ⟨bound, same⟩
      have nextState := native_step_protected_marker metadata attributes foreign nativeMetadata nativeAttributes
        profile selected current safe.1 key old nextLive markedState
      exact ih (by intro event member; exact included event (by simp [member])) remaining safe.2 nextOld alive nextState

-- §FS-host-boundary.snapshot: The accepted privacy guard selects its actual earlier
-- global position. Initial key protection is propagated to that point one operation at a time.
theorem primitive_guard_excludes_protected_key {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    (lifetimes : LifetimeContract runtime) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child) (attributes : ExistingAttributeContract runtime child)
    (foreign : ForeignContract runtime) (nativeMetadata : NativeLiveMetadataContract native)
    (nativeAttributes : NativeExistingAttributeContract native)
    {initial : World} {final : Population} {all : List (ActorTick runtime)} {keys : ObjectId → Prop}
    (profile : NativeProtectedKeyProfile native all keys)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {first last : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid first callers all last next)
    {backend : NativeAuthorityJournal recording}
    {key : ObjectId} {value : ByteArray} (keyMember : keys key) (old : initial.allocated key = true)
    (initialMarker : ProtectedMarker initial hostUid key value)
    {actor : ActorId} {fd : UInt64} {handle : Handle}
    (guard : PublicGuard kernel (fun ordinal request reply =>
      SourceReturnAt runtime all actor ordinal Reply (.filesystem request) reply) fd handle) :
    handle.object ≠ key := by
  intro sameObject
  obtain ⟨position, tick, engine, nextEngine, selected, action, present, afterPresent,
    count, beforeShape, afterShape⟩ := guard.sampled
  obtain ⟨cut, cutAt⟩ := selectNativeCut_exists recording selected
  have firstJournal : ActorJournal runtime (Population.empty initial) cut.leading tick.before := by
    have arranged := journal
    rw [cut.shape] at arranged
    obtain ⟨middle, leading, remaining⟩ := actor_journal_split cut.leading _ arranged
    cases remaining with
    | cons tail => exact leading
  have subset : ∀ event ∈ cut.leading, event ∈ all := by
    intro event member
    rw [cut.shape]
    exact List.mem_append_left _ member
  have safe := (recorded_authority_at recording backend ⟨tick, cut⟩ cutAt).1
  have alive : ObjectAlive tick.before.shared key := by
    have observed := objects.reference _ _ _ _ _ _ guard.actual guard.live
    simpa only [sameObject, beforeShape, ObjectAlive, Population.project] using observed
  obtain ⟨information, known, owner, mode, marker⟩ := native_journal_protected_marker lifetimes objects metadata
    attributes foreign nativeMetadata nativeAttributes profile firstJournal subset cut.first safe
    keyMember old alive initialMarker
  have absent := guard.absent
  have actualMarker : guard.before.attributes key PrivateNames.attributeName = some value := by
    simpa only [beforeShape, Population.project] using marker
  rw [sameObject, actualMarker] at absent
  cases absent

-- §FS-host-boundary.snapshot: Actual maintained freeze reads preserve their source guard
-- and cannot copy the initialized protected key through direct, hardlink or bind aliases.
theorem primitive_snapshot_key_reference {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (attributes : ExistingAttributeContract runtime child) (foreign : ForeignContract runtime)
    (nativeMetadata : NativeLiveMetadataContract native) (nativeAttributes : NativeExistingAttributeContract native)
    {initial : World} {final : Population} {all : List (ActorTick runtime)} {keys : ObjectId → Prop}
    (profile : NativeProtectedKeyProfile native all keys)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {first last : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid first callers all last next)
    {backend : NativeAuthorityJournal recording}
    {key : ObjectId} {value : ByteArray} (keyMember : keys key) (old : initial.allocated key = true)
    (initialMarker : ProtectedMarker initial hostUid key value)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : all[position]? = some tick)
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (workspace : Option ByteArray) (stdin : Snapshot.Stdin) (limits : Snapshot.Limits)
    {context : List Program.Event} {before : List (Request × Option Reply)}
    (source : Prefix (Snapshot.freeze workspace stdin limits) (before ++ [(request, none)]))
    (sourceTrace : adapter.occurrence.logicalBefore = context ++ before.map Program.filesystemPrefixEvent)
    (reading : request.op = .read) :
    ∃ handle, engine.references request.first = some handle ∧ handle.object ≠ key := by
  obtain ⟨guarded⟩ := primitive_snapshot_guarded_read descriptors journal selected present adapter
    workspace stdin limits source sourceTrace reading
  exact ⟨guarded.handle, guarded.live, primitive_guard_excludes_protected_key (backend := backend) lifetimes objects metadata attributes
    foreign nativeMetadata nativeAttributes profile journal recording keyMember old initialMarker guarded.guard⟩

end LeanCage.Host.Kernel
