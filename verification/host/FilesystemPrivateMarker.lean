import FilesystemNativeMarkerLifetime
import FilesystemRegisteredCustody

namespace LeanCage.Host.Kernel
open Filesystem

private theorem attribute_target_fd {references : NativeReferences} {operation : NativeOperation}
    {object : ObjectId} {name : ByteArray} (target : NativeAttributeTarget references operation object name) :
    ∃ fd, NativeFdObject references fd object := by
  cases target with
  | set target | remove target | adapted setting target => exact ⟨_, target⟩

private theorem attribute_target_held {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {native : NativePrimitive kernel} {before after : NativeProcesses} {tick : ActorTick runtime}
    (call : NativeCallAt native tick before after) {object : ObjectId} {name : ByteArray}
    (target : NativeAttributeTarget call.beforeReferences call.operation object name) : NativeHeld before object := by
  obtain ⟨fd, handle, live, identity⟩ := attribute_target_fd target
  exact .inl ⟨call.token, call.beforeReferences, call.inputTable, .inl ⟨fd, handle, live, identity⟩⟩

private theorem foreign_operation {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {caller : Credentials} {before after : Population}
    (actual : ActorStep runtime (.foreign caller) before after) : runtime.foreign caller before.shared after.shared := by
  cases actual
  assumption

-- §FS-host-boundary.publication: The current constructed custody state and actual
-- kernel row preserve this live root marker. Native denial uses its real operand;
-- public namespace/content interference remains unrestricted.
theorem registered_private_marker_step {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    (objects : ObjectLifetimeContract runtime) (attributes : ExistingAttributeContract runtime child)
    (foreign : ForeignContract runtime) (nativeAttributes : NativeExistingAttributeContract native)
    {initial : World} {all processed : List (ActorTick runtime)} {foreignReferences : ForeignReferences}
    {before after : Processes} {callers next : NativeProcesses} {tick : ActorTick runtime}
    (state : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before callers)
    (source : NativeExternalStep process child native hostUid before callers tick after next)
    (safe : NativeAuthoritySafe source) {object : ObjectId} {value : ByteArray}
    (label : state.current.source.custody.caps.family object = some object)
    (alive : ObjectAlive tick.after.shared object)
    (marked : tick.before.shared.attributes object Publication.attributeName = some value) :
    tick.after.shared.attributes object Publication.attributeName = some value := by
  have old := state.current.source.custody.namespaceState.graph.live object object label
  cases source with
  | application recorded notForeign notLaunch notRetiring =>
    exact application_existing_attribute_for attributes tick notForeign safe (.inr rfl) old alive marked
  | launch recorded handoff =>
    exact application_existing_attribute_for attributes tick
      (by intro caller impossible; rw [handoff.action] at impossible; cases impossible)
      (by simp only [handoff.action, AuthoritySafeAction]) (.inr rfl) old alive marked
  | ordinary caller recorded action allowed =>
    obtain ⟨information, known⟩ := actor_step_live_backward_for objects tick.operation old alive
    have directory := state.current.source.custody.namespaceState.scopes object object label
    obtain ⟨owner, mask⟩ := state.current.source.custody.namespaceState.privateDirectories object object information
      label known directory
    have noWrite : information.mode &&& 18 = 0 := by
      simpa only [Nat.zero_and] using masked_bits information.mode 63 18 0 (by decide) mask
    exact foreign_cannot_clear_private_attribute_for foreign caller (foreign_operation (action ▸ tick.operation))
      allowed.2.2.1 (by rw [owner]; exact allowed.1) noWrite known marked alive
  | child recorded call => exact attributes.child call object Publication.attributeName value safe (.inr rfl) old alive marked
  | native recorded call retirementFrame otherReferences =>
    rcases nativeAttributes.existing call object Publication.attributeName value (.inr rfl) old alive marked with kept | target
    · exact kept
    · have publicObject := state.current.nativePublic object (attribute_target_held call target)
      rw [label] at publicObject
      cases publicObject
  | retiring recorded exit =>
    exact application_existing_attribute_for attributes tick
      (by intro caller impossible; rw [exit.action] at impossible; cases impossible)
      (by simp only [exit.action, AuthoritySafeAction]) (.inr rfl) old alive marked

end LeanCage.Host.Kernel
