import FilesystemNativeOperations
import FilesystemNativeMetadata
import FilesystemFamilies
import FilesystemRemovalJournal

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

def RetirementResources.Held (resources : RetirementResources) (object : ObjectId) : Prop :=
  (∃ fd handle, resources.handles fd = some handle ∧ handle.object = object) ∨ resources.directory = some object

def NativeHeld (processes : NativeProcesses) (object : ObjectId) : Prop :=
  (∃ token references, processes.references token = some references ∧
    ((∃ fd handle, references.handles fd = some handle ∧ handle.object = object) ∨
      references.workingDirectory = object)) ∨
  ∃ token resources, processes.retiring token = some resources ∧ resources.Held object

def NativeReferencesPublic (processes : NativeProcesses) (family : Family) : Prop :=
  ∀ object, NativeHeld processes object → family object = none

def NativeReferencesLive (processes : NativeProcesses) (world : World) : Prop :=
  ∀ object, NativeHeld processes object → world.allocated object = true

-- §AR-host-boundary.primitives: This is the operand/effect record of ONE native operation,
-- with its own full FD/CWD tables, exact operands, optional reply and committed product.
-- Its laws contain no family, caller-role label or whole-callback preservation premise.
structure NativeNamespaceContract {kernel : Contract} (primitive : NativePrimitive kernel) where
  accesses : NativeToken → Credentials → NativeProcesses → World → NativeOperation →
    Option Reply → NativeProduct → NativeProcesses → World → ObjectId → Prop
  path_metadata : ∀ {program : Program UInt32} {runtime : ActorRuntime kernel program}
    {before after : NativeProcesses} {tick : ActorTick runtime} (call : NativeCallAt primitive tick before after) object,
    NativeCallPathTarget call object →
      accesses call.token call.caller before (call.beforeReferences.project tick.before.shared)
        call.operation call.reply call.product after (call.afterReferences.project tick.after.shared) object
  acquired : ∀ {program : Program UInt32} {runtime : ActorRuntime kernel program}
    {before after : NativeProcesses} {tick : ActorTick runtime} (call : NativeCallAt primitive tick before after) object,
    NativeHeld after object → NativeHeld before object ∨ tick.before.shared.allocated object = false ∨
      accesses call.token call.caller before (call.beforeReferences.project tick.before.shared)
        call.operation call.reply call.product after (call.afterReferences.project tick.after.shared) object
  references_live : ∀ {program : Program UInt32} {runtime : ActorRuntime kernel program}
    {before after : NativeProcesses} {tick : ActorTick runtime} (_call : NativeCallAt primitive tick before after),
    NativeReferencesLive after tick.after.shared
  inserted_parent : ∀ {program : Program UInt32} {runtime : ActorRuntime kernel program}
    {before after : NativeProcesses} {tick : ActorTick runtime} (call : NativeCallAt primitive tick before after)
    parent name object, tick.after.shared.entries parent name = some object →
    tick.before.shared.entries parent name ≠ some object →
      accesses call.token call.caller before (call.beforeReferences.project tick.before.shared)
        call.operation call.reply call.product after (call.afterReferences.project tick.after.shared) parent
  inserted_object : ∀ {program : Program UInt32} {runtime : ActorRuntime kernel program}
    {before after : NativeProcesses} {tick : ActorTick runtime} (call : NativeCallAt primitive tick before after)
    parent name object, tick.after.shared.entries parent name = some object →
    tick.before.shared.entries parent name ≠ some object →
    tick.before.shared.allocated object = false ∨ NativeHeld before object ∨
      accesses call.token call.caller before (call.beforeReferences.project tick.before.shared)
        call.operation call.reply call.product after (call.afterReferences.project tick.after.shared) object
  removed_object : ∀ {program : Program UInt32} {runtime : ActorRuntime kernel program}
    {before after : NativeProcesses} {tick : ActorTick runtime} (call : NativeCallAt primitive tick before after)
    parent name object, tick.before.shared.entries parent name = some object →
    tick.after.shared.entries parent name ≠ some object →
      accesses call.token call.caller before (call.beforeReferences.project tick.before.shared)
        call.operation call.reply call.product after (call.afterReferences.project tick.after.shared) object
  inserted_lifetimes : ∀ {program : Program UInt32} {runtime : ActorRuntime kernel program}
    {before after : NativeProcesses} {tick : ActorTick runtime} (_call : NativeCallAt primitive tick before after)
    parent name object, tick.after.shared.entries parent name = some object →
    tick.before.shared.entries parent name ≠ some object →
    tick.before.shared.allocated parent = true ∧ tick.after.shared.allocated object = true

def NativeCallAccess {kernel : Contract} {primitive : NativePrimitive kernel}
    (laws : NativeNamespaceContract primitive) {runtime : ActorRuntime kernel sourceProgram}
    {before after : NativeProcesses} {tick : ActorTick runtime}
    (call : NativeCallAt primitive tick before after) (object : ObjectId) : Prop :=
  laws.accesses call.token call.caller before (call.beforeReferences.project tick.before.shared)
    call.operation call.reply call.product after (call.afterReferences.project tick.after.shared) object

-- §FS-host-boundary.ownership: Profile 1 restricts each external host-code operation's
-- actual resolved operands. Public data/name changes remain; UID equality supplies no denial.
def NativePrivateOperandProfile {kernel : Contract} {primitive : NativePrimitive kernel}
    (laws : NativeNamespaceContract primitive) {runtime : ActorRuntime kernel sourceProgram}
    {before after : NativeProcesses} {tick : ActorTick runtime}
    (call : NativeCallAt primitive tick before after) (family : Family) : Prop :=
  ∀ object, NativeCallAccess laws call object → family object = none

theorem native_references_public {kernel : Contract} {primitive : NativePrimitive kernel}
    (laws : NativeNamespaceContract primitive) {runtime : ActorRuntime kernel sourceProgram}
    {before after : NativeProcesses} {tick : ActorTick runtime} {family : Family}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (call : NativeCallAt primitive tick before after) (profile : NativePrivateOperandProfile laws call family)
    (graph : FamilyGraph tick.before.shared family initialObjects dataObjects)
    (safe : NativeReferencesPublic before family) : NativeReferencesPublic after family := by
  intro object held
  rcases laws.acquired call object held with old | fresh | used
  · exact safe object old
  · cases label : family object with
    | none => rfl
    | some scope => have allocated := graph.live object scope label; rw [fresh] at allocated; cases allocated
  · exact profile object used

theorem native_public_existing_labels {processes : NativeProcesses}
    {before after : World} {first final : Family}
    (live : NativeReferencesLive processes before) (safe : NativeReferencesPublic processes first)
    (labels : ExistingLabels before after first final) : NativeReferencesPublic processes final := by
  intro object held
  rcases labels object (live object held) with same | publicObject
  · exact same.trans (safe object held)
  · exact publicObject

private theorem authority_target_fd {references : NativeReferences} {operation : NativeOperation} {object : ObjectId}
    (target : NativeAuthorityTarget references operation object) : ∃ fd, NativeFdObject references fd object := by
  cases target with
  | chmod actual | chown actual => exact ⟨_, actual⟩
  | aclSet acl actual | aclRemove acl actual => exact ⟨_, actual⟩
  | adaptedAcl setting acl actual => exact ⟨_, actual⟩

theorem native_authority_target_public {kernel : Contract} {primitive : NativePrimitive kernel}
    (laws : NativeNamespaceContract primitive) {runtime : ActorRuntime kernel sourceProgram}
    {before after : NativeProcesses} {tick : ActorTick runtime} {family : Family}
    (call : NativeCallAt primitive tick before after) (profile : NativePrivateOperandProfile laws call family)
    (safe : NativeReferencesPublic before family) {object : ObjectId}
    (target : NativeCallAuthorityTarget call object) : family object = none := by
  have fromFd : ∀ fd, NativeFdObject call.beforeReferences fd object → family object = none := by
    intro fd actual
    obtain ⟨handle, live, identity⟩ := actual
    exact safe object (.inl ⟨call.token, call.beforeReferences, call.inputTable, .inl ⟨fd, handle, live, identity⟩⟩)
  rcases target with descriptor | pathname
  · obtain ⟨fd, actual⟩ := authority_target_fd descriptor
    exact fromFd fd actual
  · exact profile object (laws.path_metadata call object pathname)

theorem native_private_binding_preserved {kernel : Contract} {primitive : NativePrimitive kernel}
    (laws : NativeNamespaceContract primitive) {runtime : ActorRuntime kernel sourceProgram}
    {before after : NativeProcesses} {tick : ActorTick runtime} {family : Family}
    (call : NativeCallAt primitive tick before after) (profile : NativePrivateOperandProfile laws call family)
    {parent object scope : ObjectId} {name : ByteArray}
    (bound : tick.before.shared.entries parent name = some object) (privateObject : family object = some scope) :
    tick.after.shared.entries parent name = some object := by
  by_cases kept : tick.after.shared.entries parent name = some object
  · exact kept
  · have publicObject := profile object (laws.removed_object call parent name object bound kept)
    rw [privateObject] at publicObject
    cases publicObject

theorem native_private_binding_earlier {kernel : Contract} {primitive : NativePrimitive kernel}
    (laws : NativeNamespaceContract primitive) {runtime : ActorRuntime kernel sourceProgram}
    {before after : NativeProcesses} {tick : ActorTick runtime} {family : Family}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (call : NativeCallAt primitive tick before after) (profile : NativePrivateOperandProfile laws call family)
    (graph : FamilyGraph tick.before.shared family initialObjects dataObjects)
    (safe : NativeReferencesPublic before family) {parent object scope : ObjectId} {name : ByteArray}
    (bound : tick.after.shared.entries parent name = some object) (privateObject : family object = some scope) :
    tick.before.shared.entries parent name = some object := by
  by_cases old : tick.before.shared.entries parent name = some object
  · exact old
  · have publicObject : family object = none := by
      rcases laws.inserted_object call parent name object bound old with fresh | held | used
      · have allocated := graph.live object scope privateObject
        rw [fresh] at allocated
        cases allocated
      · exact safe object held
      · exact profile object used
    rw [privateObject] at publicObject
    cases publicObject

-- §FS-host-boundary.ownership: Individual native rows preserve the private graph while
-- allowing arbitrary public insertions/removals, live aliases and FD/CWD acquisitions.
theorem native_namespace_family {kernel : Contract} {primitive : NativePrimitive kernel}
    (laws : NativeNamespaceContract primitive) {runtime : ActorRuntime kernel sourceProgram}
    (lifetimes : LifetimeContract runtime)
    {before after : NativeProcesses} {tick : ActorTick runtime} {family : Family}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (call : NativeCallAt primitive tick before after) (profile : NativePrivateOperandProfile laws call family)
    (graph : FamilyGraph tick.before.shared family initialObjects dataObjects)
    (safe : NativeReferencesPublic before family) :
    FamilyGraph tick.after.shared family initialObjects dataObjects := by
  constructor
  · intro object scope label
    exact actor_step_allocated lifetimes tick.operation object (graph.live object scope label)
  · exact graph.young
  · exact graph.data
  · intro parent name object scope bound label
    exact graph.border _ _ _ _ (native_private_binding_earlier laws call profile graph safe bound label) label
  · intro parent name object scope bound label
    by_cases old : tick.before.shared.entries parent name = some object
    · exact graph.descendants _ _ _ _ old label
    · have publicParent := profile parent (laws.inserted_parent call parent name object bound old)
      rw [label] at publicParent
      cases publicParent

theorem native_namespace_well_formed {kernel : Contract} {primitive : NativePrimitive kernel}
    (laws : NativeNamespaceContract primitive) {runtime : ActorRuntime kernel sourceProgram}
    (lifetimes : LifetimeContract runtime)
    {before after : NativeProcesses} {tick : ActorTick runtime}
    (call : NativeCallAt primitive tick before after) (wellFormed : NamespaceWellFormed tick.before.shared) :
    NamespaceWellFormed tick.after.shared := by
  intro parent name object bound
  by_cases old : tick.before.shared.entries parent name = some object
  · have live := wellFormed parent name object old
    exact ⟨actor_step_allocated lifetimes tick.operation parent live.1,
      actor_step_allocated lifetimes tick.operation object live.2⟩
  · have born := laws.inserted_lifetimes call parent name object bound old
    exact ⟨actor_step_allocated lifetimes tick.operation parent born.1, born.2⟩

theorem native_namespace_ownership_step {kernel : Contract} {primitive : NativePrimitive kernel}
    (laws : NativeNamespaceContract primitive) {runtime : ActorRuntime kernel sourceProgram}
    {before after : NativeProcesses} {tick : ActorTick runtime} {family : Family}
    {all : List (ActorTick runtime)} (catalogue : Catalogue runtime all)
    (call : NativeCallAt primitive tick before after) (profile : NativePrivateOperandProfile laws call family) :
    CustodyOwnershipStep catalogue tick family family := by
  constructor
  · intro parent name object scope bound label missing
    exact False.elim (missing (native_private_binding_preserved laws call profile bound label))
  · intro object scope allocated label released
    exact False.elim (released label)

end LeanCage.Host.Kernel
