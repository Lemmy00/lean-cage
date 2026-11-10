import FilesystemPrivateReads

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: This is initialized operator configuration and
-- actual protected file-lifetime data. It identifies no request-created object,
-- successful validation helper or future kernel result.
structure BootstrapCatalogue (initial : World) where
  roots : String → Prop
  files : String → String → ObjectId → Prop
  initialized : ∀ root name object, files root name object → initial.allocated object = true

-- §FS-host-boundary.caller: Explicit selection may differ from the extension's
-- default bundle. Its producer must bind this SAME request field to an authorized
-- operator root; engine-content equality alone does not establish this selection.
structure BootstrapSelection {initial : World} (catalogue : BootstrapCatalogue initial) (request : GatewayWire.Request) where
  root : String
  selected : Validation.rootString (request.field GatewayWire.bundleSlot).bytes = .ok root
  authorized : catalogue.roots root

structure BootstrapReadSource {initial : World} (catalogue : BootstrapCatalogue initial)
    (request : GatewayWire.Request) (operation : Request) where
  selection : BootstrapSelection catalogue request
  name : String
  canonical : Validation.canonicalName name = true
  exactCall : operation = {
    op := .openAt, first := cwd, second := readFlags, left := (selection.root ++ "/" ++ name).toUTF8 }

-- §AR-host-boundary.primitives: This is ONE actual open's resolution under the
-- protected operator bundle namespace/mount binding. It applies equally to error
-- or lost replies with a committed descriptor; it supplies no caller/source role.
structure BootstrapLookupContract (kernel : Contract) {initial : World} (catalogue : BootstrapCatalogue initial)
    {semantics : NameSemanticsView} {dataObjects : ObjectId → Prop}
    (targets : OpenTargetContract kernel semantics initial.allocated dataObjects) : Prop where
  resolved : ∀ before after observed root name object,
    catalogue.roots root → Validation.canonicalName name = true →
    kernel.step before {
      op := .openAt, first := cwd, second := readFlags, left := (root ++ "/" ++ name).toUTF8 } observed after →
    targets.target before {
      op := .openAt, first := cwd, second := readFlags, left := (root ++ "/" ++ name).toUTF8 } observed after object →
    catalogue.files root name object

-- §FS-host-boundary.ownership: The exact initialized selected path gives the new
-- raw reference its authority. Arbitrary packet bundle bytes and arbitrary cwd
-- opens are not classified as public by this source-specific consumer.
theorem bootstrap_read_registered_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (namespaceLaws : PassiveNamespaceContract kernel) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} (targets : OpenTargetContract kernel semantics initial.allocated dataObjects)
    (catalogue : BootstrapCatalogue initial) (resolution : BootstrapLookupContract kernel catalogue targets)
    {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    {position : Nat} (selected : all[position]? = some tick) {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} {input : GatewayWire.Request}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (source : BootstrapReadSource catalogue input request) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative) := by
  have actual := selected_filesystem_step tick action present
  have filesystem := selected_filesystem_action_family action
  have safe := selected_primitive_action_authority journal selected
  have passive : NamespacePassive request := by rw [source.exactCall]; exact .inl rfl
  have requestSafe : AuthoritySafeRequest request := by intro setting; rw [source.exactCall] at setting; cases setting
  have entries := namespaceLaws.operation (tick.before.project engine) tick.after.shared request observed actual passive
  have state := source_unchanged_filesystem_custody accounts objects metadata actual filesystem safe requestSafe
    prior.current.source.custody.namespaceState.project entries
  have names := filesystem_registered_root_names lookup filesystem safe
    prior.current.source.custody.namespaceState.registry prior.current.source.custody.names
  have owned := opened_filesystem_references_owned targets action present (congrArg Request.op source.exactCall)
    prior.current.source.custody.consistent (unchanged_existing_labels _ _ _) (by intro record member; exact member)
    prior.current.source.custody.references (by
      intro object scope target label
      have identified := resolution.resolved (tick.before.project engine) tick.after.shared observed source.selection.root
        source.name object source.selection.authorized source.canonical (source.exactCall ▸ actual) (source.exactCall ▸ target)
      have publicObject := family_initial_public prior.current.source.custody.namespaceState.graph object
        (catalogue.initialized source.selection.root source.name object identified)
      rw [publicObject] at label
      cases label)
  have allocation := fun object => kernel.allocation_monotone (tick.before.project engine)
    tick.after.shared request observed object actual
  let next := prior.current.source.custody.advance descriptors lifetimes references
    (prior.current.source.custody.caps.retain tick.after.shared) prior.current.source.custody.catalogue
    state names (catalogue_retained_covers prior.current.source.custody.coverage)
    (catalogue_advance_valid prior.current.source.custody.valid allocation) owned .same
  have ownership : CustodyOwnershipStep next.catalogue tick prior.current.source.custody.caps.family next.caps.family :=
    nonremoving_ownership_step _ (by intro parent name object bound; rwa [entries]) (by intro object allocated; rfl)
  let nextSource := prior.current.source.advance next (by intro record member; exact member) ownership
  refine ⟨prior.sourceStep sdk lifetimes nextSource ?_ (unchanged_existing_labels _ _ _) rfl ownership ?_⟩
  · intro owner handles closeExec directory impossible
    rw [impossible] at action
    cases action
  · exact no_root_use_of_other_operation action (by rw [source.exactCall]; change Op.openAt ≠ Op.mkdirAt; decide)

end LeanCage.Host.Kernel
