import FilesystemRegisteredDescendants
import FilesystemJointCreation

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: Descendant creation contributes its exact
-- nonremoving ownership row to the SAME joint prefix. Fresh object labels
-- do not privatize any old public reference or change a historical owner.
theorem descendant_registered_publication_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (types : CreationTypeContract kernel directories) (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} (targets : OpenTargetContract kernel semantics initial.allocated dataObjects)
    (dataLookup : DynamicDataLookupContract kernel semantics initial.allocated dataObjects)
    (cwdLookup : WorkingDirectoryContract kernel initial.allocated dataObjects)
    {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    (anchor : TemporaryAnchor initial) (anchorLookup : TemporaryLookupContract kernel anchor)
    (anchors : SystemAnchorJournal runtime anchor semantics (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} {parent : Handle} {scope : ObjectId}
    (selected : all[position]? = some tick) {trailing : List (ActorTick runtime)}
    (whole : all = processed ++ tick :: trailing) (count : processed.length = position)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (operation : request.op = .mkdirAt ∨ (request.op = .openAt ∧ request.second = newFileFlags))
    (mode : request.op = .mkdirAt → request.second = 448) (component : Directories.component request.left = true)
    (parentLive : engine.references request.first = some parent)
    (comparison : (semantics.at tick.before.shared parent.object).byteExact)
    {foreignReferences : ForeignReferences} {nativeCurrent : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before nativeCurrent)
    (joint : JointPublicationPrefix prior)
    (parentPrivate : prior.custody.current.source.custody.caps.family parent.object = some scope) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after nativeCurrent, JointPublicationPrefix next := by
  obtain ⟨next, catalogue, labels, bindings⟩ := descendant_creation_prefix_current namespaceLaws descriptors lifetimes
    references accounts objects metadata types lookup targets journal selected action present operation mode component parentLive
    comparison prior.custody.current.source.custody parentPrivate
  have ownership : CustodyOwnershipStep next.catalogue tick prior.custody.current.source.custody.caps.family next.caps.family :=
    nonremoving_ownership_step _ bindings labels
  let nextSource := prior.custody.current.source.advance next (by rw [catalogue]; exact fun _ member => member) ownership
  have noRoot := no_root_use_with_private_parent descriptors aliases lifetimes dataLookup cwdLookup journal anchor anchorLookup
    anchors prior.custody selected whole count action present parentLive parentPrivate
  let registered := prior.custody.sourceStep sdk lifetimes nextSource (by
    intro owner references closeExec directory impossible
    rw [impossible] at action
    cases action) (fun object allocated => .inl (labels object allocated)) catalogue ownership noRoot
  let result := prior.preserved registered catalogue labels
  exact ⟨result, joint.preserved registered catalogue labels ownership⟩

end LeanCage.Host.Kernel
