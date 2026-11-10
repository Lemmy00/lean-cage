import FilesystemRootUseAuthority
import FilesystemRootOpenReceipt

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: The actual source reopen receipt feeds the custody
-- step even when this open's acknowledgement fails or is lost. Its original
-- acknowledged mkdir and source-selected parent/name are derived, never replaced.
theorem root_receipt_registered_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    (namespaceLaws : PassiveNamespaceContract kernel) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (targets : OpenTargetContract kernel semantics initial.allocated dataObjects)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    {position : Nat} {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (receipt : RootOpenReceipt runtime initial all tick actor engine request position)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ tick :: trailing) (count : processed.length = position)
    (selected : all[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (opening : request.op = .openAt) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative) := by
  have bound : receipt.birthPosition < processed.length := by rw [count]; exact receipt.earlier
  have birthAt : processed[receipt.birthPosition]? = some receipt.birthTick := by
    simpa only [whole, List.getElem?_append_left bound] using receipt.birthAt
  have reserved : PrivateNames.reservedBytes request.left = true := by
    rw [receipt.sameName]
    exact receipt.use.reserved
  have notDot : request.left ≠ ".".toUTF8 := by
    intro same
    rw [same] at reserved
    exact Bool.noConfusion reserved
  have notUp : request.left ≠ "..".toUTF8 := by
    intro same
    rw [same] at reserved
    exact Bool.noConfusion reserved
  exact root_reopen_custody namespaceLaws descriptors lifetimes references sdk accounts objects metadata lookup targets journal
    prior birthAt receipt.use selected (by simpa only [receipt.sameActor] using action)
    (by simpa only [receipt.sameActor] using present) opening receipt.flags receipt.sameName receipt.reference
    notDot notUp receipt.probes

end LeanCage.Host.Kernel
