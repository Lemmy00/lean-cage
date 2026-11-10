import FilesystemPublishedCustody
import FilesystemByteNamespaceFrames

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: Every removed name and released private label in this
-- publication step belongs to its actual source owner. Other bindings are preserved by
-- the individual rename primitive law, including error/lost acknowledgements.
theorem source_publication_ownership_step_with_frame {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {resources : PrimitiveCommitResources runtime initial all tick actor engine request observed}
    {caps : Capabilities} {catalogue : Catalogue runtime all}
    (root : CommitRootAt runtime resources caps.family catalogue)
    (_actual : kernel.step (tick.before.project engine) request observed tick.after.shared)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (moving : request.op = .renameNew)
    (otherSource : ∀ parent name object, tick.before.shared.entries parent name = some object →
      ¬ NamesEntry (tick.before.project engine) request.first request.left parent name →
      tick.after.shared.entries parent name = some object) :
    CustodyOwnershipStep catalogue tick caps.family (caps.published tick.after.shared root.root.object).family := by
  have mutation : OwnerMutation catalogue tick root.root.object :=
    ⟨actor, request, observed, action, .inr moving, root.owned⟩
  have sourceBound : tick.before.shared.entries root.root.parent root.root.name = some root.root.object := by
    rw [← root.container, ← root.name]
    exact root.bound
  constructor
  · intro parent name object scope bound privateObject missing
    have named : NamesEntry (tick.before.project engine) request.first request.left parent name := by
      by_cases outside : NamesEntry (tick.before.project engine) request.first request.left parent name
      · exact outside
      · exact False.elim (missing (otherSource parent name object bound outside))
    obtain ⟨handle, live, sameParent, sameName⟩ := named
    obtain ⟨sourceHandle, sourceLive, sourceParent, sourceName⟩ := root.root_entry
    have sameHandle : handle = sourceHandle := Option.some.inj (live.symm.trans sourceLive)
    have parents : parent = root.root.parent := sameParent.symm.trans ((congrArg Handle.object sameHandle).trans sourceParent)
    have names : name = root.root.name := sameName.symm.trans sourceName
    have sameObject : object = root.root.object := by
      rw [parents, names, sourceBound] at bound
      exact Option.some.inj bound.symm
    have sameScope : scope = root.root.object := by
      rw [sameObject] at privateObject
      exact Option.some.inj (privateObject.symm.trans root.privateRoot)
    exact sameScope.symm ▸ mutation
  · intro object scope allocated privateObject released
    by_cases same : scope = root.root.object
    · exact same.symm ▸ mutation
    · have different : caps.family object ≠ some root.root.object := by
        intro other
        exact same (Option.some.inj (privateObject.symm.trans other))
      have kept : (caps.published tick.after.shared root.root.object).family object = some scope := by
        simp only [Capabilities.published, clearFamily, ite_eq_right different]
        exact privateObject
      exact False.elim (released kept)

-- §AR-host-boundary.interfaces: Preserve the original logical exact-name consumer.
theorem source_publication_ownership_step {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (namespaceLaws : NamespaceContract kernel)
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {resources : PrimitiveCommitResources runtime initial all tick actor engine request observed}
    {caps : Capabilities} {catalogue : Catalogue runtime all}
    (root : CommitRootAt runtime resources caps.family catalogue)
    (actual : kernel.step (tick.before.project engine) request observed tick.after.shared)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (moving : request.op = .renameNew) :
    CustodyOwnershipStep catalogue tick caps.family (caps.published tick.after.shared root.root.object).family := by
  exact source_publication_ownership_step_with_frame root actual action moving
    (fun parent name object bound outside =>
      namespaceLaws.rename_other_source _ _ _ _ _ _ _ actual moving root.components bound outside)

-- §FS-host-boundary.lookup: The raw rename frames other bindings only after its
-- actual source/probes establish current byte-exact operands.
theorem source_publication_ownership_step_byte {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {semantics : NameSemanticsView} (namespaceLaws : ByteNamespaceFrameContract kernel semantics)
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {resources : PrimitiveCommitResources runtime initial all tick actor engine request observed}
    {caps : Capabilities} {catalogue : Catalogue runtime all}
    (root : CommitRootAt runtime resources caps.family catalogue)
    (actual : kernel.step (tick.before.project engine) request observed tick.after.shared)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (moving : request.op = .renameNew)
    (comparison : ByteNamespaceOperands semantics (tick.before.project engine) request) :
    CustodyOwnershipStep catalogue tick caps.family (caps.published tick.after.shared root.root.object).family := by
  exact source_publication_ownership_step_with_frame root actual action moving
    (fun parent name object bound outside =>
      namespaceLaws.renameOtherSource _ _ _ _ _ _ _ actual moving root.components comparison bound outside)

end LeanCage.Host.Kernel
