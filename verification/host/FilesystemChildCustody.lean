import FilesystemPublicationProgress
import FilesystemUnchangedSource

namespace LeanCage.Host.Kernel
open Filesystem

private theorem foreign_actors {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {before after : Population} {caller : Credentials} (actual : ActorStep runtime (.foreign caller) before after) :
    after.actors = before.actors := by
  cases actual
  rfl

-- §FS-host-boundary.ownership: This case consumes ONE actual child syscall row
-- and its separately derived source/namespace observation. It does not frame a
-- controller/QEMU lifetime, invent a wait result, or discard child descriptors.
theorem child_unchanged_registered_publication {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    (sdk : RuntimeDescriptorContract runtime) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (heldMetadata : GlobalAuthorityContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {all processed : List (ActorTick runtime)} {tick : ActorTick runtime}
    {before after : Processes} (_recorded : process.step tick before after)
    (call : ChildCallAt child tick before after) (safe : ChildAuthoritySafe call.operation)
    (entries : tick.after.shared.entries = tick.before.shared.entries)
    {foreignReferences : ForeignReferences} {callers : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before callers) :
    Nonempty (RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after callers) := by
  let previous := prior.custody.current.source.custody.namespaceState
  have allocation := fun object => actor_step_allocated lifetimes tick.operation object
  have earlier : ∀ parent name object, tick.after.shared.entries parent name = some object →
      tick.before.shared.entries parent name = some object := by
    intro parent name object bound
    rwa [entries] at bound
  have authorities : RootAuthorities (prior.custody.current.source.custody.caps.retain tick.after.shared)
      tick.after.shared hostUid := by
    intro root member
    have old := (List.mem_filter.mp member).1
    have bound : tick.after.shared.entries root.parent root.name = some root.object := by
      simpa using (List.mem_filter.mp member).2
    obtain ⟨childInfo, parentInfo, childKnown, parentKnown, owner, mode, directory, trusted⟩ := previous.authorities root old
    obtain ⟨laterChild, laterChildKnown, sameChild⟩ := heldMetadata.child call _ _ safe (.inr (.inl ⟨root.parent, root.name, bound⟩)) childKnown
    obtain ⟨laterParent, laterParentKnown, sameParent⟩ := heldMetadata.child call _ _ safe (.inr (.inr ⟨root.name, root.object, bound⟩)) parentKnown
    exact ⟨laterChild, laterParent, laterChildKnown, laterParentKnown, sameChild.1.trans owner,
      (same_authority_mask sameChild 63 (by decide)).trans mode,
      (same_authority_directory sameChild).trans directory, (same_authority_trusted hostUid sameParent).trans trusted⟩
  have privateDirectories : PrivateDirectoryAuthority tick.after.shared
      prior.custody.current.source.custody.caps.family hostUid directories := by
    intro object scope information label known directory
    have alive : ObjectAlive tick.after.shared object := ⟨information, known⟩
    obtain ⟨oldInformation, oldKnown⟩ := actor_step_live_backward_for objects tick.operation
      (previous.graph.live object scope label) alive
    obtain ⟨owner, mask⟩ := previous.privateDirectories object scope oldInformation label oldKnown directory
    obtain ⟨later, laterKnown, same⟩ := metadata.child call object oldInformation safe alive oldKnown
    have identity := Option.some.inj (known.symm.trans laterKnown)
    subst later
    exact ⟨same.1.trans owner, (same_authority_mask same 63 (by decide)).trans mask⟩
  have state : NamespaceCustody tick.after.shared
      (prior.custody.current.source.custody.caps.retain tick.after.shared) hostUid initial.allocated
      dataObjects directories foreignReferences := by
    refine ⟨retained_capabilities_valid previous.registry allocation,
      family_graph_delete previous.graph allocation earlier,
      root_boundaries_retain previous.boundaries (by intro parent name object scope bound label; exact earlier _ _ _ bound),
      authorities, privateDirectories, previous.scopes,
      ⟨fun object held => allocation _ (previous.foreignSafe.1 object held), previous.foreignSafe.2⟩, ?_⟩
    intro parent name object bound
    have old := previous.wellFormed _ _ _ (earlier _ _ _ bound)
    exact ⟨allocation _ old.1, allocation _ old.2⟩
  have names : RegisteredRootNames (prior.custody.current.source.custody.caps.retain tick.after.shared)
      semantics tick.after.shared := by
    intro root member
    have kept := List.mem_filter.mp member
    have bound : tick.after.shared.entries root.parent root.name = some root.object := by simpa using kept.2
    exact byte_exact_after_lookup_bits (prior.custody.current.source.custody.names root kept.1)
      (lookup.child call root.parent safe (previous.registry.1 root kept.1).2.1 (.inr (.inr ⟨root.name, root.object, bound⟩)))
  have actors := foreign_actors (call.action ▸ tick.operation)
  have owned : EngineReferencesOwned runtime all tick.after prior.custody.current.source.custody.caps.family
      prior.custody.current.source.custody.catalogue := by
    intro actor engine present fd handle scope live label
    rw [actors] at present
    exact prior.custody.current.source.custody.references actor engine present fd handle scope live label
  let next := prior.custody.current.source.custody.advance descriptors lifetimes references
    (prior.custody.current.source.custody.caps.retain tick.after.shared) prior.custody.current.source.custody.catalogue
    state names (catalogue_retained_covers prior.custody.current.source.custody.coverage)
    (catalogue_advance_valid prior.custody.current.source.custody.valid allocation) owned .same
  have ownership : CustodyOwnershipStep next.catalogue tick prior.custody.current.source.custody.caps.family next.caps.family :=
    nonremoving_ownership_step _ (by intro parent name object bound; rwa [entries]) (by intro object allocated; rfl)
  let nextSource := prior.custody.current.source.advance next (by intro record member; exact member) ownership
  let registered := prior.custody.sourceStep sdk lifetimes nextSource (by
      intro actor handles closeExec directory impossible
      rw [call.action] at impossible
      cases impossible) (unchanged_existing_labels _ _ _) rfl ownership
    (no_root_use_of_nonfilesystem (by rw [call.action]; intro impossible; cases impossible))
  exact ⟨prior.preserved registered rfl (by intro object allocated; rfl)⟩

end LeanCage.Host.Kernel
