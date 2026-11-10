import FilesystemNamespaceMetadata

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: A genuine unchanged namespace delta retains the custody registry.
-- This is one actual tick, including a failed/lost mutation with no committed namespace change.
theorem unchanged_namespace_custody {kernel : Contract} {runtime : ActorRuntime kernel}
    {process : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    {initialObjects : ObjectId → Bool} {dataObjects directories : ObjectId → Prop}
    (lifetimes : LifetimeContract runtime) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime primitive)
    {prior next : Processes} {tick : ActorTick runtime}
    (source : ExternalStep process primitive hostUid prior tick next) (safe : ExternalAuthoritySafe source)
    {caps : Capabilities} {references : ForeignReferences}
    (state : NamespaceCustody tick.before.shared caps hostUid initialObjects dataObjects directories references)
    (entries : tick.after.shared.entries = tick.before.shared.entries)
    (live : LiveNamespace tick.after.shared) :
    NamespaceCustody tick.after.shared (caps.retain tick.after.shared) hostUid
      initialObjects dataObjects directories references ∧
    ∀ root ∈ caps.roots, root ∈ (caps.retain tick.after.shared).roots := by
  have allocation : ∀ object, tick.before.shared.allocated object = true → tick.after.shared.allocated object = true :=
    fun object => actor_step_allocated lifetimes tick.operation object
  have oldBinding : ∀ parent name object, tick.after.shared.entries parent name = some object →
      tick.before.shared.entries parent name = some object := by
    intro parent name object binding
    rw [entries] at binding
    exact binding
  constructor
  · refine ⟨retained_capabilities_valid state.registry allocation,
      family_graph_delete state.graph allocation oldBinding,
      root_boundaries_retain state.boundaries (fun parent name object scope binding label => oldBinding _ _ _ binding),
      external_retained_root_authorities metadata source safe state.authorities live,
      retained_private_directory_authority objects metadata source safe state.graph state.privateDirectories
        (fun object scope label => ⟨scope, label⟩),
      state.scopes, ?_, ?_⟩
    · exact foreign_references_public_retained state.foreignSafe allocation
        (by intro object allocated publicObject; exact publicObject)
    · intro parent name object binding
      have old := state.wellFormed _ _ _ (oldBinding _ _ _ binding)
      exact ⟨allocation _ old.1, allocation _ old.2⟩
  · intro root member
    apply List.mem_filter.mpr
    have bound : tick.after.shared.entries root.parent root.name = some root.object := by
      rw [entries]
      exact (state.registry.1 root member).2.2.1
    exact ⟨member, by simpa using bound⟩

end LeanCage.Host.Kernel
