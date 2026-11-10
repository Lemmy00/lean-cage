import FilesystemFamilyAuthority

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: All fields are produced from births and actual syscall steps.
structure NamespaceCustody (world : World) (caps : Capabilities) (hostUid : Nat)
    (initialObjects : ObjectId → Bool) (dataObjects directories : ObjectId → Prop)
    (foreignReferences : ForeignReferences) : Prop where
  registry : caps.Valid world
  graph : FamilyGraph world caps.family initialObjects dataObjects
  boundaries : RootBoundaries caps world
  authorities : RootAuthorities caps world hostUid
  privateDirectories : PrivateDirectoryAuthority world caps.family hostUid directories
  scopes : ScopeDirectories caps.family directories
  foreignSafe : ForeignReferenceSafe world caps.family directories foreignReferences
  wellFormed : NamespaceWellFormed world

theorem initial_namespace_custody (world : World) (hostUid : Nat) (dataObjects directories : ObjectId → Prop)
    (foreignReferences : ForeignReferences) (wellFormed : NamespaceWellFormed world)
    (live : ∀ object, foreignReferences object = true → world.allocated object = true) :
    NamespaceCustody world Capabilities.empty hostUid world.allocated dataObjects directories foreignReferences := by
  refine ⟨empty_capabilities_valid world, empty_family_graph world world.allocated dataObjects,
    empty_root_boundaries world, ?_, ?_, empty_scope_directories directories, ⟨live, ?_⟩, wellFormed⟩
  · intro root impossible
    cases impossible
  · intro object scope information impossible
    cases impossible
  · intro object scope held impossible
    cases impossible

private theorem actual_foreign_step {kernel : Contract} {runtime : ActorRuntime kernel}
    {caller : Credentials} {before after : Population} (actual : ActorStep runtime (.foreign caller) before after) :
    runtime.foreign caller before.shared after.shared := by
  cases actual with
  | foreign operation => exact operation

-- §FS-host-boundary.ownership: Ordinary foreign namespace changes preserve private custody.
-- Public changes, O_PATH root references and pending lookups remain in the primitive observation.
theorem ordinary_namespace_custody {kernel : Contract} {runtime : ActorRuntime kernel}
    {process : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    {initialObjects : ObjectId → Bool} {dataObjects directories : ObjectId → Prop}
    (lifetimes : LifetimeContract runtime) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime primitive)
    (foreign : ForeignContract runtime) (authority : ForeignAuthorityContract runtime)
    {prior next : Processes} {tick : ActorTick runtime} {caller : Credentials}
    (processStep : process.step tick prior next) (action : tick.action = .foreign caller)
    (allowed : OrdinaryForeign caller hostUid) {caps : Capabilities} {before after : ForeignReferences}
    (view : DirectoryView tick.before.shared directories)
    (observation : ForeignNamespaceObservation tick.before.shared tick.after.shared before after
      initialObjects directories caller)
    (state : NamespaceCustody tick.before.shared caps hostUid initialObjects dataObjects directories before) :
    NamespaceCustody tick.after.shared (caps.retain tick.after.shared) hostUid
      initialObjects dataObjects directories after ∧
    ∀ root ∈ caps.roots, root ∈ (caps.retain tick.after.shared).roots := by
  have operation : runtime.foreign caller tick.before.shared tick.after.shared :=
    actual_foreign_step (action ▸ tick.operation)
  have allocation : ∀ object, tick.before.shared.allocated object = true → tick.after.shared.allocated object = true :=
    fun object => lifetimes.foreign _ _ _ object operation
  have boundary := root_boundaries_authority state.boundaries state.authorities
  have earlier : ∀ parent name object scope,
      tick.after.shared.entries parent name = some object → caps.family object = some scope →
      tick.before.shared.entries parent name = some object := by
    intro parent name object scope binding label
    exact foreign_private_binding_earlier state.graph view state.privateDirectories boundary
      state.foreignSafe allowed observation binding label
  let source : ExternalStep process primitive hostUid prior tick next :=
    .ordinary caller processStep action allowed
  have rootAuthorities := ordinary_foreign_root_authorities foreign authority operation allowed
    state.registry state.authorities
  constructor
  · refine ⟨retained_capabilities_valid state.registry allocation,
      foreign_namespace_family state.graph view state.privateDirectories boundary state.foreignSafe
        allowed observation allocation,
      root_boundaries_retain state.boundaries earlier,
      ?_, ?_, state.scopes,
      foreign_namespace_references state.graph view state.privateDirectories state.scopes state.foreignSafe
        allowed observation,
      foreign_namespace_well_formed observation state.wellFormed allocation⟩
    · intro root kept
      exact rootAuthorities root (List.mem_filter.mp kept).1
    · exact retained_private_directory_authority objects metadata source True.intro state.graph
        state.privateDirectories (fun object scope label => ⟨scope, label⟩)
  · intro root member
    apply List.mem_filter.mpr
    have bound := ordinary_foreign_preserves_root foreign operation allowed
      state.registry state.authorities root member
    exact ⟨member, by simpa using bound⟩

end LeanCage.Host.Kernel
