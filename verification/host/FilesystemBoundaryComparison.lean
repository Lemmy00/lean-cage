import FilesystemCreationDeltas
import FilesystemLookupNames
import FilesystemBoundaries

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.lookup: Comparison is retained only at live private boundaries. Public
-- input directories without such a binding remain free to change their lookup flags.
def RegisteredRootNames (caps : Capabilities) (semantics : NameSemanticsView) (world : World) : Prop :=
  ∀ root ∈ caps.roots, (semantics.at world root.parent).byteExact

theorem empty_registered_root_names (semantics : NameSemanticsView) (world : World) :
    RegisteredRootNames Capabilities.empty semantics world := by
  intro root impossible
  cases impossible

theorem registered_boundaries_exact {caps : Capabilities} {semantics : NameSemanticsView} {world : World}
    (boundaries : RootBoundaries caps world) (names : RegisteredRootNames caps semantics world) :
    ExactPrivateBoundaries semantics world caps.family := by
  intro parent name child scope binding label publicParent
  obtain ⟨root, member, sameParent, sameName, sameObject⟩ := boundaries _ _ _ _ binding label publicParent
  simpa only [sameParent] using names root member

-- §FS-host-boundary.lookup: After the fresh binding exists, each actual ext4 flag/encryption
-- setter sees a nonempty directory under its inode lock. No active-source-FD lease is assumed.
theorem native_registered_root_names {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {native : NativePrimitive kernel} {semantics : NameSemanticsView}
    (nonempty : NativeNonemptyLookupContract native semantics)
    {before after : NativeProcesses} {tick : ActorTick runtime}
    (call : NativeCallAt native tick before after) {caps : Capabilities}
    (valid : caps.Valid tick.before.shared) (names : RegisteredRootNames caps semantics tick.before.shared) :
    RegisteredRootNames (caps.retain tick.after.shared) semantics tick.after.shared := by
  intro root member
  have prior := (List.mem_filter.mp member).1
  have exactBefore := names root prior
  rcases exactBefore with temporary | ⟨ext, flags⟩
  · exact .inl temporary
  · have same := nonempty.existing call root.parent root.name root.object
      (valid.1 root prior).2.2.1 ext
    exact byte_exact_after_lookup_bits (.inr ⟨ext, flags⟩) same

theorem filesystem_registered_root_names {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {semantics : NameSemanticsView}
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {tick : ActorTick runtime} (filesystem : actionFamily tick.action = .filesystem)
    (safe : AuthoritySafeAction tick.action) {caps : Capabilities}
    (valid : caps.Valid tick.before.shared) (names : RegisteredRootNames caps semantics tick.before.shared) :
    RegisteredRootNames (caps.retain tick.after.shared) semantics tick.after.shared := by
  intro root member
  have kept := List.mem_filter.mp member
  have binding : tick.after.shared.entries root.parent root.name = some root.object := by simpa using kept.2
  have held : GloballyHeld tick.after root.parent := .inr (.inr ⟨root.name, root.object, binding⟩)
  exact byte_exact_after_lookup_bits (names root kept.1)
    (lookup.filesystem root.parent tick.operation filesystem safe (valid.1 root kept.1).2.1 held)

-- §FS-host-boundary.lookup: The new boundary uses the SAME current accepted-parent proof;
-- older boundaries derive their post-mkdir comparison from individual physical effects.
theorem created_registered_root_names {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {semantics : NameSemanticsView}
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {tick : ActorTick runtime} {engine : EngineState} {request : Request}
    (filesystem : actionFamily tick.action = .filesystem) (safe : AuthoritySafeAction tick.action)
    {dataObjects : ObjectId → Prop}
    (delta : FreshDirectoryDelta dataObjects request (tick.before.project engine) tick.after.shared)
    (actor : ActorId) {caps : Capabilities} (valid : caps.Valid tick.before.shared)
    (names : RegisteredRootNames caps semantics tick.before.shared)
    (parentNames : (semantics.at tick.before.shared delta.parent.object).byteExact) :
    RegisteredRootNames (caps.addRoot ⟨actor, delta.object, delta.parent.object, request.left⟩) semantics tick.after.shared := by
  intro root member
  rcases List.mem_cons.mp member with rfl | old
  · have held : GloballyHeld tick.after delta.parent.object := .inr (.inr ⟨request.left, delta.object, delta.bound⟩)
    exact byte_exact_after_lookup_bits parentNames
      (lookup.filesystem delta.parent.object tick.operation filesystem safe delta.parentLive held)
  · have held : GloballyHeld tick.after root.parent := .inr (.inr
      ⟨root.name, root.object, delta.preserves_binding (valid.1 root old).2.2.1⟩)
    exact byte_exact_after_lookup_bits (names root old)
      (lookup.filesystem root.parent tick.operation filesystem safe (valid.1 root old).2.1 held)

end LeanCage.Host.Kernel
