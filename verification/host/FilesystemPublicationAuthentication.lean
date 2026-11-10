import FilesystemCommitPublication
import FilesystemInstalledExposure

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.publication: Join the already produced SAME current commit
-- state with the actual selected installation's key. A committed error/loss
-- still exposes its real source query; the collision alternative stays explicit.
theorem PublicationCommitStep.installed_authentication
    {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {sha256 : ByteArray → ByteArray} {hmac : ByteArray → ByteArray → ByteArray}
    (crypto : CryptographicContract kernel sha256 hmac)
    (attributes : TrackedAttributeContract kernel) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (objects : ObjectLifetimeContract runtime)
    (existing : ExistingAttributeContract runtime child) (foreign : ForeignContract runtime)
    (nativeAttributes : NativeExistingAttributeContract native)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {firstProcesses lastProcesses : Processes} {firstNative lastNative : NativeProcesses}
    {recording : NativeExternalJournal process child native hostUid firstProcesses firstNative all lastProcesses lastNative}
    (execution : RegisteredCustodyExecution runtime initial all hostUid dataObjects directories semantics recording
      [] (Population.empty initial) final)
    {backend : NativeAuthorityJournal recording}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {currentNative : NativeProcesses}
    {prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (step : PublicationCommitStep runtime prior actor engine request observed)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ tick :: trailing)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    {bootstrap : BootstrapCatalogue initial}
    (selection : BootstrapSelection bootstrap step.authority.resources.source.invocation.effective)
    (installed : InstalledPublicationKey bootstrap sha256 selection.root
      step.authority.resources.source.invocation.authenticated.bundle.manifest)
    (moving : request.op = .renameNew) :
    (tick.after.shared.entries = tick.before.shared.entries ∧
      step.updated.custody.current.source.custody.caps = prior.custody.current.source.custody.caps.retain tick.after.shared) ∨
    (∃ _delta : CommitDelta step.authority.resources step.root.root.object,
      ∃ marker : CommitMarkerAt (position := processed.length) runtime step.root hmac,
        (KeyDigestCollision sha256 marker.receipt.key installed.secret ∨
          (marker.receipt.key = installed.secret ∧
            Nonempty (ExposedSourceQuery runtime initial all hmac installed.secret marker.receipt.message
              (processed.length + 1)))) ∧
        step.updated.custody.current.source.custody.caps =
          prior.custody.current.source.custody.caps.published tick.after.shared step.root.root.object) := by
  rcases step.effect with unchanged | ⟨⟨delta⟩, published⟩
  · exact .inl unchanged
  · have selected : all[processed.length]? = some tick := by
      rw [whole, List.getElem?_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem?_cons_zero]
    obtain ⟨marker, query⟩ := actual_installed_commit_source_exposure_attributes (backend := backend)
      crypto attributes descriptors lifetimes objects existing foreign nativeAttributes execution selected action present
      step.root selection installed moving delta (Nat.lt_succ_self _)
    exact .inr ⟨delta, marker, query, published⟩

end LeanCage.Host.Kernel
