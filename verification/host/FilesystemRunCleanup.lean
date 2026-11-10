import FilesystemRunSetupRemoval
import FilesystemUnlinkOrigins

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: Every real run/validator cleanup source route
-- feeds the SAME current operation and application-built joint prefix. The
-- source-origin constructors retain setup errors and genuine reaping guards.
theorem actual_run_cleanup_origin_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (frames : ByteNamespaceFrameContract kernel semantics) (otherDirectories : UnlinkDirectoryFrameContract kernel)
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    (raw : RawReferenceLifetimeContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (accounts : AccountContract kernel hostUid) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child) (authority : GlobalAuthorityContract runtime child)
    (nativeMetadata : NativeMetadataContract native) (lookup : LookupMutationContract (runtime := runtime) child native)
    (probes : LookupPrimitiveContract kernel.step kernel.interference semantics)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (mounts : MountContract kernel initial.allocated)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    (authorityProfile : NativeAuthorityProfile native all hostUid) (lookupProfile : NativeLookupProfile native all hostUid)
    {beforeProcesses afterProcesses : Processes} {first last : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid beforeProcesses first all afterProcesses last)
    {backend : NativeAuthorityJournal recording}
    {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {foreignReferences : ForeignReferences} {currentNative : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    (joint : JointPublicationPrefix prior)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ tick :: trailing)
    {before : List Program.Event} {sourceObserved : Option Reply}
    (source : RunCleanupOrigin before request sourceObserved)
    (unlink : request.op = .unlinkAt) :
    sourceObserved = none → ∀ outside, adapter.occurrence.logicalBefore = outside ++ before →
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
        foreignReferences (processed ++ [tick]) tick.after currentNative,
      next.custody.current.source.custody.catalogue = prior.custody.current.source.custody.catalogue ∧
      next.custody.current.source.custody.caps.family = prior.custody.current.source.custody.caps.family ∧
      JointPublicationPrefix next := by
  have selected : all[processed.length]? = some tick := by
    rw [whole, List.getElem?_append_right (by omega)]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  induction source with
  | creating invocation =>
    intro pending outside trace
    cases pending
    let actual : RunCreationPrefix adapter.occurrence.logicalBefore _ none := {
      context := outside ++ invocation.context
      inside := invocation.inside
      active := invocation.active
      trace := trace.trans ((congrArg (outside ++ ·) invocation.trace).trans (by simp only [List.append_assoc])) }
    exact actual_run_setup_unlink_joint namespaceLaws frames descriptors lifetimes references environment sdk accounts
      objects metadata lookup journal action present adapter prior joint whole actual unlink
  | failedWrite bytes context writing error written inside active sourceTrace =>
    intro pending outside trace
    cases pending
    obtain ⟨selectedInside, insideTrace, ⟨parent⟩⟩ := actual_validator_failed_write_cleanup_parent descriptors lifetimes
      references environment journal selected present adapter bytes context written active (by
        rw [sourceTrace] at trace
        simpa only [List.append_assoc] using trace) unlink
    exact actual_run_cleanup_unlink_joint (backend := backend) namespaceLaws frames otherDirectories descriptors lifetimes
      references raw sdk accounts objects metadata authority nativeMetadata lookup probes mounts journal authorityProfile
      lookupProfile recording action present adapter prior joint whole parent unlink
  | observedChild bundle bytes context reaped inside active sourceTrace =>
    intro pending outside trace
    cases pending
    obtain ⟨selectedInside, insideTrace, ⟨parent⟩⟩ := actual_validator_observed_cleanup_parent descriptors lifetimes references
      environment sdk journal selected present adapter context active (by
        rw [sourceTrace] at trace
        simpa only [List.append_assoc] using trace) unlink
    exact actual_run_cleanup_unlink_joint (backend := backend) namespaceLaws frames otherDirectories descriptors lifetimes
      references raw sdk accounts objects metadata authority nativeMetadata lookup probes mounts journal authorityProfile
      lookupProfile recording action present adapter prior joint whole parent unlink
  | running caller bundle duration context known inside active sourceTrace =>
    intro pending outside trace
    cases pending
    obtain ⟨selectedInside, insideTrace, ⟨parent⟩⟩ := actual_vm_cleanup_parent descriptors lifetimes references environment sdk
      journal selected present adapter context active (by
        rw [sourceTrace] at trace
        simpa only [List.append_assoc] using trace) unlink
    exact actual_run_cleanup_unlink_joint (backend := backend) namespaceLaws frames otherDirectories descriptors lifetimes
      references raw sdk accounts objects metadata authority nativeMetadata lookup probes mounts journal authorityProfile
      lookupProfile recording action present adapter prior joint whole parent unlink
  | prepend source context sourceTrace ih =>
    intro pending outside trace
    cases pending
    apply ih action adapter unlink rfl (outside ++ context)
    exact trace.trans ((congrArg (outside ++ ·) sourceTrace).trans (by simp only [List.append_assoc]))

end LeanCage.Host.Kernel
