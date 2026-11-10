import FilesystemLookupAuthority
import FilesystemPrimitiveParentAuthority

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.lookup: Only actual per-operation lookup changes are excluded for an
-- active checked parent. Every public input mutation and raw operation remains in the history.
theorem native_parent_state_snapshots {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    (lifetimes : LifetimeContract runtime) (metadata : GlobalAuthorityContract runtime child)
    (nativeMetadata : NativeMetadataContract native) (lookup : LookupMutationContract (runtime := runtime) child native)
    {all : List (ActorTick runtime)} (authorityProfile : NativeAuthorityProfile native all hostUid)
    (lookupProfile : NativeLookupProfile native all hostUid)
    {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) (included : ∀ tick ∈ ticks, tick ∈ all)
    {prior last : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid prior callers ticks last next)
    (safe : NativeAuthorityJournal recording) {object : ObjectId} {information : Stat}
    (known : before.shared.information object = some information)
    (owner : information.uid = hostUid ∨ information.uid = 0) (old : before.shared.allocated object = true)
    (held : ∀ tick ∈ ticks, GloballyHeld tick.after object)
    (leases : ∀ tick ∈ ticks, Nonempty (ActiveParentLease runtime all tick.before hostUid object)) :
    (∃ later, after.shared.information object = some later ∧ SameAuthority information later ∧
      LookupBitsEqual before.shared after.shared object) ∧
    ∀ tick ∈ ticks, LookupBitsEqual before.shared tick.before.shared object ∧
      LookupBitsEqual before.shared tick.after.shared object := by
  induction journal generalizing prior callers information with
  | nil => exact ⟨⟨information, known, ⟨rfl, rfl, rfl⟩, rfl⟩, by intro tick impossible; cases impossible⟩
  | @cons tick ticks after tail ih =>
    cases recording with
    | cons current rest =>
      obtain ⟨position, bound, actual⟩ := List.mem_iff_getElem.mp (included tick (by simp))
      have selected : all[position]? = some tick := List.getElem?_eq_some_iff.mpr ⟨bound, actual⟩
      obtain ⟨lease⟩ := leases tick (by simp)
      have firstBits := native_step_lookup_bits lookup lookupProfile selected current safe.1 lease known owner old
        (held tick (by simp))
      obtain ⟨middle, actualMiddle, firstSame⟩ := native_step_parent_authority metadata nativeMetadata authorityProfile
        selected current safe.1 lease known owner (held tick (by simp))
      have middleOwner : middle.uid = hostUid ∨ middle.uid = 0 := by rw [firstSame.1]; exact owner
      have middleOld := actor_step_allocated lifetimes tick.operation object old
      obtain ⟨⟨later, actualLater, restSame, restBits⟩, snapshots⟩ := ih
        (by intro other member; exact included other (by simp [member])) rest safe.2 actualMiddle middleOwner middleOld
        (by intro other member; exact held other (by simp [member]))
        (by intro other member; exact leases other (by simp [member]))
      refine ⟨⟨later, actualLater, same_authority_trans firstSame restSame, lookup_bits_trans firstBits restBits⟩, ?_⟩
      intro other member
      rcases List.mem_cons.mp member with rfl | laterMember
      · exact ⟨rfl, firstBits⟩
      · exact ⟨lookup_bits_trans firstBits (snapshots other laterMember).1,
          lookup_bits_trans firstBits (snapshots other laterMember).2⟩

-- §FS-host-boundary.ownership: This consumes the actual source interval producer rather than
-- accepting a current parent handle, authority, flag frame, or detached safe callback trace.
theorem primitive_run_parent_state {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (raw : RawReferenceLifetimeContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (metadata : GlobalAuthorityContract runtime child) (nativeMetadata : NativeMetadataContract native)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (authorityProfile : NativeAuthorityProfile native ticks hostUid) (lookupProfile : NativeLookupProfile native ticks hostUid)
    {prior last : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid prior callers ticks last next)
    {backend : NativeAuthorityJournal recording}
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request}
    (selected : ticks[position]? = some tick) (present : tick.before.actors actor = some engine)
    (source : PrimitiveRunParent runtime initial ticks tick actor engine request) :
    ∃ interval : PrimitiveParentInterval process child native hostUid initial ticks tick actor engine request,
      ∃ information, tick.before.shared.information interval.parent.object = some information ∧
        Directories.trusted hostUid information = true ∧
        LookupBitsEqual interval.sampleTick.after.shared tick.before.shared interval.parent.object ∧
        ∀ current ∈ interval.events,
          LookupBitsEqual interval.sampleTick.after.shared current.before.shared interval.parent.object ∧
          LookupBitsEqual interval.sampleTick.after.shared current.after.shared interval.parent.object := by
  obtain ⟨interval⟩ := primitive_run_parent_interval (backend := backend) descriptors lifetimes references raw sdk accounts journal
    recording selected present source
  obtain ⟨⟨information, known, same, flags⟩, snapshots⟩ := native_parent_state_snapshots lifetimes metadata nativeMetadata lookup
    authorityProfile lookupProfile interval.journal interval.included interval.recording interval.safe interval.known
    interval.owner interval.old interval.held interval.leases
  exact ⟨interval, information, known, (same_authority_trusted hostUid same).trans interval.trusted, flags, snapshots⟩

end LeanCage.Host.Kernel
