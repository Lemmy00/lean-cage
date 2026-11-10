import FilesystemPrimitiveProbes
import FilesystemPrimitiveChunks

namespace LeanCage.Host.Kernel
open Filesystem

def RetainingEvent : Program.Event → Prop
  | .returned (.filesystem request) _ => RetainsDescriptors request.op
  | _ => False

-- §AR-host-boundary.primitives: The frame is derived from the actual individual source calls.
-- Shared data, OFD offsets and other actors' namespace effects remain unrestricted.
theorem actor_retaining_event_handles {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (descriptors : DescriptorContract kernel)
    {actor : ActorId} {origin : OperationOrigin} {ordinal : Nat} {before after : World}
    {events : List Program.Event}
    (history : ActorHistoryWith runtime actor origin ordinal before events after)
    (profile : ∀ event ∈ events, RetainingEvent event) : after.handles = before.handles := by
  induction history with
  | nil => rfl
  | @returned β effect reply before middle after ordinal events actual recorded tail ih =>
    have head := profile (.returned effect reply) (by simp)
    have rest := ih (by intro event member; exact profile event (by simp [member]))
    cases effect with
    | filesystem request => exact rest.trans (descriptors.retained _ _ _ _ actual head)
    | spawn | read | wait | terminate | tryWait | descriptor => cases head
  | environment actual tail ih =>
    exact (ih profile).trans (kernel.interference_handles _ _ actual)

theorem random_request_profile (fuel count : Nat) (bytes : ByteArray) :
    RequestProfile (fun request => request.op = .random) (Directories.randomBytes fuel count bytes) := by
  induction fuel generalizing bytes with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold Directories.randomBytes
    split
    · exact .pure _
    · split
      · exact .pure _
      · apply RequestProfile.call (allowed := fun request => request.op = .random) _ _ rfl
        intro reply
        split
        · exact .pure _
        · split
          · exact .pure _
          · exact ih _

theorem random_events_identity {fuel count : Nat} {bytes : ByteArray}
    {events : List (Request × Reply)} {result : Result ByteArray}
    (source : Returns (Directories.randomBytes fuel count bytes) events result) :
    ∀ event ∈ events.map Program.filesystemEvent, PrimitiveFilesystem.IdentityEvent event := by
  intro event member
  obtain ⟨⟨request, reply⟩, occurs, same⟩ := List.mem_map.mp member
  subst event
  exact PrimitiveFilesystem.random_identity request (profile_returns (random_request_profile _ _ _) source _ occurs)

theorem random_events_retaining {fuel count : Nat} {bytes : ByteArray}
    {events : List (Request × Reply)} {result : Result ByteArray}
    (source : Returns (Directories.randomBytes fuel count bytes) events result) :
    ∀ event ∈ events.map Program.filesystemEvent, RetainingEvent event := by
  intro event member
  obtain ⟨⟨request, reply⟩, occurs, same⟩ := List.mem_map.mp member
  subst event
  have operation := profile_returns (random_request_profile _ _ _) source (request, reply) occurs
  change RetainsDescriptors request.op
  rw [operation]
  simp [RetainsDescriptors]

theorem adapter_namespace_prefix_retaining {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed)
    (kind : NamespaceRequest request) :
    ∀ event ∈ adapter.occurrence.inside.map Program.filesystemPrefixEvent, RetainingEvent event := by
  obtain ⟨checks, checked, same, trace⟩ := guarded_namespace_last adapter.occurrence.adapter kind
  intro event member
  rw [trace, List.map_map] at member
  obtain ⟨⟨query, reply⟩, occurs, same⟩ := List.mem_map.mp member
  subst event
  have operation := checked_parents_probes checked (query, reply) occurs
  change RetainsDescriptors query.op
  rcases operation with magic | flags
  · rw [magic]; simp [RetainsDescriptors]
  · rw [flags]; simp [RetainsDescriptors]

end LeanCage.Host.Kernel
