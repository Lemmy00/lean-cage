import FilesystemLoweredPhases

namespace LeanCage.Host.Kernel.Lowered
open Filesystem

def CopyOperation (request : Request) : Prop := request.op = .read ∨ request.op = .stat

theorem read_loop_profile (fuel : Nat) (fd : UInt64) (limit : Nat) (bytes : ByteArray) :
    RequestProfile CopyOperation (readLoop fuel fd limit bytes) := by
  induction fuel generalizing bytes with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold readLoop
    split
    · exact .pure _
    · apply RequestProfile.call _ _ (.inl rfl)
      intro reply
      split
      · exact .pure _
      · split
        · exact .pure _
        · split
          · exact .pure _
          · split
            · exact .pure _
            · exact ih _

theorem copy_profile (fd : UInt64) (limit : Nat) : RequestProfile CopyOperation (copyOpened fd limit) := by
  unfold copyOpened
  apply RequestProfile.call _ _ (.inr rfl)
  intro reply
  split
  · exact .pure _
  · split
    · exact .pure _
    · apply profile_bind (read_loop_profile _ _ _ _)
      intro result
      cases result with
      | error => exact .pure _
      | ok bytes =>
        apply RequestProfile.call _ _ (.inr rfl)
        intro finalReply
        split
        · exact .pure _
        · split <;> exact .pure _

theorem copy_operation_identity (request : Request) (kind : CopyOperation request) :
    PrimitiveFilesystem.lowerEffect (.filesystem request) = Program.effect (.filesystem request) := by
  cases request with
  | mk operation first second third left right =>
    rcases kind with rfl | rfl <;> rfl

theorem copy_prefix_identity (fd : UInt64) (limit : Nat)
    {events : List (Request × Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (copyOpened fd limit) (Publication.completed events ++ [(request, observed)])) :
    ∀ event ∈ events.map Program.filesystemEvent, PrimitiveFilesystem.IdentityEvent event := by
  intro event member
  obtain ⟨⟨query, reply⟩, occurs, same⟩ := List.mem_map.mp member
  subst event
  apply copy_operation_identity
  apply profile_prefix (copy_profile fd limit) source (query, some reply)
  simp only [Publication.completed, List.mem_append, List.mem_map, List.mem_singleton]
  exact .inl ⟨(query, reply), occurs, rfl⟩

theorem effect_prefix_length (request : Request) {events : List (Request × Option Reply)}
    (source : Prefix (Filesystem.Program.effect request) events) : events.length ≤ 1 := by
  cases source with
  | empty => simp
  | lost => simp
  | returned request next reply tail rest => cases rest; simp

theorem read_guard_identity (request : Request) (reading : request.op = .read) :
    guardedCall request = Filesystem.Program.effect request := by
  cases request with
  | mk operation first second third left right => cases reading; rfl

theorem read_adapter_empty {request : Request} {before : List (Request × Option Reply)} {observed : Option Reply}
    (source : Prefix (guardedCall request) (before ++ [(request, observed)]))
    (reading : request.op = .read) : before = [] := by
  rw [read_guard_identity request reading] at source
  have bounded := effect_prefix_length request source
  have size : before.length = 0 := by
    simp only [List.length_append, List.length_singleton] at bounded
    omega
  cases before with
  | nil => rfl
  | cons first rest => simp at size

end LeanCage.Host.Kernel.Lowered
