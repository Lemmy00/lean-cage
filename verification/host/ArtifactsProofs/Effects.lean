import LeanCageHost.Artifacts
import SnapshotProofs.Effects

namespace LeanCage.Host.Artifacts

open Filesystem

-- §FS-host-boundary.artifacts: Validation may hash bytes; it never requests filesystem mutation.
inductive HashOnly {α : Type} : Program α → Prop where
  | pure (value : α) : HashOnly (.pure value)
  | call {request : Request} {next : Reply → Program α}
      (hash : request.op = .sha256) (tail : ∀ reply, HashOnly (next reply)) :
      HashOnly (.call request next)

theorem hashOnly_bind {α β : Type} {program : Program α} {next : α → Program β}
    (first : HashOnly program) (tail : ∀ value, HashOnly (next value)) : HashOnly (program.bind next) := by
  induction first with
  | pure value => exact tail value
  | call hash _ ih => exact .call hash ih

theorem hashOnly_hash (bytes : ByteArray) : HashOnly (Filesystem.hash bytes) := by
  unfold Filesystem.hash
  apply HashOnly.call rfl
  intro reply
  split <;> exact .pure _

theorem checkBlobs_hashOnly (limits : Transport.Limits) (sources : List Transport.Blob) (state : BlobState) :
    HashOnly (checkBlobs limits sources state) := by
  induction sources generalizing state with
  | nil => exact .pure _
  | cons source rest ih =>
    unfold checkBlobs
    split
    · exact .pure _
    · split
      · exact .pure _
      · split
        · exact .pure _
        · apply hashOnly_bind (hashOnly_hash source.content)
          intro result
          cases result with
          | error => exact .pure _
          | ok digest =>
            dsimp only
            split
            · split
              · exact .pure _
              · exact ih _
            · exact .pure _

theorem validateExport_hashOnly (limits : Transport.Limits) (raw : ByteArray) (digest : String)
    (omitted : Nat) (sources : List Transport.Blob) : HashOnly (validateExport limits raw digest omitted sources) := by
  unfold validateExport
  split
  · exact .pure _
  · apply hashOnly_bind (hashOnly_hash raw)
    intro result
    cases result with
    | error => exact .pure _
    | ok bytes =>
      dsimp only
      split
      · exact .pure _
      · split
        · exact .pure _
        · split
          · exact .pure _
          · apply hashOnly_bind (checkBlobs_hashOnly _ _ _)
            intro checked
            cases checked with
            | error => exact .pure _
            | ok blobs =>
              dsimp only
              split
              · exact .pure _
              · split <;> exact .pure _

theorem validate_hashOnly (expected : Expected) (received : Transport.Result) : HashOnly (validate expected received) := by
  unfold validate
  split
  · exact .pure _
  · split
    · split
      · apply hashOnly_bind (validateExport_hashOnly _ _ _ _ _)
        intro result
        exact .pure _
      · exact .pure _
    · exact .pure _

theorem hashOnly_prefix {α : Type} {program : Program α} {events : List (Request × Option Reply)}
    (only : HashOnly program) (run : Prefix program events) :
    ∀ event ∈ events, event.1.op = .sha256 := by
  induction run with
  | empty => simp
  | lost request next =>
    cases only with
    | call hash tail => simpa using hash
  | returned request next reply events rest ih =>
    cases only with
    | call hash tail =>
      intro event member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact hash
      · exact ih (tail reply) event member

-- §FS-host-boundary.artifacts: Lost and malicious-reply prefixes also contain no writes.
theorem validate_prefix_no_write (expected : Expected) (received : Transport.Result)
    (events : List (Request × Option Reply)) (run : Prefix (validate expected received) events) :
    ∀ event ∈ events, event.1.op = .sha256 :=
  hashOnly_prefix (validate_hashOnly expected received) run

def HashSeen (events : List (Request × Reply)) (bytes digest : ByteArray) : Prop :=
  ∃ reply, (({ op := .sha256, left := bytes } : Request), reply) ∈ events ∧
    reply.1 = 0 ∧ reply.2 = digest ∧ digest.size = 32

theorem hash_returned (bytes digest : ByteArray) (events : List (Request × Reply))
    (returned : Returns (Filesystem.hash bytes) events (.ok digest)) : HashSeen events bytes digest := by
  unfold Filesystem.hash at returned
  cases returned with
  | call request next reply tail result returned =>
    dsimp only at returned
    split at returned
    · rename_i success
      obtain ⟨rfl, equal⟩ := Snapshot.returns_pure_eq returned
      cases equal
      have fields : reply.1 = 0 ∧ reply.2.size = 32 := by
        simpa only [Bool.and_eq_true, beq_iff_eq] using success
      exact ⟨reply, by simp, fields.1, rfl, fields.2⟩
    · have impossible := (Snapshot.returns_pure_eq returned).2
      cases impossible

theorem hashSeen_append_left (first last : List (Request × Reply)) (bytes digest : ByteArray)
    (seen : HashSeen first bytes digest) : HashSeen (first ++ last) bytes digest := by
  rcases seen with ⟨reply, member, zero, payload, size⟩
  exact ⟨reply, List.mem_append_left last member, zero, payload, size⟩

theorem hashSeen_append_right (first last : List (Request × Reply)) (bytes digest : ByteArray)
    (seen : HashSeen last bytes digest) : HashSeen (first ++ last) bytes digest := by
  rcases seen with ⟨reply, member, zero, payload, size⟩
  exact ⟨reply, List.mem_append_right first member, zero, payload, size⟩

end LeanCage.Host.Artifacts
