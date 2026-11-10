import ImageProofs.Source
import RunDirectoryProofs.Requests

namespace LeanCage.Host.Image
open Filesystem

theorem copyIdentified_readOnly (bundle : Validation.Bundle) (name : String) (limit : Nat) :
    Retrieval.ReadOnly (Validation.copyIdentified bundle name limit) := by
  unfold Validation.copyIdentified
  split
  · split
    · apply Retrieval.readOnly_bind
      · unfold readBounded
        exact Retrieval.readOnly_bind (Retrieval.readOnly_snapshot (Snapshot.copyAt_input _ _ _)) (fun _ => .pure _)
      · intro readResult
        cases readResult with
        | error => exact .pure _
        | ok bytes =>
          apply Retrieval.readOnly_bind (Retrieval.readOnly_snapshot (Snapshot.hash_input _))
          intro hashed
          cases hashed with
          | error => exact .pure _
          | ok value => dsimp only; split <;> exact .pure _
    · exact .pure _
  · exact .pure _

def HasWrite (events : List (Request × Option Reply)) : Prop := ∃ event ∈ events, event.1.op = .write

private theorem readOnly_returns {α : Type} {program : Filesystem.Program α}
    {events : List (Request × Reply)} {value : α} (safe : Retrieval.ReadOnly program)
    (run : Returns program events value) : ∀ event ∈ events, Retrieval.Allowed event.1 := by
  induction run with
  | pure => simp
  | call request next reply tail value run ih =>
    cases safe with
    | call allowed following =>
      intro event member
      rcases List.mem_cons.mp member with rfl | member
      · exact allowed
      · exact ih (following reply) event member

private theorem pure_no_write {α : Type} {value : α} {events : List (Request × Option Reply)}
    (run : Prefix (.pure value) events) (written : HasWrite events) : False := by
  have empty := Snapshot.prefix_pure_empty run
  subst events
  obtain ⟨_, member, _⟩ := written
  cases member

private theorem readOnly_bind_reaches_write {α β : Type} {program : Filesystem.Program α}
    {next : α → Filesystem.Program β} {events : List (Request × Option Reply)}
    (safe : Retrieval.ReadOnly program) (run : Prefix (program.bind next) events) (written : HasWrite events) :
    ∃ first value last, Returns program first value ∧ Prefix (next value) last ∧
      events = Publication.completed first ++ last ∧ HasWrite last := by
  rcases Publication.prefix_bind_split _ _ run with before | after
  · obtain ⟨event, member, writes⟩ := written
    have allowed := Retrieval.readOnly_prefix safe before event member
    simp only [Retrieval.Allowed, writes] at allowed
  · obtain ⟨first, value, last, returned, following, shape⟩ := after
    refine ⟨first, value, last, returned, following, shape, ?_⟩
    obtain ⟨event, member, writes⟩ := written
    rw [shape] at member
    rcases List.mem_append.mp member with before | after
    · obtain ⟨original, present, rfl⟩ := List.mem_map.mp before
      have allowed := readOnly_returns safe returned original present
      change original.1.op = .write at writes
      simp only [Retrieval.Allowed, writes] at allowed
    · exact ⟨event, after, writes⟩

def WriteOrClose (fd : UInt64) (request : Request) : Prop :=
  ImageWrite fd request ∨ request = {op := .close, first := fd}

private theorem write_requests {α : Type} {fd : UInt64} {program : Filesystem.Program α}
    (verified : WriteProgram fd program) : RequestProgram (WriteOrClose fd) program := by
  induction verified with
  | pure => exact .pure _
  | call permitted following ih => exact .call (.inl permitted) ih

theorem contentClose_requests (fd : UInt64) (base : ByteArray) (overlay : List Entry) :
    RequestProgram (WriteOrClose fd) ((content fd base overlay).bind (closeResult fd)) := by
  apply request_bind (write_requests (content_scoped _ _ _))
  intro result
  apply RequestProgram.call (by exact .inr rfl)
  intro reply
  cases result with
  | error => exact .pure _
  | ok => dsimp only; split <;> exact .pure _

def OutputPrefix (runFd : UInt64) (bundle : Validation.Bundle) (overlay : List Entry)
    (events : List (Request × Option Reply)) : Prop :=
  overlayValid overlay = true ∧ ∃ base fd copied opened following,
    events = Publication.completed copied ++ ({
      op := .openAt
      first := runFd
      second := newFileFlags
      third := 384
      left := "request.cpio".toUTF8 }, some opened) :: following ∧
    BaseObservation bundle copied base ∧ descriptor opened = some fd ∧
    Prefix ((content fd base overlay).bind (closeResult fd)) following ∧
    ∀ event ∈ following, WriteOrClose fd event.1

-- §FS-host-boundary.ownership: Every write follows the same checked copy and exclusive open.
theorem create_write_prefix (runFd : UInt64) (bundle : Validation.Bundle) (overlay : List Entry)
    {events : List (Request × Option Reply)} (run : Prefix (create runFd bundle overlay) events)
    (written : HasWrite events) : OutputPrefix runFd bundle overlay events := by
  unfold create at run
  split at run
  · exact False.elim (pure_no_write run written)
  · rename_i bounded
    obtain ⟨copied, result, rest, copiedRun, afterCopy, shape, inCopy⟩ :=
      readOnly_bind_reaches_write (copyIdentified_readOnly _ _ _) run written
    cases result with
    | error => exact False.elim (pure_no_write afterCopy inCopy)
    | ok base =>
      change Prefix (.call _ _) rest at afterCopy
      cases afterCopy with
      | empty => obtain ⟨_, member, _⟩ := inCopy; cases member
      | lost =>
        obtain ⟨event, member, wrote⟩ := inCopy
        simp only [List.mem_singleton] at member
        cases member
        cases wrote
      | returned request next opened following tail =>
        dsimp only [Filesystem.Program.bind] at tail
        split at tail
        · obtain ⟨event, member, wrote⟩ := inCopy
          rcases List.mem_cons.mp member with rfl | member
          · cases wrote
          · exact False.elim (pure_no_write tail ⟨event, member, wrote⟩)
        · rename_i fd recognized
          exact ⟨by simpa using bounded, base, fd, copied, opened, following, shape,
            base_source _ copiedRun, recognized, tail, request_prefix (contentClose_requests _ _ _) tail⟩

end LeanCage.Host.Image
