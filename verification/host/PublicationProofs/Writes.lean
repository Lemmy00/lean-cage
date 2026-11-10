import PublicationProofs.Effects

namespace LeanCage.Host.Publication

open Filesystem

inductive AcknowledgedWrites (fd : UInt64) (bytes : ByteArray) :
    Nat → List (Request × Reply) → Prop where
  | done : AcknowledgedWrites fd bytes bytes.size []
  | more (offset : Nat) (reply : Reply) (events : List (Request × Reply))
      (inside : offset < bytes.size) (native : nativeError reply = false)
      (empty : reply.2 = .empty) (positive : 0 < reply.1.toNat)
      (bounded : reply.1.toNat ≤ (bytes.extract offset (min bytes.size (offset + chunkMax))).size)
      (tail : AcknowledgedWrites fd bytes (offset + reply.1.toNat) events) :
      AcknowledgedWrites fd bytes offset
        (({
          op := .write
          first := fd
          left := bytes.extract offset (min bytes.size (offset + chunkMax)) }, reply) :: events)

-- §FS-host-boundary.publication: Successful writes advance only by actual acknowledged counts.
theorem writeLoop_source (fuel : Nat) (fd : UInt64) (bytes : ByteArray) (offset : Nat)
    (within : offset ≤ bytes.size) {events : List (Request × Reply)}
    (run : Returns (writeLoop fuel fd bytes offset) events (.ok ())) :
    AcknowledgedWrites fd bytes offset events := by
  induction fuel generalizing offset events with
  | zero => cases run
  | succ fuel ih =>
    unfold writeLoop at run
    split at run
    · rename_i finished
      obtain ⟨rfl, _⟩ := Snapshot.returns_pure_eq run
      have same : offset = bytes.size := by omega
      subst offset
      exact .done
    · rename_i inside
      obtain ⟨reply, rest, rfl, tail⟩ := Snapshot.returns_call_split run
      split at tail
      · cases tail
      · rename_i native
        split at tail
        · cases tail
        · rename_i valid
          have fields : reply.2.isEmpty = true ∧ reply.1 ≠ 0 ∧
              reply.1.toNat ≤ (bytes.extract offset (min bytes.size (offset + chunkMax))).size := by
            simpa [Bool.or_eq_true, and_assoc] using valid
          have empty : reply.2 = .empty := ByteArray.size_eq_zero_iff.mp
            (by simpa only [ByteArray.isEmpty, beq_iff_eq] using fields.1)
          have positive : 0 < reply.1.toNat := by
            have nonzero : reply.1.toNat ≠ 0 := by
              intro zero
              exact fields.2.1 (UInt64.toNat_inj.mp (by simpa using zero))
            omega
          have nextWithin : offset + reply.1.toNat ≤ bytes.size := by
            have bounded := fields.2.2
            rw [ByteArray.size_extract] at bounded
            omega
          exact .more offset reply rest (by omega) (Bool.eq_false_iff.mpr native) empty positive
            fields.2.2 (ih _ nextWithin tail)

def NewFileWrite (parent : UInt64) (name bytes : ByteArray) (mode : UInt64)
    (events : List (Request × Reply)) : Prop :=
  rawPathValid name = true ∧ ∃ fd opened writes closing,
    events = ({
      op := .openAt
      first := parent
      second := newFileFlags
      third := mode
      left := name }, opened) :: (writes ++ closing) ∧
    descriptor opened = some fd ∧ AcknowledgedWrites fd bytes 0 writes ∧
    Returns (closeResult fd (.ok ())) closing (.ok ())

-- §FS-host-boundary.publication: Acknowledged file data uses the same exclusive-open descriptor.
theorem writeNew_source (parent : UInt64) (name bytes : ByteArray) (mode : UInt64)
    {events : List (Request × Reply)}
    (run : Returns (writeNew parent name bytes mode) events (.ok ())) :
    NewFileWrite parent name bytes mode events := by
  unfold writeNew at run
  split at run
  · cases run
  · rename_i checked
    obtain ⟨opened, rest, rfl, tail⟩ := Snapshot.returns_call_split run
    split at tail
    · cases tail
    · rename_i fd recognized
      obtain ⟨writes, result, closing, writeRun, closeRun, shape⟩ := Snapshot.returns_bind_split _ _ tail
      have same := (Snapshot.closeResult_provenance _ _ closeRun).1
      cases same
      exact ⟨by simpa using checked, fd, opened, writes, closing, by simp only [shape], recognized,
        writeLoop_source _ _ _ _ (Nat.zero_le _) writeRun, closeRun⟩

end LeanCage.Host.Publication
