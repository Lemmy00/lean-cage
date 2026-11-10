import SnapshotProofs.Copy

namespace LeanCage.Host.Snapshot
open Filesystem

-- §FS-host-boundary.snapshot: Offset words are the actual checked, nonwrapped
-- accumulator position plus one; zero belongs to the separate stream ABI.
structure PositionedRead (fd : UInt64) (before : ByteArray) (request : Request) : Prop where
  reading : ReadRequest fd request
  position : request.third.toNat = before.size + 1
  supported : before.size < 2 ^ 63

inductive PositionalReads (fd : UInt64) :
    ByteArray → List (Request × Reply) → ByteArray → Prop where
  | eof {before : ByteArray} {request : Request} {reply : Reply}
      (read : PositionedRead fd before request) (ack : ReadAcknowledged request reply)
      (empty : reply.2 = .empty) : PositionalReads fd before [(request, reply)] before
  | more {before after : ByteArray} {request : Request} {reply : Reply}
      {rest : List (Request × Reply)} (read : PositionedRead fd before request)
      (ack : ReadAcknowledged request reply) (nonempty : reply.2 ≠ .empty)
      (tail : PositionalReads fd (before ++ reply.2) rest after) :
      PositionalReads fd before ((request, reply) :: rest) after

theorem PositionalReads.acknowledged {fd : UInt64} {before after : ByteArray}
    {events : List (Request × Reply)} (reads : PositionalReads fd before events after) :
    AcknowledgedReads fd before events after := by
  induction reads with
  | eof read ack empty => exact .eof read.reading ack empty
  | more read ack nonempty tail ih => exact .more read.reading ack nonempty ih

-- §FS-host-boundary.snapshot: This follows the maintained executable loop,
-- retaining actual replies, partial reads and EOF rather than assuming a copy.
theorem readLoop_positions (fuel : Nat) (fd : UInt64) (limit : Nat) (initial : ByteArray)
    {events : List (Request × Reply)} {bytes : ByteArray}
    (run : Returns (readLoop fuel fd limit initial) events (.ok bytes)) :
    PositionalReads fd initial events bytes := by
  induction fuel generalizing initial events bytes with
  | zero => cases run
  | succ fuel ih =>
    simp only [readLoop] at run
    split at run
    · cases run
    · rename_i within
      have bounds : initial.size ≤ limit ∧ initial.size < 2 ^ 63 := by
        simpa only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt, Nat.not_le] using within
      obtain ⟨reply, rest, rfl, tail⟩ := returns_call_split run
      split at tail
      · cases tail
      · rename_i native
        split at tail
        · cases tail
        · rename_i checked
          have amount : min chunkMax (limit + 1 - initial.size) < 2 ^ 64 := by
            have bound := Nat.min_le_left chunkMax (limit + 1 - initial.size)
            have : chunkMax < 2 ^ 64 := by decide
            omega
          have count : (min chunkMax (limit + 1 - initial.size)).toUInt64.toNat =
              min chunkMax (limit + 1 - initial.size) := by
            simp only [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt amount]
          have offset : (initial.size + 1).toUInt64.toNat = initial.size + 1 := by
            have fits : initial.size + 1 < 2 ^ 64 := by omega
            simp only [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt fits]
          have read : PositionedRead fd initial {
              op := .read, first := fd, second := (min chunkMax (limit + 1 - initial.size)).toUInt64,
              third := (initial.size + 1).toUInt64 } := by
            refine ⟨⟨rfl, rfl, ?_, ?_⟩, offset, bounds.2⟩ <;> rw [count]
            · apply Nat.le_min.mpr
              constructor
              · decide
              · omega
            · exact Nat.min_le_left _ _
          have fields : reply.1.toNat = reply.2.size ∧ reply.2.size ≤ min chunkMax (limit + 1 - initial.size) := by
            simp only [Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq, not_or, Nat.not_lt] at checked
            exact ⟨Classical.byContradiction checked.1, checked.2⟩
          have ack : ReadAcknowledged {
              op := .read, first := fd, second := (min chunkMax (limit + 1 - initial.size)).toUInt64,
              third := (initial.size + 1).toUInt64 } reply :=
            ⟨Bool.eq_false_iff.mpr native, fields.1, by simpa only [count] using fields.2⟩
          split at tail
          · rename_i empty
            obtain ⟨rfl, same⟩ := returns_pure_eq tail
            cases same
            apply PositionalReads.eof read ack
            apply ByteArray.size_eq_zero_iff.mp
            simpa only [ByteArray.isEmpty, beq_iff_eq] using empty
          · rename_i nonempty
            split at tail
            · cases tail
            · apply PositionalReads.more read ack ?_ (ih _ tail)
              intro empty
              simp [empty, ByteArray.isEmpty] at nonempty

theorem copyOpened_positions (fd : UInt64) (limit : Nat)
    {events : List (Request × Reply)} {copied : CopiedFile}
    (source : Returns (copyOpened fd limit) events (.ok copied)) :
    ∃ beforeReply reads afterReply,
      events = ({op := .stat, first := fd}, beforeReply) ::
        (reads ++ [({op := .stat, first := fd}, afterReply)]) ∧
      PositionalReads fd .empty reads copied.bytes := by
  unfold copyOpened at source
  obtain ⟨initialReply, tail, rfl, initial⟩ := returns_call_split source
  split at initial
  · cases initial
  · split at initial
    · cases initial
    · obtain ⟨reads, result, last, readRun, rest, shape⟩ := returns_bind_split _ _ initial
      cases result with
      | error => cases rest
      | ok bytes =>
        obtain ⟨finalReply, finalTail, finalShape, finished⟩ := returns_call_split rest
        split at finished
        · cases finished
        · split at finished
          · cases finished
          · obtain ⟨rfl, accepted⟩ := returns_pure_eq finished
            cases accepted
            refine ⟨initialReply, reads, finalReply, ?_, readLoop_positions _ _ _ _ readRun⟩
            simpa only [finalShape, List.append_assoc] using congrArg
              (fun events => ({op := .stat, first := fd}, initialReply) :: events) shape

end LeanCage.Host.Snapshot
