import SnapshotProofs.Effects

namespace LeanCage.Host.Snapshot

open Filesystem

private theorem read_count_exact (limit count : Nat) :
    (min chunkMax (limit + 1 - count)).toUInt64.toNat = min chunkMax (limit + 1 - count) := by
  have upper := Nat.min_le_left chunkMax (limit + 1 - count)
  have fits : min chunkMax (limit + 1 - count) < 2 ^ 64 := by
    have maximum : chunkMax < 2 ^ 64 := by decide
    omega
  simp only [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt fits]

private theorem actual_read_request (fd : UInt64) (limit count : Nat) (within : count ≤ limit) :
    ReadRequest fd { op := .read, first := fd, second := (min chunkMax (limit + 1 - count)).toUInt64 } := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> rw [read_count_exact]
  · apply Nat.le_min.mpr
    constructor
    · decide
    · omega
  · exact Nat.min_le_left _ _

private theorem read_ack (fd : UInt64) (limit count : Nat) (reply : Reply)
    (native : ¬ nativeError reply = true)
    (checked : ¬ (reply.1.toNat != reply.2.size || reply.2.size > min chunkMax (limit + 1 - count)) = true) :
    ReadAcknowledged { op := .read, first := fd, second := (min chunkMax (limit + 1 - count)).toUInt64 } reply := by
  have fields : reply.1.toNat = reply.2.size ∧ reply.2.size ≤ min chunkMax (limit + 1 - count) := by
    simp only [Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq, not_or, Nat.not_lt] at checked
    exact ⟨Classical.byContradiction checked.1, checked.2⟩
  exact ⟨Bool.eq_false_iff.mpr native, fields.1, by simpa only [read_count_exact] using fields.2⟩

-- §FS-host-boundary.transport: The checked lookahead holds at most one byte beyond the limit.
theorem read_reply_buffer_bound (fd : UInt64) (limit : Nat) (before : ByteArray) (reply : Reply)
    (within : before.size ≤ limit)
    (ack : ReadAcknowledged
      { op := .read, first := fd, second := (min chunkMax (limit + 1 - before.size)).toUInt64 } reply) :
    before.size + reply.2.size ≤ limit + 1 ∧ reply.2.size ≤ chunkMax := by
  have count := ack.2.2
  rw [read_count_exact] at count
  have remaining := Nat.min_le_right chunkMax (limit + 1 - before.size)
  have chunk := Nat.min_le_left chunkMax (limit + 1 - before.size)
  omega

-- §FS-host-boundary.snapshot: Successful copying is exactly acknowledged data and a real EOF reply.
theorem readLoop_provenance (fuel : Nat) (fd : UInt64) (limit : Nat) (initial : ByteArray)
    {events : List (Request × Reply)} {bytes : ByteArray}
    (run : Returns (readLoop fuel fd limit initial) events (.ok bytes)) :
    bytes.size ≤ limit ∧ AcknowledgedReads fd initial events bytes := by
  induction fuel generalizing initial events bytes with
  | zero => cases run
  | succ fuel ih =>
    simp only [readLoop] at run
    split at run
    · cases run
    · rename_i within
      obtain ⟨reply, rest, rfl, tail⟩ := returns_call_split run
      split at tail
      · cases tail
      · rename_i native
        split at tail
        · cases tail
        · rename_i checked
          have read := actual_read_request fd limit initial.size (by omega)
          have ack := read_ack fd limit initial.size reply native checked
          split at tail
          · rename_i empty
            obtain ⟨rfl, value⟩ := returns_pure_eq tail
            cases value
            have emptyBytes : reply.2 = .empty := by
              apply ByteArray.size_eq_zero_iff.mp
              simpa only [ByteArray.isEmpty, beq_iff_eq] using empty
            exact ⟨by omega, .eof read ack emptyBytes⟩
          · rename_i nonempty
            split at tail
            · cases tail
            · obtain ⟨bounded, observed⟩ := ih _ tail
              have nonemptyBytes : reply.2 ≠ .empty := by
                intro empty
                simp [empty, ByteArray.isEmpty] at nonempty
              exact ⟨bounded, .more read ack nonemptyBytes observed⟩

-- §AR-host-boundary.interfaces: Every successful digest refers to this exact hash request.
theorem hash_provenance (bytes : ByteArray) {events : List (Request × Reply)} {digest : ByteArray}
    (run : Returns (Filesystem.hash bytes) events (.ok digest)) :
    ∃ reply, events = [({ op := .sha256, left := bytes }, reply)] ∧
      reply.1 = 0 ∧ reply.2 = digest ∧ digest.size = 32 := by
  obtain ⟨reply, rest, shape, tail⟩ := returns_call_split run
  split at tail
  · rename_i valid
    obtain ⟨rfl, value⟩ := returns_pure_eq tail
    cases value
    simp only [Bool.and_eq_true, beq_iff_eq] at valid
    exact ⟨reply, shape, valid.1, rfl, valid.2⟩
  · cases tail

private theorem stat_beq_iff (first second : Stat) : (first == second) = true ↔ first = second := by
  cases first
  cases second
  simp [instBEqStat.beq, BEq.beq, Stat.mk.injEq]

instance statLawfulBEq : LawfulBEq Stat where
  eq_of_beq := fun same => stat_beq_iff _ _ |>.mp same
  rfl := (stat_beq_iff _ _).mpr rfl

def CopiedObservation (fd : UInt64) (events : List (Request × Reply)) (copied : CopiedFile) : Prop :=
  ∃ beforeReply reads afterReply,
    events = ({ op := .stat, first := fd }, beforeReply) ::
      (reads ++ [({ op := .stat, first := fd }, afterReply)]) ∧
    parseStat beforeReply = some copied.stat ∧ parseStat afterReply = some copied.stat ∧
    copied.stat.regular = true ∧ copied.stat.links = 1 ∧ copied.bytes.size = copied.stat.size ∧
    AcknowledgedReads fd .empty reads copied.bytes

-- §FS-host-boundary.snapshot: Checked before/after metadata accompanies the same copied byte trace.
theorem copyOpened_provenance (fd : UInt64) (limit : Nat)
    {events : List (Request × Reply)} {copied : CopiedFile}
    (run : Returns (copyOpened fd limit) events (.ok copied)) :
    copied.bytes.size ≤ limit ∧ CopiedObservation fd events copied := by
  unfold copyOpened at run
  obtain ⟨initialReply, tail, rfl, initial⟩ := returns_call_split run
  split at initial
  · cases initial
  · rename_i before beforeStat
    split at initial
    · cases initial
    · rename_i beforeValid
      obtain ⟨reads, result, last, readRun, rest, shape⟩ := returns_bind_split _ _ initial
      cases result with
      | error error => cases rest
      | ok bytes =>
        obtain ⟨finalReply, finalTail, finalShape, finished⟩ := returns_call_split rest
        split at finished
        · cases finished
        · rename_i after afterStat
          split at finished
          · cases finished
          · rename_i finalValid
            obtain ⟨rfl, accepted⟩ := returns_pure_eq finished
            cases accepted
            have finalProperties : after = before ∧ bytes.size = before.size := by
              simpa [Bool.or_eq_true] using finalValid
            have initialProperties : before.regular = true ∧ before.links = 1 ∧ before.size ≤ limit := by
              simpa [Bool.or_eq_true, and_assoc] using beforeValid
            obtain ⟨bounded, acknowledged⟩ := readLoop_provenance _ _ _ _ readRun
            refine ⟨bounded, initialReply, reads, finalReply, ?_, beforeStat, ?_,
              initialProperties.1, initialProperties.2.1, finalProperties.2, acknowledged⟩
            · simpa only [finalShape, List.append_assoc] using congrArg (fun events =>
                ({ op := .stat, first := fd }, initialReply) :: events) shape
            · simpa only [finalProperties.1] using afterStat

theorem closeResult_provenance {α : Type} (fd : UInt64) (input : Result α)
    {events : List (Request × Reply)} {value : α}
    (run : Returns (closeResult fd input) events (.ok value)) :
    input = .ok value ∧ ∃ reply, events = [({ op := .close, first := fd }, reply)] ∧
      reply.1 = 0 ∧ reply.2 = .empty := by
  obtain ⟨reply, rest, shape, tail⟩ := returns_call_split run
  cases input with
  | error error => cases tail
  | ok initial =>
    dsimp only at tail
    split at tail
    · rename_i accepted
      obtain ⟨rfl, same⟩ := returns_pure_eq tail
      cases same
      simp only [Bool.and_eq_true, beq_iff_eq] at accepted
      refine ⟨rfl, reply, shape, accepted.1, ?_⟩
      apply ByteArray.size_eq_zero_iff.mp
      simpa only [ByteArray.isEmpty, beq_iff_eq] using accepted.2
    · cases tail

def OpenedCopy (parent : UInt64) (path : ByteArray) (events : List (Request × Reply))
    (copied : CopiedFile) : Prop :=
  ∃ fd opened middle closed,
    events = ({ op := .openAt, first := parent, second := readFlags, left := path }, opened) ::
      (middle ++ [({ op := .close, first := fd }, closed)]) ∧
    descriptor opened = some fd ∧ CopiedObservation fd middle copied ∧
    closed.1 = 0 ∧ closed.2 = .empty

-- §FS-host-boundary.snapshot: Stdin file bytes retain their actual open/read/stat/close lineage.
theorem copyAt_provenance (parent : UInt64) (path : ByteArray) (limit : Nat)
    {events : List (Request × Reply)} {copied : CopiedFile}
    (run : Returns (copyAt parent path limit) events (.ok copied)) :
    copied.bytes.size ≤ limit ∧ OpenedCopy parent path events copied := by
  unfold copyAt at run
  split at run
  · cases run
  · obtain ⟨opened, rest, rfl, tail⟩ := returns_call_split run
    split at tail
    · cases tail
    · rename_i fd owned
      obtain ⟨middle, result, last, first, final, shape⟩ := returns_bind_split _ _ tail
      obtain ⟨same, closed, closeShape, closeValue, closeBytes⟩ := closeResult_provenance _ _ final
      cases same
      obtain ⟨bounded, copiedFrom⟩ := copyOpened_provenance _ _ first
      refine ⟨bounded, fd, opened, middle, closed, ?_, owned, copiedFrom, closeValue, closeBytes⟩
      simpa only [closeShape] using congrArg (fun events =>
        ({ op := .openAt, first := parent, second := readFlags, left := path }, opened) :: events) shape

end LeanCage.Host.Snapshot
