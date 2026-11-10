import PositionalReadProofs
import FilesystemRecording

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: ONE bounded pread returns bytes at its explicit
-- offset when that actual read interval has no concurrent content modification.
structure PositionedReadContract (kernel : Contract) (regular : ObjectId → Prop) where
  unmodified : World → Request → World → ObjectId → Prop
  returned : ∀ before after request reply handle (collected suffix : ByteArray),
    kernel.step before request (some reply) after → request.op = .read →
    Snapshot.ReadAcknowledged request reply → request.third.toNat = collected.size + 1 →
    collected.size < 2 ^ 63 → before.handles request.first = some handle → regular handle.object →
    1 ≤ request.second.toNat → unmodified before request after handle.object →
    before.contents handle.object = collected ++ suffix →
    ∃ remaining, suffix = reply.2 ++ remaining ∧ (reply.2 = .empty → remaining = .empty)

-- §FS-host-boundary.caller: Each observation names its actual origin/FD/file and
-- current contents. The global source/installation history must produce these.
def FileReadContentsAt (unmodified : World → Request → World → ObjectId → Prop)
    (origin : FilesystemOrigin) (lower upper : Nat) (object : ObjectId) (contents : ByteArray) : Prop :=
  ∀ ordinal request reply before after,
    lower ≤ ordinal → ordinal < upper → origin ordinal request reply before after → request.op = .read →
    ∃ handle, before.handles request.first = some handle ∧ handle.object = object ∧
      before.contents object = contents ∧ unmodified before request after object

-- §FS-host-boundary.snapshot: Actual positional reads, EOF and the SAME origin
-- reconstruct contents without an OFD-cursor or whole-copy premise.
theorem positional_reads_contents {kernel : Contract} {regular : ObjectId → Prop}
    (reads : PositionedReadContract kernel regular) {origin : FilesystemOrigin}
    {lower upper : Nat} {object : ObjectId} {contents : ByteArray}
    (observed : FileReadContentsAt reads.unmodified origin lower upper object contents)
    (file : regular object) {fd : UInt64} {initial result : ByteArray} {events : List (Request × Reply)}
    (source : Snapshot.PositionalReads fd initial events result) {ordinal : Nat} {before after : World}
    (history : RecordedHistory kernel origin ordinal before events after)
    (interval : lower ≤ ordinal ∧ ordinal + events.length ≤ upper)
    (collected : ∃ suffix, contents = initial ++ suffix) : result = contents := by
  induction source generalizing ordinal before with
  | @eof initial request reply read ack empty =>
    obtain ⟨actual, middle, _, operation, sampled, _⟩ := recorded_history_head history
    obtain ⟨handle, live, same, bytes, stable⟩ := observed _ _ _ _ _ interval.1
      (by simp only [List.length_singleton] at interval; omega) sampled read.reading.1
    obtain ⟨suffix, collected⟩ := collected
    obtain ⟨remaining, tail, finished⟩ := reads.returned actual middle request reply handle initial suffix
      operation read.reading.1 ack read.position read.supported live (same ▸ file)
      read.reading.2.2.1 (by simpa only [same] using stable)
      (by simpa only [same] using bytes.trans collected)
    rw [empty, finished empty, ByteArray.empty_append] at tail
    simpa only [tail, ByteArray.append_empty] using collected.symm
  | @more initial result request reply rest read ack nonempty tail ih =>
    obtain ⟨actual, middle, _, operation, sampled, following⟩ := recorded_history_head history
    obtain ⟨handle, live, same, bytes, stable⟩ := observed _ _ _ _ _ interval.1 (by simp only [List.length_cons] at interval; omega) sampled read.reading.1
    obtain ⟨suffix, collected⟩ := collected
    obtain ⟨remaining, split, _⟩ := reads.returned actual middle request reply handle initial suffix
      operation read.reading.1 ack read.position read.supported live (same ▸ file)
      read.reading.2.2.1 (by simpa only [same] using stable)
      (by simpa only [same] using bytes.trans collected)
    apply ih following (by simp only [List.length_cons] at interval; omega)
    exact ⟨remaining, by simpa only [split, ByteArray.append_assoc] using collected⟩

theorem readLoop_installed_contents {kernel : Contract} {regular : ObjectId → Prop}
    (reads : PositionedReadContract kernel regular) {origin : FilesystemOrigin}
    {lower upper : Nat} {object : ObjectId} {contents : ByteArray}
    (observed : FileReadContentsAt reads.unmodified origin lower upper object contents)
    (file : regular object) (fuel : Nat) (fd : UInt64) (limit : Nat)
    {events : List (Request × Reply)} {bytes : ByteArray} {ordinal : Nat} {before after : World}
    (actual : RecordedRun kernel origin ordinal (readLoop fuel fd limit .empty) before events after (.ok bytes)) :
    lower ≤ ordinal ∧ ordinal + events.length ≤ upper →
    bytes = contents :=
  fun interval => positional_reads_contents reads observed file (Snapshot.readLoop_positions _ _ _ _ actual.1) actual.2
    interval ⟨contents, by simp⟩

-- §FS-host-boundary.caller: The source supplies the actual stat/read/stat split;
-- the byte conclusion consumes that SAME recorded kernel history.
theorem copyOpened_installed_contents {kernel : Contract} {regular : ObjectId → Prop}
    (reads : PositionedReadContract kernel regular) {origin : FilesystemOrigin}
    {object : ObjectId} {contents : ByteArray} (file : regular object)
    (fd : UInt64) (limit : Nat) {events : List (Request × Reply)} {copied : CopiedFile}
    {ordinal : Nat} {before after : World}
    (actual : RecordedRun kernel origin ordinal (copyOpened fd limit) before events after (.ok copied))
    (observed : FileReadContentsAt reads.unmodified origin ordinal (ordinal + events.length) object contents) :
    copied.bytes = contents := by
  obtain ⟨beforeReply, reading, afterReply, shape, positioned⟩ := Snapshot.copyOpened_positions _ _ actual.1
  have history := actual.2
  rw [shape] at history
  obtain ⟨_, middle, _, _, _, following⟩ := recorded_history_head history
  obtain ⟨readAfter, readHistory, _⟩ := recorded_history_split reading _ following
  have bound : ordinal ≤ ordinal + 1 ∧ ordinal + 1 + reading.length ≤ ordinal + events.length := by
    rw [shape]
    simp only [List.length_cons, List.length_append]
    omega
  exact positional_reads_contents reads observed file positioned readHistory bound ⟨contents, by simp⟩

end LeanCage.Host.Kernel
