import LeanCageHost.Image
import PublicationProofs

namespace LeanCage.Host.Image
open Filesystem

def ImageWrite (fd : UInt64) (request : Request) : Prop :=
  request.op = .write ∧ request.first = fd ∧ 1 ≤ request.left.size ∧ request.left.size ≤ chunkMax

inductive WriteProgram {α : Type} (fd : UInt64) : Filesystem.Program α → Prop where
  | pure (value : α) : WriteProgram fd (.pure value)
  | call {request : Request} {next : Reply → Filesystem.Program α}
      (allowed : ImageWrite fd request) (tail : ∀ reply, WriteProgram fd (next reply)) :
      WriteProgram fd (.call request next)

theorem write_bind {α β : Type} {fd : UInt64} {program : Filesystem.Program α}
    {next : α → Filesystem.Program β} (first : WriteProgram fd program)
    (tail : ∀ value, WriteProgram fd (next value)) : WriteProgram fd (program.bind next) := by
  induction first with
  | pure => exact tail _
  | call allowed rest ih => exact .call allowed ih

theorem writeLoop_scoped (fuel : Nat) (fd : UInt64) (bytes : ByteArray) (offset : Nat) :
    WriteProgram fd (writeLoop fuel fd bytes offset) := by
  induction fuel generalizing offset with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold writeLoop
    split
    · exact .pure _
    · apply WriteProgram.call
      · exact ⟨rfl, rfl, Publication.write_part_bounds _ _ (by omega)⟩
      · intro reply
        split
        · exact .pure _
        · split
          · exact .pure _
          · exact ih _

theorem writeEntries_scoped (inode : Nat) (fd : UInt64) (overlay : List Entry) :
    WriteProgram fd (writeEntries inode fd overlay) := by
  induction overlay generalizing inode with
  | nil => exact .pure _
  | cons entry rest ih =>
    unfold writeEntries
    apply write_bind (writeLoop_scoped _ _ _ _)
    intro headerResult
    cases headerResult with
    | error => exact .pure _
    | ok =>
      apply write_bind (writeLoop_scoped _ _ _ _)
      intro dataResult
      cases dataResult with
      | error => exact .pure _
      | ok =>
        apply write_bind (writeLoop_scoped _ _ _ _)
        intro padResult
        cases padResult with
        | error => exact .pure _
        | ok => exact ih _

theorem content_scoped (fd : UInt64) (base : ByteArray) (overlay : List Entry) :
    WriteProgram fd (content fd base overlay) := by
  unfold content
  apply write_bind (writeLoop_scoped _ _ _ _)
  intro written
  cases written with
  | error => exact .pure _
  | ok =>
    apply write_bind (writeLoop_scoped _ _ _ _)
    intro padded
    cases padded with
    | error => exact .pure _
    | ok => exact writeEntries_scoped _ _ _

theorem write_prefix {α : Type} {fd : UInt64} {program : Filesystem.Program α}
    {events : List (Request × Option Reply)} (verified : WriteProgram fd program) (run : Prefix program events) :
    ∀ event ∈ events, ImageWrite fd event.1 := by
  induction run with
  | empty => simp
  | lost request next => cases verified with | call allowed => simpa using allowed
  | returned request next reply events run ih =>
    cases verified with
    | call allowed tail =>
      intro event member
      rcases List.mem_cons.mp member with rfl | member
      · exact allowed
      · exact ih (tail reply) event member

-- §FS-host-boundary.ownership: Every archive prefix writes only its retained output descriptor.
theorem content_write_prefix (fd : UInt64) (base : ByteArray) (overlay : List Entry)
    {events : List (Request × Option Reply)} (run : Prefix (content fd base overlay) events) :
    ∀ event ∈ events, ImageWrite fd event.1 := write_prefix (content_scoped _ _ _) run

inductive ArchiveWrites (fd : UInt64) : Nat → List Entry → List (Request × Reply) → Prop where
  | empty (inode : Nat) : ArchiveWrites fd inode [] []
  | next (inode : Nat) (entry : Entry) (rest : List Entry)
      (headers data padding following : List (Request × Reply))
      (headerBytes : Publication.AcknowledgedWrites fd (header inode entry) 0 headers)
      (dataBytes : Publication.AcknowledgedWrites fd entry.bytes 0 data)
      (paddingBytes : Publication.AcknowledgedWrites fd (pad4 entry.bytes.size) 0 padding)
      (tail : ArchiveWrites fd (inode + 1) rest following) :
      ArchiveWrites fd inode (entry :: rest) (headers ++ data ++ padding ++ following)

theorem writeEntries_source (inode : Nat) (fd : UInt64) (overlay : List Entry)
    {events : List (Request × Reply)} (run : Returns (writeEntries inode fd overlay) events (.ok ())) :
    ArchiveWrites fd inode overlay events := by
  induction overlay generalizing inode events with
  | nil => cases run; exact .empty _
  | cons entry rest ih =>
    unfold writeEntries at run
    obtain ⟨headers, result, later, headerRun, afterHeader, shape⟩ := Snapshot.returns_bind_split _ _ run
    cases result with
    | error => cases afterHeader
    | ok headerUnit =>
      cases headerUnit
      obtain ⟨data, result, restEvents, dataRun, afterData, dataShape⟩ := Snapshot.returns_bind_split _ _ afterHeader
      cases result with
      | error => cases afterData
      | ok dataUnit =>
        cases dataUnit
        obtain ⟨padding, result, following, padRun, final, padShape⟩ := Snapshot.returns_bind_split _ _ afterData
        cases result with
        | error => cases final
        | ok paddedUnit =>
          cases paddedUnit
          have observed := ArchiveWrites.next inode entry rest headers data padding following
            (Publication.writeLoop_source _ _ _ _ (Nat.zero_le _) headerRun)
            (Publication.writeLoop_source _ _ _ _ (Nat.zero_le _) dataRun)
            (Publication.writeLoop_source _ _ _ _ (Nat.zero_le _) padRun) (ih _ final)
          simpa only [shape, dataShape, padShape, List.append_assoc] using observed

def ContentObservation (fd : UInt64) (base : ByteArray) (overlay : List Entry)
    (events : List (Request × Reply)) : Prop :=
  ∃ baseWrites padding overlayWrites,
    events = baseWrites ++ padding ++ overlayWrites ∧
    Publication.AcknowledgedWrites fd base 0 baseWrites ∧
    Publication.AcknowledgedWrites fd (pad4 base.size) 0 padding ∧
    ArchiveWrites fd 1 (overlay ++ [⟨"TRAILER!!!", 0, .empty⟩]) overlayWrites

-- §FS-host-boundary.snapshot: Archive writes preserve base/header/data/padding order.
theorem content_source (fd : UInt64) (base : ByteArray) (overlay : List Entry)
    {events : List (Request × Reply)} (run : Returns (content fd base overlay) events (.ok ())) :
    ContentObservation fd base overlay events := by
  unfold content at run
  obtain ⟨baseWrites, result, rest, baseRun, afterBase, shape⟩ := Snapshot.returns_bind_split _ _ run
  cases result with
  | error => cases afterBase
  | ok baseUnit =>
    obtain ⟨padding, result, overlayWrites, padded, final, padShape⟩ := Snapshot.returns_bind_split _ _ afterBase
    cases result with
    | error => cases final
    | ok padUnit =>
      exact ⟨baseWrites, padding, overlayWrites,
        by simpa only [padShape, List.append_assoc] using shape,
        Publication.writeLoop_source _ _ _ _ (Nat.zero_le _) baseRun,
        Publication.writeLoop_source _ _ _ _ (Nat.zero_le _) padded, writeEntries_source _ _ _ final⟩

end LeanCage.Host.Image
