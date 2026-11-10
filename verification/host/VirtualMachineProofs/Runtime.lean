import ProgramProofs
import LeanCageHost.VirtualMachine
import TransportProofs

namespace LeanCage.Host.VirtualMachine
open Filesystem

-- §AR-host-boundary.interfaces: Read observations retain the actual requested FD, size and reply.
inductive ReadOrigin (fd : UInt64) : Transport.Event → Program.Event → Prop where
  | data (amount : Nat) (reply : Reply)
      (positive : 0 < amount) (bounded : amount ≤ chunkMax)
      (native : nativeError reply = false) (count : reply.1.toNat = reply.2.size)
      (size : reply.2.size ≤ amount) (nonempty : reply.2.isEmpty = false) :
      ReadOrigin fd (.data reply.2)
        (.returned (.filesystem { op := .read, first := fd, second := amount.toUInt64 }) reply)
  | eof (amount : Nat) (reply : Reply)
      (positive : 0 < amount) (bounded : amount ≤ chunkMax)
      (native : nativeError reply = false) (count : reply.1.toNat = reply.2.size)
      (empty : reply.2.isEmpty = true) :
      ReadOrigin fd .eof
        (.returned (.filesystem { op := .read, first := fd, second := amount.toUInt64 }) reply)

-- §FS-host-boundary.transport: A decoded chunk is the whole actual successful native read reply.
theorem runtime_read_data (fd : UInt64) (amount : Nat) {events : List Program.Event}
    {bytes : ByteArray} (run : Program.Returns (Runtime.read fd amount) events (.ok (.data bytes))) :
    ∃ observation, events = [observation] ∧ ReadOrigin fd (.data bytes) observation ∧
      0 < bytes.size ∧ bytes.size ≤ amount ∧ amount ≤ chunkMax := by
  unfold Runtime.read at run
  split at run
  · cases run
  · rename_i budget
    have checkedBudget : amount ≠ 0 ∧ amount ≤ chunkMax := by simpa using budget
    have budget : 0 < amount ∧ amount ≤ chunkMax := ⟨by omega, checkedBudget.2⟩
    dsimp only [Runtime.perform, Program.liftFilesystem, Filesystem.Program.effect, Program.bind] at run
    cases run with
    | call _ _ reply tail _ rest =>
      dsimp only [Program.bind] at rest
      split at rest
      · split at rest <;> cases rest
      · rename_i native
        split at rest
        · cases rest
        · rename_i checked
          have checked : reply.1.toNat = reply.2.size ∧ reply.2.size ≤ amount := by simpa using checked
          split at rest
          · cases rest
          · rename_i nonempty
            obtain ⟨rfl, equal⟩ := Program.returns_pure _ rest
            cases equal
            refine ⟨_, rfl, .data amount reply budget.1 budget.2 ?_ checked.1 checked.2 ?_, ?_,
              checked.2, budget.2⟩
            · simpa using native
            · simpa using nonempty
            · have : reply.2.isEmpty = false := by simpa using nonempty
              have nonzero : reply.2.size ≠ 0 := by
                intro zero
                simp [ByteArray.isEmpty, zero] at this
              omega

theorem runtime_read_eof (fd : UInt64) (amount : Nat) {events : List Program.Event}
    (run : Program.Returns (Runtime.read fd amount) events (.ok .eof)) :
    ∃ observation, events = [observation] ∧ ReadOrigin fd .eof observation := by
  unfold Runtime.read at run
  split at run
  · cases run
  · rename_i budget
    have checkedBudget : amount ≠ 0 ∧ amount ≤ chunkMax := by simpa using budget
    have budget : 0 < amount ∧ amount ≤ chunkMax := ⟨by omega, checkedBudget.2⟩
    dsimp only [Runtime.perform, Program.liftFilesystem, Filesystem.Program.effect, Program.bind] at run
    cases run with
    | call _ _ reply tail _ rest =>
      dsimp only [Program.bind] at rest
      split at rest
      · split at rest <;> cases rest
      · rename_i native
        split at rest
        · cases rest
        · rename_i checked
          have checked : reply.1.toNat = reply.2.size ∧ reply.2.size ≤ amount := by simpa using checked
          split at rest
          · rename_i empty
            obtain ⟨rfl, equal⟩ := Program.returns_pure _ rest
            cases equal
            exact ⟨_, rfl, .eof amount reply budget.1 budget.2 (by simpa using native) checked.1 empty⟩
          · cases rest

-- §FS-host-boundary.transport: Selected observations form a subsequence of the actual effect
-- history.
inductive ReadSubsequence (connection : Option UInt64) :
    List Program.Event → List Transport.Event → Prop where
  | nil : ReadSubsequence connection [] []
  | skip (event : Program.Event) {events stream}
      (rest : ReadSubsequence connection events stream) :
      ReadSubsequence connection (event :: events) stream
  | read {fd observation frame events stream}
      (selected : connection = some fd) (origin : ReadOrigin fd frame observation)
      (rest : ReadSubsequence connection events stream) :
      ReadSubsequence connection (observation :: events) (frame :: stream)

theorem read_subsequence_append {connection : Option UInt64} {first last : List Program.Event}
    {before after : List Transport.Event} (left : ReadSubsequence connection first before)
    (right : ReadSubsequence connection last after) :
    ReadSubsequence connection (first ++ last) (before ++ after) := by
  induction left with
  | nil => exact right
  | skip event rest ih => exact .skip event ih
  | read selected origin rest ih => exact .read selected origin ih

theorem read_subsequence_empty (connection : Option UInt64) (events : List Program.Event) :
    ReadSubsequence connection events [] := by
  induction events with
  | nil => exact .nil
  | cons event rest ih => exact .skip event ih

theorem read_subsequence_mono {before after : Option UInt64}
    (growth : ∀ fd, before = some fd → after = some fd) {events stream}
    (origin : ReadSubsequence before events stream) : ReadSubsequence after events stream := by
  induction origin with
  | nil => exact .nil
  | skip event rest ih => exact .skip event ih
  | read selected origin rest ih => exact .read (growth _ selected) origin ih

def StreamSource (initial final : Transport.State) (connection : Option UInt64)
    (events : List Program.Event) : Prop :=
  ∃ stream, final = initial.run stream ∧ ReadSubsequence connection events stream

theorem stream_source_refl (state : Transport.State) (connection : Option UInt64)
    (events : List Program.Event) : StreamSource state state connection events :=
  ⟨[], rfl, read_subsequence_empty connection events⟩

theorem stream_source_append {first middle final : Transport.State} {connection : Option UInt64}
    {before after : List Program.Event} (left : StreamSource first middle connection before)
    (right : StreamSource middle final connection after) :
    StreamSource first final connection (before ++ after) := by
  obtain ⟨earlier, initial, source⟩ := left
  obtain ⟨suffix, ending, rest⟩ := right
  refine ⟨earlier ++ suffix, ?_, read_subsequence_append source rest⟩
  simpa only [Transport.State.run, List.foldl_append] using ending.trans (congrArg (fun state =>
    state.run suffix) initial)

end LeanCage.Host.VirtualMachine
