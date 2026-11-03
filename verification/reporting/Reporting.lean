-- §AR-reporting.interface: The live decoder consumes the checked whole-call observation.
import Normalized

namespace LeanCage.Reporting
open LeanCageM3 LeanCageM4.Normalized

structure Frame where
  badHeader : Bool
  entry : Nat
  cleanup : Nat
  fields : Entry → Result

def FrameView (bytes : ByteArray) (frame : Frame) : Prop :=
  headerBadBytes bytes = frame.badHeader ∧
  littleBytes bytes 40 4 = frame.entry ∧
  littleBytes bytes 44 4 = frame.cleanup ∧
  fieldsBytes bytes = frame.fields

def parseWords (header : Bool) (entry cleanup : Nat) (fields : Entry → Result) :
    Except ErrorCode Result := do
  if header then throw ErrorCode.header
  let tag ← match entry with
    | 0 => pure Entry.no
    | 1 => pure Entry.yes
    | 2 => pure Entry.unknown
    | _ => throw ErrorCode.entry
  if cleanup > 1 then throw ErrorCode.cleanup
  return fields tag

def decodeFrame (frame : Frame) : Except ErrorCode Result :=
  (parseWords frame.badHeader frame.entry frame.cleanup frame.fields).bind validate

theorem parse_words_exact (bytes : ByteArray) :
    parse bytes = parseWords (headerBadBytes bytes) (littleBytes bytes 40 4)
      (littleBytes bytes 44 4) (fieldsBytes bytes) := rfl

theorem normalized_from_view (bytes : ByteArray) (frame : Frame)
    (view : FrameView bytes frame) : decode bytes = decodeFrame frame := by
  have parsed : parse bytes = parseWords frame.badHeader frame.entry frame.cleanup frame.fields := by
    calc
      parse bytes = parseWords (headerBadBytes bytes) (littleBytes bytes 40 4)
        (littleBytes bytes 44 4) (fieldsBytes bytes) := rfl
      _ = parseWords frame.badHeader frame.entry frame.cleanup frame.fields := by
        rw [view.1, view.2.1, view.2.2.1, view.2.2.2]
  exact congrArg (fun parsed => parsed.bind validate) parsed

theorem live_from_view (bytes : ByteArray) (frame : Frame)
    (view : FrameView bytes frame) :
    decodeResult bytes = restore (decodeFrame frame) := by
  exact (decode_exact bytes).symm.trans (congrArg restore (normalized_from_view bytes frame view))

inductive Status where
  | running | published | failed | lost

def appendBytes (emitted : ByteArray) (rest : List UInt8) : ByteArray :=
  ByteArray.mk (emitted.data.toList ++ rest).toArray

def Call (payload emitted : ByteArray) (rest : List UInt8) (status : Status) : Prop :=
  payload = appendBytes emitted rest ∧ (status = .published → rest = [])

theorem append_tail_empty (bytes : List UInt8) : bytes ++ [] = bytes := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih => exact congrArg (List.cons byte) ih

theorem append_empty (emitted : ByteArray) : appendBytes emitted [] = emitted := by
  unfold appendBytes
  rw [append_tail_empty]

theorem published_bytes (payload emitted : ByteArray) (rest : List UInt8)
    (run : Call payload emitted rest .published) : emitted = payload := by
  have tailEmpty := run.2 rfl
  have same : appendBytes emitted rest = emitted := by
    rw [tailEmpty]
    exact append_empty emitted
  exact (run.1.trans same).symm

theorem normalized_publication (payload emitted : ByteArray) (rest : List UInt8) (frame : Frame)
    (view : FrameView payload frame) (run : Call payload emitted rest .published) :
    decode emitted = decodeFrame frame := by
  exact (congrArg decode (published_bytes payload emitted rest run)).trans
    (normalized_from_view payload frame view)

theorem live_publication (payload emitted : ByteArray) (rest : List UInt8) (frame : Frame)
    (view : FrameView payload frame) (run : Call payload emitted rest .published) :
    decodeResult emitted = restore (decodeFrame frame) := by
  exact (congrArg decodeResult (published_bytes payload emitted rest run)).trans
    (live_from_view payload frame view)

end LeanCage.Reporting
