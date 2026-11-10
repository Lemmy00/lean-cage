import FilesystemPositionedContents

namespace LeanCage.Host.Kernel
open Filesystem

structure BoundedReadSource (path : ByteArray) (limit : Nat) (bytes : ByteArray)
    (events : List (Request × Reply)) where
  fd : UInt64
  opened : Reply
  recognized : descriptor opened = some fd
  copying : List (Request × Reply)
  closed : Reply
  copied : CopiedFile
  content : copied.bytes = bytes
  source : Returns (copyOpened fd limit) copying (.ok copied)
  trace : events = ({op := .openAt, first := cwd, second := readFlags, left := path}, opened) ::
    (copying ++ [({op := .close, first := fd}, closed)])

-- §FS-host-boundary.caller: Read provenance begins at the actual open and keeps
-- its complete successful copy and close, rather than trusting readBounded.
theorem bounded_read_source (path : ByteArray) (limit : Nat) {bytes : ByteArray}
    {events : List (Request × Reply)} (source : Returns (readBounded path limit) events (.ok bytes)) :
    Nonempty (BoundedReadSource path limit bytes events) := by
  unfold readBounded at source
  obtain ⟨first, result, last, copy, final, trace⟩ := Snapshot.returns_bind_split _ _ source
  cases result with
  | error => cases final
  | ok copied =>
    obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
    cases same
    simp only [List.append_nil] at trace
    unfold copyAt at copy
    split at copy
    · cases copy
    · obtain ⟨opened, rest, copyTrace, tail⟩ := Snapshot.returns_call_split copy
      split at tail
      · cases tail
      · rename_i fd recognized
        obtain ⟨copying, result, closing, copyingSource, closingSource, tailTrace⟩ :=
          Snapshot.returns_bind_split _ _ tail
        obtain ⟨same, closed, closeTrace, _, _⟩ := Snapshot.closeResult_provenance _ _ closingSource
        cases same
        refine ⟨⟨fd, opened, recognized, copying, closed, copied, rfl, copyingSource, ?_⟩⟩
        rw [trace, copyTrace, tailTrace, closeTrace]

theorem FileReadContentsAt.restrict {unmodified : World → Request → World → ObjectId → Prop}
    {origin : FilesystemOrigin} {lower upper innerLower innerUpper : Nat}
    {object : ObjectId} {contents : ByteArray}
    (observed : FileReadContentsAt unmodified origin lower upper object contents)
    (left : lower ≤ innerLower) (right : innerUpper ≤ upper) :
    FileReadContentsAt unmodified origin innerLower innerUpper object contents := by
  intro ordinal request reply before after first last sampled reading
  exact observed _ _ _ _ _ (by omega) (by omega) sampled reading

theorem bounded_read_installed_contents {kernel : Contract} {regular : ObjectId → Prop}
    (reads : PositionedReadContract kernel regular) {origin : FilesystemOrigin}
    {object : ObjectId} {contents : ByteArray} (file : regular object)
    (path : ByteArray) (limit : Nat) {events : List (Request × Reply)} {bytes : ByteArray}
    {ordinal : Nat} {before after : World}
    (actual : RecordedRun kernel origin ordinal (readBounded path limit) before events after (.ok bytes))
    (observed : FileReadContentsAt reads.unmodified origin ordinal (ordinal + events.length) object contents) :
    bytes = contents := by
  obtain ⟨source⟩ := bounded_read_source path limit actual.1
  have history := actual.2
  rw [source.trace] at history
  obtain ⟨_, middle, _, _, _, following⟩ := recorded_history_head history
  obtain ⟨copyAfter, copying, _⟩ := recorded_history_split source.copying _ following
  have right : ordinal + 1 + source.copying.length ≤ ordinal + events.length := by
    have size := congrArg List.length source.trace
    simp only [List.length_cons, List.length_append] at size
    omega
  have same := copyOpened_installed_contents reads file source.fd limit ⟨source.source, copying⟩
    (observed.restrict (by omega) right)
  exact source.content.symm.trans same

end LeanCage.Host.Kernel
