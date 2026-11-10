import PublicationProofs.Source

namespace LeanCage.Host.Publication
open Filesystem

-- §FS-host-boundary.publication: Useful partial ACKs inhabit the actual writer.
theorem useful_partial_write :
    Returns (writeNew 7 "file".toUTF8 "abc".toUTF8)
      [({op := .openAt, first := 7, second := newFileFlags, third := 384, left := "file".toUTF8}, (8, .empty)),
       ({op := .write, first := 8, left := "abc".toUTF8}, (1, .empty)),
       ({op := .write, first := 8, left := "bc".toUTF8}, (2, .empty)),
       ({op := .close, first := 8}, (0, .empty))] (.ok ()) := by
  apply Returns.call
  apply Returns.call
  apply Returns.call
  apply Returns.call
  exact .pure _

-- §FS-host-boundary.publication: A lost write remains a real unfinished source prefix.
theorem useful_lost_write :
    Prefix (writeNew 7 "file".toUTF8 "abc".toUTF8)
      [({op := .openAt, first := 7, second := newFileFlags, third := 384, left := "file".toUTF8}, some (8, .empty)),
       ({op := .write, first := 8, left := "abc".toUTF8}, none)] := by
  apply Prefix.returned
  exact .lost _ _

end LeanCage.Host.Publication
