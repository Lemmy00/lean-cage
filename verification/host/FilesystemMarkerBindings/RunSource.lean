import FilesystemMarkerBindings.Publication

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.interfaces: This is the exact executable continuation after private marking.
def runAfterMark (container : Directories.Opened) (areaPath : String)
    (child : Directories.NewDirectory) (marked : Reply) : Filesystem.Program (Result RunDirectory.Owned) := do
  if marked.1 != 0 || !marked.2.isEmpty then do
    let _ ← Filesystem.Program.effect { op := .close, first := child.directory.fd }
    let _ ← Filesystem.Program.effect {
      op := .unlinkAt, first := container.fd, second := 512, left := child.name }
    return ← closeResult container.fd (.error "private run marker failed")
  match String.fromUTF8? child.name with
  | none => do
    let _ ← Filesystem.Program.effect { op := .close, first := child.directory.fd }
    closeResult container.fd (.error "invalid private run name")
  | some name =>
    let path := areaPath ++ "/" ++ name
    if path.toUTF8.size + "/control.sock".toUTF8.size > 107 then do
      let _ ← Filesystem.Program.effect { op := .close, first := child.directory.fd }
      closeResult container.fd (.error "private run socket name exceeds its bound")
    else return .ok ⟨path, child.directory, container, child.name⟩

theorem run_after_mark_no_attribute (container : Directories.Opened) (areaPath : String)
    (child : Directories.NewDirectory) (marked : Reply) :
    RequestProgram Publication.NoAttribute (runAfterMark container areaPath child marked) := by
  unfold runAfterMark
  split
  · apply RequestProgram.call (by change Op.close ≠ Op.setAttribute; decide)
    intro ignored
    dsimp only [Bind.bind, Pure.pure, Filesystem.Program.bind]
    apply RequestProgram.call (by change Op.unlinkAt ≠ Op.setAttribute; decide)
    intro ignored
    dsimp only [Bind.bind, Pure.pure, Filesystem.Program.bind]
    exact Publication.readOnly_no_attribute (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
  · split
    · apply RequestProgram.call (by change Op.close ≠ Op.setAttribute; decide)
      intro ignored
      dsimp only [Bind.bind, Pure.pure, Filesystem.Program.bind]
      exact Publication.readOnly_no_attribute (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
    · dsimp only
      split
      · apply RequestProgram.call (by change Op.close ≠ Op.setAttribute; decide)
        intro ignored
        dsimp only [Bind.bind, Pure.pure, Filesystem.Program.bind]
        exact Publication.readOnly_no_attribute (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
      · exact .pure _

private theorem no_attribute_last {α : Type} {program : Filesystem.Program α}
    (profile : RequestProgram Publication.NoAttribute program)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (active : Prefix program (before ++ [(request, observed)])) (setting : request.op = .setAttribute) : False :=
  request_prefix profile active (request, observed) (by simp) setting

private theorem attribute_call_last {α : Type} (request : Request) (next : Reply → Filesystem.Program α)
    (profile : ∀ reply, RequestProgram Publication.NoAttribute (next reply))
    {before : List (Request × Option Reply)} {event : Request × Option Reply}
    (source : Prefix (.call request next) (before ++ [event]))
    (setting : event.1.op = .setAttribute) : before = [] ∧ event.1 = request := by
  cases before with
  | nil =>
    rcases event with ⟨operation, observed⟩
    cases observed <;> cases source <;> exact ⟨rfl, rfl⟩
  | cons first rest =>
    cases rest with
    | nil =>
      change Prefix (.call request next) [first, event] at source
      cases source with
      | returned request next reply events following =>
        exact False.elim (no_attribute_last (profile reply) (before := []) following setting)
    | cons second rest =>
      change Prefix (.call request next) (first :: second :: (rest ++ [event])) at source
      cases source with
      | returned request next reply events following =>
        exact False.elim (no_attribute_last (profile reply) (before := second :: rest) following setting)

structure RunMarkerCall (before : List (Request × Option Reply)) (request : Request) where
  uid : Nat
  areaPath : String
  container : Directories.Opened
  child : Directories.NewDirectory
  selecting : List (Request × Reply)
  creating : List (Request × Reply)
  selected : Returns Directories.temporaryParent selecting (.ok (container, areaPath, uid))
  created : Returns (Directories.newChild uid container.fd PrivateNames.prefixText) creating (.ok child)
  trace : before = Publication.completed (selecting ++ creating)
  operation : request = {
    op := .setAttribute
    first := child.directory.fd
    left := PrivateNames.attributeName
    right := PrivateNames.attributeValue }

-- §FS-host-boundary.ownership: The same private marker follows this successful child opening.
theorem run_marker_call {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (active : Prefix RunDirectory.create (before ++ [(request, observed)])) (setting : request.op = .setAttribute) :
    Nonempty (RunMarkerCall before request) := by
  unfold RunDirectory.create at active
  rcases filesystem_last_bind_split _ _ active with selecting |
      ⟨selecting, selected, afterSelection, selectedSource, following, shape⟩
  · exact False.elim (no_attribute_last (request_weaken RunDirectory.temporaryParent_requests
      (fun _ permitted => permitted.2.1)) selecting setting)
  · cases selected with
    | error error => exact False.elim (no_attribute_last (.pure _) following setting)
    | ok area =>
      rcases area with ⟨container, areaPath, uid⟩
      rcases filesystem_last_bind_split _ _ following with creating |
          ⟨creating, child, afterCreate, created, following, createShape⟩
      · exact False.elim (no_attribute_last (request_weaken (RunDirectory.directoryChild_requests _ _ _)
          (fun _ permitted => permitted.2.1)) creating setting)
      · cases child with
        | error error => exact False.elim (no_attribute_last
            (Publication.readOnly_no_attribute (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _)))
            following setting)
        | ok child =>
          obtain ⟨rfl, same⟩ := attribute_call_last _ _
            (fun reply => run_after_mark_no_attribute container areaPath child reply) following setting
          refine ⟨⟨uid, areaPath, container, child, selecting, creating, selectedSource, created, ?_, same⟩⟩
          simp only [shape, createShape, List.append_nil, Publication.completed, List.map_append]

end LeanCage.Host.Kernel
