import RunDirectoryProofs.Cleanup
import FilesystemPublicationSource

namespace LeanCage.Host.RunDirectory
open Filesystem
open Kernel (filesystem_last_bind_split)

private theorem pure_last_impossible {α : Type} (value : α)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (.pure value) (before ++ [(request, observed)])) : False := by
  have empty := Snapshot.prefix_pure_empty source
  have length := congrArg List.length empty
  simp only [List.length_append, List.length_singleton, List.length_nil] at length
  omega

private theorem no_unlink_last {α : Type} {program : Filesystem.Program α}
    (allowed : RequestProgram (fun request => request.op ≠ .unlinkAt) program)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix program (before ++ [(request, observed)])) (unlink : request.op = .unlinkAt) : False :=
  request_prefix allowed source (request, observed) (by simp) unlink

private theorem close_result_no_unlink {α : Type} (fd : UInt64) (value : Result α) :
    RequestProgram (fun request => request.op ≠ .unlinkAt) (closeResult fd value) := by
  unfold closeResult
  apply RequestProgram.call (by intro impossible; cases impossible)
  intro reply
  cases value with
  | error => exact .pure _
  | ok => dsimp only; split <;> exact .pure _

private theorem effect_return_trace {request : Request} {events : List (Request × Reply)} {reply : Reply}
    (source : Returns (Filesystem.Program.effect request) events reply) : events = [(request, reply)] := by
  cases source with
  | call _ _ observed rest _ tail => cases tail; rfl

private theorem effect_prefix_last {operation : Request}
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (Filesystem.Program.effect operation) (before ++ [(request, observed)])) :
    before = [] ∧ request = operation := by
  cases before with
  | nil => cases observed <;> cases source <;> exact ⟨rfl, rfl⟩
  | cons head rest =>
    generalize trace : (head :: rest) ++ [(request, observed)] = events at source
    cases source with
    | empty =>
      have length := congrArg List.length trace
      simp only [List.length_append, List.length_cons, List.length_nil] at length
      omega
    | lost =>
      have length := congrArg List.length trace
      simp only [List.length_append, List.length_cons, List.length_nil] at length
      omega
    | returned _ _ reply tail following =>
      exact False.elim (pure_last_impossible _ ((List.cons.inj trace).2.symm ▸ following))

structure SetupRemoval (before : List (Request × Option Reply)) (request : Request) where
  container : Directories.Opened
  path : String
  uid : Nat
  child : Directories.NewDirectory
  selecting : List (Request × Reply)
  creating : List (Request × Reply)
  selected : Returns Directories.temporaryParent selecting (.ok (container, path, uid))
  created : Returns (Directories.newChild uid container.fd PrivateNames.prefixText) creating (.ok child)
  marked : Reply
  closed : Reply
  markerFailed : (marked.1 != 0 || !marked.2.isEmpty) = true
  trace : before = Publication.completed (selecting ++ creating ++ [({
      op := .setAttribute, first := child.directory.fd,
      left := PrivateNames.attributeName, right := PrivateNames.attributeValue }, marked),
    ({op := .close, first := child.directory.fd}, closed)])
  operation : request = {op := .unlinkAt, first := container.fd, second := 512, left := child.name}

-- §FS-host-boundary.ownership: The only setup removal follows this actual
-- successful child creation, failed private marker and child-handle close.
-- No successful create return or future cleanup acknowledgement is required.
theorem setup_removal_source {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix create (before ++ [(request, observed)])) (unlink : request.op = .unlinkAt) :
    Nonempty (SetupRemoval before request) := by
  unfold create at source
  rcases filesystem_last_bind_split _ _ source with selecting |
      ⟨selecting, result, afterSelection, selected, following, selectionTrace⟩
  · exact False.elim (no_unlink_last
      (request_weaken temporaryParent_requests (fun _ allowed => allowed.2.2)) selecting unlink)
  · cases result with
    | error error => exact False.elim (pure_last_impossible _ following)
    | ok area =>
      rcases area with ⟨container, path, uid⟩
      rcases filesystem_last_bind_split _ _ following with creating |
          ⟨creating, result, afterCreation, created, following, creationTrace⟩
      · exact False.elim (no_unlink_last
          (request_weaken (directoryChild_requests _ _ _) (fun _ allowed => allowed.2.2)) creating unlink)
      · cases result with
        | error error => exact False.elim (no_unlink_last (close_result_no_unlink _ _) following unlink)
        | ok child =>
          rcases filesystem_last_bind_split _ _ following with marking |
              ⟨marking, marked, afterMark, markSource, following, markTrace⟩
          · exact False.elim (no_unlink_last
              (.call (by intro impossible; cases impossible) (fun _ => .pure _)) marking unlink)
          · have markedTrace := effect_return_trace markSource
            dsimp only at following
            split at following
            · rename_i failed
              rcases filesystem_last_bind_split _ _ following with closing |
                  ⟨closing, closed, afterClose, closeSource, following, closeTrace⟩
              · exact False.elim (no_unlink_last
                  (.call (by intro impossible; cases impossible) (fun _ => .pure _)) closing unlink)
              · have closedTrace := effect_return_trace closeSource
                rcases filesystem_last_bind_split _ _ following with removing |
                    ⟨removing, result, afterRemoval, removed, following, removeTrace⟩
                · obtain ⟨empty, sameCall⟩ := effect_prefix_last removing
                  refine ⟨⟨container, path, uid, child, selecting, creating, selected, created,
                    marked, closed, ?_, ?_, sameCall⟩⟩
                  · simpa using failed
                  · simp only [selectionTrace, creationTrace, markTrace, closeTrace, markedTrace, closedTrace, empty,
                      Publication.completed, List.map_append, List.map_cons, List.map_nil,
                      List.append_nil, List.append_assoc, List.cons_append, List.nil_append]
                · exact False.elim (no_unlink_last (close_result_no_unlink _ _) following unlink)
            · split at following
              · apply False.elim
                apply no_unlink_last ?_ following unlink
                apply request_bind (program := Filesystem.Program.effect {op := .close, first := child.directory.fd})
                  (.call (by intro impossible; cases impossible) (fun _ => .pure _))
                intro ignored
                exact close_result_no_unlink _ _
              · split at following
                · apply False.elim
                  apply no_unlink_last ?_ following unlink
                  apply request_bind (program := Filesystem.Program.effect {op := .close, first := child.directory.fd})
                    (.call (by intro impossible; cases impossible) (fun _ => .pure _))
                  intro ignored
                  exact close_result_no_unlink _ _
                · exact False.elim (pure_last_impossible _ following)

end LeanCage.Host.RunDirectory
