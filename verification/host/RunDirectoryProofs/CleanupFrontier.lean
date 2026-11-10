import FilesystemUses

namespace LeanCage.Host.Kernel
open Filesystem

private theorem script_frontier {requests : List Request} {before : List (Request × Option Reply)}
    {request : Request} {observed : Option Reply}
    (source : Prefix (callScript requests) (before ++ [(request, observed)])) :
    ∃ replies : List (Request × Reply), ∃ rest,
      before = Publication.completed replies ∧ requests = replies.map Prod.fst ++ request :: rest := by
  induction before generalizing requests with
  | nil =>
    cases requests with
    | nil => cases observed <;> cases source
    | cons first rest =>
      cases observed <;> cases source <;> exact ⟨[], rest, rfl, rfl⟩
  | cons event before ih =>
    cases requests with
    | nil =>
      have empty := Snapshot.prefix_pure_empty source
      have length := congrArg List.length empty
      simp only [List.length_append, List.length_cons, List.length_nil] at length
      omega
    | cons first rest =>
      generalize shape : (event :: before) ++ [(request, observed)] = events at source
      cases source with
      | empty =>
        have length := congrArg List.length shape
        simp only [List.length_append, List.length_cons, List.length_nil] at length
        omega
      | lost =>
        have length := congrArg List.length shape
        simp only [List.length_append, List.length_cons, List.length_nil] at length
        omega
      | returned _ _ reply tail following =>
        have parts := List.cons.inj shape
        obtain ⟨replies, rest, trace, script⟩ := ih (parts.2.symm ▸ following)
        exact ⟨(first, reply) :: replies, rest, by simp only [parts.1, trace, Publication.completed, List.map_cons],
          by simp only [script, List.map_cons, List.cons_append]⟩

structure CleanupFrontier (run : RunDirectory.Owned) (before : List (Request × Option Reply))
    (request : Request) where
  replies : List (Request × Reply)
  rest : List Request
  trace : before = Publication.completed replies
  script : cleanupScript run = replies.map Prod.fst ++ request :: rest

-- §FS-host-boundary.ownership: An interrupted cleanup selects one actual call
-- from its finite source script; every preceding reply remains in order.
theorem cleanup_frontier {run : RunDirectory.Owned} {before : List (Request × Option Reply)}
    {request : Request} {observed : Option Reply}
    (source : Prefix (RunDirectory.cleanup run) (before ++ [(request, observed)])) :
    Nonempty (CleanupFrontier run before request) := by
  rw [cleanup_script] at source
  obtain ⟨replies, rest, trace, script⟩ := script_frontier source
  exact ⟨⟨replies, rest, trace, script⟩⟩

-- §FS-host-boundary.ownership: The current unlink's retained FD has not been
-- closed by any earlier cleanup call. The directory close precedes only the
-- final parent-relative removal, whose descriptor is proved distinct.
theorem CleanupFrontier.keeps_parent {run : RunDirectory.Owned} {before : List (Request × Option Reply)}
    {request : Request} (source : CleanupFrontier run before request)
    (distinct : run.directory.fd ≠ run.container.fd) (unlink : request.op = .unlinkAt) :
    ∀ prior ∈ source.replies, KeepsReference request.first prior.1 := by
  have selected : (cleanupScript run)[source.replies.length]? = some request := by
    have bound : (source.replies.map Prod.fst).length ≤ source.replies.length := by simp only [List.length_map, Nat.le_refl]
    exact (congrArg (fun requests : List Request => requests[source.replies.length]?) source.script).trans
      ((List.getElem?_append_right bound).trans (by rw [List.length_map, Nat.sub_self]; rfl))
  have leading : source.replies.map Prod.fst = (cleanupScript run).take source.replies.length := by
    rw [source.script]
    have taken : (source.replies.map Prod.fst ++ request :: source.rest).take
        (source.replies.map Prod.fst).length = source.replies.map Prod.fst := List.take_left
    simpa only [List.length_map] using taken.symm
  intro prior member
  have occurs : prior.1 ∈ source.replies.map Prod.fst := List.mem_map.mpr ⟨prior, member, rfl⟩
  rw [leading] at occurs
  cases count : source.replies.length with
  | zero => simp only [count, List.take_zero, List.not_mem_nil] at occurs
  | succ one =>
    cases one with
    | zero =>
      simp only [cleanupScript, count, List.getElem?_cons_succ, List.getElem?_cons_zero] at selected
      cases selected
      simp only [cleanupScript, count, List.take_succ_cons, List.take_zero, List.mem_cons,
        List.not_mem_nil, or_false] at occurs
      rw [occurs]
      simp [KeepsReference]
    | succ two =>
      cases two with
      | zero =>
        simp only [cleanupScript, count, List.getElem?_cons_succ, List.getElem?_cons_zero] at selected
        cases selected
        simp only [cleanupScript, count, List.take_succ_cons, List.take_zero, List.mem_cons,
          List.not_mem_nil, or_false] at occurs
        rcases occurs with same | same <;> rw [same] <;> simp [KeepsReference]
      | succ three =>
        cases three with
        | zero =>
          simp only [cleanupScript, count, List.getElem?_cons_succ, List.getElem?_cons_zero] at selected
          cases selected
          cases unlink
        | succ four =>
          cases four with
          | zero =>
            simp only [cleanupScript, count, List.getElem?_cons_succ, List.getElem?_cons_zero] at selected
            cases selected
            simp only [cleanupScript, count, List.take_succ_cons, List.take_zero, List.mem_cons,
              List.not_mem_nil, or_false] at occurs
            rcases occurs with same | same | same | same <;> rw [same] <;>
              simp [KeepsReference, Ne.symm distinct]
          | succ five =>
            cases five with
            | zero =>
              simp only [cleanupScript, count, List.getElem?_cons_succ, List.getElem?_cons_zero] at selected
              cases selected
              cases unlink
            | succ six =>
              simp only [cleanupScript, count, List.getElem?_cons_succ, List.getElem?_nil] at selected
              cases selected

-- §FS-host-boundary.ownership: Before any selected unlink, every earlier
-- unlink names a child of the run directory. The parent-relative root
-- removal is last; neither close acknowledgement authorizes a second removal.
theorem CleanupFrontier.earlier_unlinks_inside {run : RunDirectory.Owned} {before : List (Request × Option Reply)}
    {request : Request} (source : CleanupFrontier run before request) (unlink : request.op = .unlinkAt) :
    ∀ prior ∈ source.replies, prior.1.op = .unlinkAt → prior.1.first = run.directory.fd := by
  have selected : (cleanupScript run)[source.replies.length]? = some request := by
    have bound : (source.replies.map Prod.fst).length ≤ source.replies.length := by simp only [List.length_map, Nat.le_refl]
    exact (congrArg (fun requests : List Request => requests[source.replies.length]?) source.script).trans
      ((List.getElem?_append_right bound).trans (by rw [List.length_map, Nat.sub_self]; rfl))
  have leading : source.replies.map Prod.fst = (cleanupScript run).take source.replies.length := by
    rw [source.script]
    have taken : (source.replies.map Prod.fst ++ request :: source.rest).take
        (source.replies.map Prod.fst).length = source.replies.map Prod.fst := List.take_left
    simpa only [List.length_map] using taken.symm
  intro prior member removing
  have occurs : prior.1 ∈ source.replies.map Prod.fst := List.mem_map.mpr ⟨prior, member, rfl⟩
  rw [leading] at occurs
  cases count : source.replies.length with
  | zero => simp only [count, List.take_zero, List.not_mem_nil] at occurs
  | succ one =>
    cases one with
    | zero =>
      simp only [cleanupScript, count, List.take_succ_cons, List.take_zero, List.mem_cons,
        List.not_mem_nil, or_false] at occurs
      exact congrArg Request.first occurs
    | succ two =>
      cases two with
      | zero =>
        simp only [cleanupScript, count, List.take_succ_cons, List.take_zero, List.mem_cons,
          List.not_mem_nil, or_false] at occurs
        rcases occurs with same | same <;> exact congrArg Request.first same
      | succ three =>
        cases three with
        | zero =>
          simp only [cleanupScript, count, List.getElem?_cons_succ, List.getElem?_cons_zero] at selected
          cases selected
          cases unlink
        | succ four =>
          cases four with
          | zero =>
            simp only [cleanupScript, count, List.take_succ_cons, List.take_zero, List.mem_cons,
              List.not_mem_nil, or_false] at occurs
            rcases occurs with same | same | same | same
            · exact congrArg Request.first same
            · exact congrArg Request.first same
            · exact congrArg Request.first same
            · have invalid := (congrArg Request.op same).symm.trans removing
              cases invalid
          | succ five =>
            cases five with
            | zero =>
              simp only [cleanupScript, count, List.getElem?_cons_succ, List.getElem?_cons_zero] at selected
              cases selected
              cases unlink
            | succ six =>
              simp only [cleanupScript, count, List.getElem?_cons_succ, List.getElem?_nil] at selected
              cases selected

end LeanCage.Host.Kernel
