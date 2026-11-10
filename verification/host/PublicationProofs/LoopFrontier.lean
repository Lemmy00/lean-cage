import PublicationProofs.Frontier

namespace LeanCage.Host.Publication
open Filesystem Kernel

structure LoopFrontier {α β : Type} (items : List α) (initial : β)
    (body : α → β → Filesystem.Program (ForInStep β))
    (before : List (Request × Option Reply)) (request : Request) (observed : Option Reply) where
  earlier : List α
  item : α
  later : List α
  sequence : items = earlier ++ item :: later
  state : β
  completed : List (Request × Reply)
  prepared : Returns (forIn earlier initial body) completed state
  inside : List (Request × Option Reply)
  active : Prefix (body item state) (inside ++ [(request, observed)])
  trace : before = Publication.completed completed ++ inside

private theorem pure_no_last {α : Type} {value : α} {before : List (Request × Option Reply)}
    {event : Request × Option Reply} (source : Prefix (.pure value) (before ++ [event])) : False := by
  have length := congrArg List.length (Snapshot.prefix_pure_empty source)
  simp only [List.length_append, List.length_singleton, List.length_nil] at length
  omega

-- §FS-host-boundary.publication: A selected cleanup iteration retains all earlier
-- actual returns and its original list position. Failed or lost operations in
-- that iteration do not require the loop or cleanup to return in the future.
theorem loop_frontier {α β : Type} (items : List α) (initial : β)
    (body : α → β → Filesystem.Program (ForInStep β))
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (forIn items initial body) (before ++ [(request, observed)])) :
    Nonempty (LoopFrontier items initial body before request observed) := by
  induction items generalizing initial before with
  | nil => exact False.elim (pure_no_last source)
  | cons item rest ih =>
    rw [List.forIn_cons] at source
    rcases filesystem_last_bind_split _ _ source with active |
        ⟨leading, result, inside, called, following, trace⟩
    · exact ⟨⟨[], item, rest, rfl, initial, [], .pure _, before, active, rfl⟩⟩
    · cases result with
      | done value => exact False.elim (pure_no_last following)
      | yield value =>
        obtain ⟨frontier⟩ := ih value following
        refine ⟨{
          earlier := item :: frontier.earlier
          item := frontier.item
          later := frontier.later
          sequence := congrArg (item :: ·) frontier.sequence
          state := frontier.state
          completed := leading ++ frontier.completed
          prepared := ?_
          inside := frontier.inside
          active := frontier.active
          trace := trace.trans ((congrArg (Publication.completed leading ++ ·) frontier.trace).trans (by
            simp only [Publication.completed, List.map_append, List.append_assoc])) }⟩
        rw [List.forIn_cons]
        exact Snapshot.returns_bind_join called frontier.prepared

end LeanCage.Host.Publication
