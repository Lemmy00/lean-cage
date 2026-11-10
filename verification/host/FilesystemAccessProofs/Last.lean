import FilesystemAccessProofs.Closing

namespace LeanCage.Host.Filesystem

-- §FS-host-boundary.lookup: A namespace operation at the exact final position has only the
-- accepted parent probes before it; post-open validation remains a later raw prefix.
theorem guarded_namespace_last {primary request : Request} {observed : Option Reply}
    {before : List (Request × Option Reply)}
    (source : Prefix (guardedCall primary) (before ++ [(request, observed)]))
    (kind : NamespaceRequest request) :
    ∃ checks, CheckedParents (Lookup.parents primary) checks ∧ request = primary ∧
      before = checks.map (fun item => (item.1, some item.2)) := by
  obtain ⟨checks, actualReply, trailing, checked, shape, same, lost, returned⟩ :=
    guarded_namespace_cut source (event := (request, observed)) (by simp) kind
  have empty : trailing = [] := by
    rcases List.eq_nil_or_concat trailing with empty | ⟨inside, final, last⟩
    · exact empty
    · have tailMember : (request, observed) ∈ trailing := by
        have concatenated : List.concat before (request, observed) =
            List.concat (checks.map (fun item => (item.1, some item.2)) ++
              (primary, actualReply) :: inside) final := by
          simpa only [last, List.concat_eq_append, List.cons_append, List.append_assoc] using shape
        have finalSame := (List.of_concat_eq_concat concatenated).2
        rw [last]
        simp only [List.concat_eq_append, List.mem_append, List.mem_singleton, finalSame, or_true]
      cases actualReply with
      | none => rw [lost rfl] at tailMember; cases tailMember
      | some reply =>
        have auxiliary := profile_prefix (lookup_opened_auxiliary primary reply)
          (returned reply rfl) (request, observed) tailMember
        exact False.elim (namespace_not_auxiliary kind auxiliary)
  rw [empty] at shape
  have requestSame : request = primary := congrArg Prod.fst same
  have replySame : observed = actualReply := congrArg Prod.snd same
  have concatenated : List.concat before (request, observed) =
      List.concat (checks.map (fun item => (item.1, some item.2))) (request, observed) := by
    simpa only [← requestSame, ← replySame, List.concat_eq_append] using shape
  exact ⟨checks, checked, requestSame, (List.of_concat_eq_concat concatenated).1⟩

theorem completed_injective : Function.Injective
    (fun events : List (Request × Reply) => events.map (fun item => (item.1, some item.2))) := by
  intro first second same
  induction first generalizing second with
  | nil => cases second <;> cases same; rfl
  | cons event rest ih =>
    cases second with
    | nil => cases same
    | cons next remaining =>
      have parts := List.cons.inj same
      have sameEvent : event = next := by
        rcases event with ⟨request, reply⟩
        rcases next with ⟨operation, observed⟩
        have requests := congrArg Prod.fst parts.1
        have replies := Option.some.inj (congrArg Prod.snd parts.1)
        cases requests
        cases replies
        rfl
      cases sameEvent
      exact congrArg (event :: ·) (ih parts.2)

end LeanCage.Host.Filesystem
