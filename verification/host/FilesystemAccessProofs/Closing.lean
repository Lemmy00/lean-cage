import FilesystemAccessProofs.Phases

namespace LeanCage.Host.Filesystem

private theorem close_not_probe {request : Request} (closed : request.op = .close) : ¬ ProbeRequest request := by
  simp only [ProbeRequest, closed, reduceCtorEq, or_self, not_false_eq_true]

-- §FS-host-boundary.lookup: Rejection closes exactly the descriptor returned by this open.
theorem opened_close_cut {primary : Request} {opened : Reply} {events : List (Request × Option Reply)}
    (source : Prefix (Lookup.opened primary opened) events) {event : Request × Option Reply}
    (selected : event ∈ events) (closed : event.1.op = .close) :
    ∃ fd checks observed, primary.op = .openAt ∧ primary.second = directoryFlags ∧
      Lookup.descriptor? opened = some fd ∧ Returns (Lookup.check fd) checks false ∧
      events = checks.map (fun item => (item.1, some item.2)) ++ [({ op := .close, first := fd }, observed)] ∧
      event = ({ op := .close, first := fd }, observed) := by
  unfold Lookup.opened at source
  split at source
  · rename_i directory
    have directory : primary.op = .openAt ∧ primary.second = directoryFlags := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using directory
    split at source
    · cases source; cases selected
    · rename_i fd parsed
      rcases adapter_prefix_bind_split _ _ source with checking |
        ⟨checks, accepted, ending, checked, following, shape⟩
      · have probe := profile_prefix (lookup_check_profile fd ProbeRequest (.inl rfl) (.inr rfl))
          checking event selected
        exact False.elim (close_not_probe closed probe)
      · rw [shape] at selected
        rcases List.mem_append.mp selected with earlier | later
        · obtain ⟨original, member, same⟩ := List.mem_map.mp earlier
          subst event
          have probe := profile_returns (lookup_check_profile fd ProbeRequest (.inl rfl) (.inr rfl))
            checked original member
          exact False.elim (close_not_probe closed probe)
        · cases accepted with
          | true => cases following; cases later
          | false =>
            change Prefix (.call { op := .close, first := fd } (fun _ => .pure Lookup.unsupported)) ending at following
            cases following with
            | empty => cases later
            | lost =>
              exact ⟨fd, checks, none, directory.1, directory.2, parsed, checked, shape,
                List.mem_singleton.mp later⟩
            | returned _ _ reply trailing remaining =>
              cases remaining
              exact ⟨fd, checks, some reply, directory.1, directory.2, parsed, checked, shape,
                List.mem_singleton.mp later⟩
  · cases source; cases selected

-- §FS-host-boundary.acceptance: Even a lost rejection close retains the same earlier open/reply.
theorem guarded_extra_close_cut {primary : Request} {events : List (Request × Option Reply)}
    (source : Prefix (guardedCall primary) events) {event : Request × Option Reply}
    (selected : event ∈ events) (closed : event.1.op = .close) (extra : primary.op ≠ .close) :
    ∃ parents opened checks fd observed,
      CheckedParents (Lookup.parents primary) parents ∧ primary.op = .openAt ∧ primary.second = directoryFlags ∧
      Lookup.descriptor? opened = some fd ∧ Returns (Lookup.check fd) checks false ∧
      events = parents.map (fun item => (item.1, some item.2)) ++ (primary, some opened) ::
        (checks.map (fun item => (item.1, some item.2)) ++ [({ op := .close, first := fd }, observed)]) ∧
      event = ({ op := .close, first := fd }, observed) := by
  unfold guardedCall at source
  rcases adapter_prefix_bind_split _ _ source with checking |
    ⟨parents, accepted, continuation, checked, following, shape⟩
  · have probe := profile_prefix (lookup_all_probe_profile _) checking event selected
    exact False.elim (close_not_probe closed probe)
  · cases accepted with
    | false =>
      cases following
      rw [shape, List.append_nil] at selected
      obtain ⟨original, member, same⟩ := List.mem_map.mp selected
      subst event
      have probe := profile_returns (lookup_all_probe_profile _) checked original member
      exact False.elim (close_not_probe closed probe)
    | true =>
      rw [shape] at selected
      rcases List.mem_append.mp selected with earlier | later
      · obtain ⟨original, member, same⟩ := List.mem_map.mp earlier
        subst event
        have probe := profile_returns (lookup_all_probe_profile _) checked original member
        exact False.elim (close_not_probe closed probe)
      · change Prefix (.call primary (fun reply => Lookup.opened primary reply)) continuation at following
        cases following with
        | empty => cases later
        | lost =>
          have same := List.mem_singleton.mp later
          rw [same] at closed
          exact False.elim (extra closed)
        | returned _ _ reply trailing remaining =>
          rcases List.mem_cons.mp later with same | later
          · rw [same] at closed
            exact False.elim (extra closed)
          · obtain ⟨fd, checks, observed, directory, flags, parsed, denied, closeShape, same⟩ :=
              opened_close_cut remaining later closed
            exact ⟨parents, reply, checks, fd, observed, checked_parents_source checked, directory, flags,
              parsed, denied, by rw [shape, closeShape], same⟩

end LeanCage.Host.Filesystem
