import FilesystemAccessProofs.Profiles

namespace LeanCage.Host.Filesystem

def ProbeRequest (request : Request) : Prop :=
  request.op = .filesystemType ∨ request.op = .inodeFlags

def AuxiliaryRequest (request : Request) : Prop := ProbeRequest request ∨ request.op = .close

def NamespaceRequest (request : Request) : Prop :=
  request.op = .openAt ∨ request.op = .mkdirAt ∨ request.op = .unlinkAt ∨
    request.op = .renameNew ∨ request.op = .dirOpen

-- §FS-host-boundary.lookup: Every checked parent has its own sequential, exact ABI transcript.
inductive CheckedParents : List UInt64 → List (Request × Reply) → Prop where
  | nil : CheckedParents [] []
  | cons (fd : UInt64) (rest : List UInt64) (first last : List (Request × Reply))
      (checked : Lookup.Accepted fd first) (following : CheckedParents rest last) :
      CheckedParents (fd :: rest) (first ++ last)

theorem checked_parents_source {fds : List UInt64} {events : List (Request × Reply)}
    (source : Returns (Lookup.checkAll fds) events true) : CheckedParents fds events := by
  induction fds generalizing events with
  | nil => cases source; exact .nil
  | cons fd rest ih =>
    unfold Lookup.checkAll at source
    obtain ⟨first, accepted, last, checked, following, shape⟩ := adapter_returns_bind_split _ _ source
    cases accepted with
    | false => cases following
    | true =>
      rw [shape]
      exact .cons fd rest first last (lookup_check_source checked) (ih following)

theorem checked_parents_probes {fds : List UInt64} {events : List (Request × Reply)}
    (checked : CheckedParents fds events) : ∀ event ∈ events, ProbeRequest event.1 := by
  induction checked with
  | nil => simp
  | cons fd rest first last accepted following ih =>
    intro event member
    rcases List.mem_append.mp member with earlier | later
    · rcases accepted with ⟨observed, rfl, _⟩ | ⟨observed, flags, rfl, _⟩
      · have same := List.mem_singleton.mp earlier
        subst event
        exact .inl rfl
      · rcases List.mem_cons.mp earlier with rfl | earlier
        · exact .inl rfl
        · have same := List.mem_singleton.mp earlier
          subst event
          exact .inr rfl
    · exact ih event later

theorem lookup_all_probe_profile (fds : List UInt64) : RequestProfile ProbeRequest (Lookup.checkAll fds) := by
  induction fds with
  | nil => exact .pure _
  | cons fd rest ih =>
    unfold Lookup.checkAll
    apply profile_bind (lookup_check_profile fd ProbeRequest (.inl rfl) (.inr rfl))
    intro accepted
    split
    · exact ih
    · exact .pure _

theorem lookup_opened_auxiliary (primary : Request) (reply : Reply) :
    RequestProfile AuxiliaryRequest (Lookup.opened primary reply) := by
  unfold Lookup.opened
  split
  · split
    · exact .pure _
    · apply profile_bind (lookup_check_profile _ _ (.inl (.inl rfl)) (.inl (.inr rfl)))
      intro accepted
      split
      · exact .pure _
      · exact .call _ _ (.inr rfl) (fun _ => .pure _)
  · exact .pure _

theorem namespace_not_auxiliary {request : Request} (namespaceOperation : NamespaceRequest request) :
    ¬ AuxiliaryRequest request := by
  intro auxiliary
  rcases namespaceOperation with actual | actual | actual | actual | actual <;>
    rcases auxiliary with (probe | flags) | close <;> simp_all

-- §FS-host-boundary.acceptance: The selected raw operation follows all accepted parent checks.
-- A lost primary call has no continuation; returned calls retain the exact post-open prefix.
theorem guarded_namespace_cut {primary : Request} {events : List (Request × Option Reply)}
    (source : Prefix (guardedCall primary) events) {event : Request × Option Reply}
    (selected : event ∈ events) (namespaceOperation : NamespaceRequest event.1) :
    ∃ checks observed trailing, CheckedParents (Lookup.parents primary) checks ∧
      events = checks.map (fun item => (item.1, some item.2)) ++ (primary, observed) :: trailing ∧
      event = (primary, observed) ∧
      (observed = none → trailing = []) ∧
      (∀ reply, observed = some reply → Prefix (Lookup.opened primary reply) trailing) := by
  unfold guardedCall at source
  rcases adapter_prefix_bind_split _ _ source with checking |
    ⟨checks, accepted, continuation, completed, following, shape⟩
  · have probe := profile_prefix (lookup_all_probe_profile _) checking event selected
    exact False.elim (namespace_not_auxiliary namespaceOperation (.inl probe))
  · cases accepted with
    | false =>
      cases following
      rw [shape, List.append_nil] at selected
      obtain ⟨original, member, same⟩ := List.mem_map.mp selected
      subst event
      have probe := profile_returns (lookup_all_probe_profile _) completed original member
      exact False.elim (namespace_not_auxiliary namespaceOperation (.inl probe))
    | true =>
      have checked := checked_parents_source completed
      rw [shape] at selected
      rcases List.mem_append.mp selected with earlier | later
      · obtain ⟨original, member, same⟩ := List.mem_map.mp earlier
        subst event
        have probe := checked_parents_probes checked original member
        exact False.elim (namespace_not_auxiliary namespaceOperation (.inl probe))
      · change Prefix (.call primary (fun reply => Lookup.opened primary reply)) continuation at following
        cases following with
        | empty => cases later
        | lost =>
          have same := List.mem_singleton.mp later
          exact ⟨checks, none, [], checked, shape, same, fun _ => rfl,
            fun reply impossible => by cases impossible⟩
        | returned _ _ reply trailing remaining =>
          rcases List.mem_cons.mp later with same | later
          · have noLost : some reply = none → trailing = [] := by
              intro impossible
              cases impossible
            have post : ∀ next, some reply = some next → Prefix (Lookup.opened primary next) trailing := by
              intro next equality
              cases equality
              exact remaining
            exact ⟨checks, some reply, trailing, checked, shape, same, noLost, post⟩
          · have auxiliary := profile_prefix (lookup_opened_auxiliary primary reply) remaining event later
            exact False.elim (namespace_not_auxiliary namespaceOperation auxiliary)

end LeanCage.Host.Filesystem
