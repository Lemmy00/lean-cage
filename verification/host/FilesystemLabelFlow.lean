import FilesystemChanges

namespace LeanCage.Host.Kernel

-- §FS-host-boundary.ownership: An old object keeps its scope or becomes public at publication.
def ExistingLabels (before _after : World) (initial final : Family) : Prop :=
  ∀ object, before.allocated object = true → final object = initial object ∨ final object = none

theorem existing_labels_public {before after : World} {initial final : Family}
    (labels : ExistingLabels before after initial final) : PublicRetained before after initial final := by
  intro object allocated publicObject
  rcases labels object allocated with same | publicAfter
  · exact same.trans publicObject
  · exact publicAfter

theorem unchanged_existing_labels (before after : World) (family : Family) :
    ExistingLabels before after family family := fun _ _ => .inl rfl

theorem set_family_existing_labels {before after : World} {family : Family} {object scope : ObjectId}
    (fresh : before.allocated object = false) : ExistingLabels before after family (setFamily family object scope) := by
  intro query allocated
  have different : query ≠ object := by
    intro same
    rw [same, fresh] at allocated
    cases allocated
  exact .inl (by simp only [setFamily, ite_eq_right different])

theorem clear_family_existing_labels (before after : World) (family : Family) (scope : ObjectId) :
    ExistingLabels before after family (clearFamily family scope) := by
  intro object allocated
  unfold clearFamily
  split
  · exact .inr rfl
  · exact .inl rfl

theorem existing_labels_trans {first middle last : World} {before between after : Family}
    (initial : ExistingLabels first middle before between) (final : ExistingLabels middle last between after)
    (allocation : ∀ object, first.allocated object = true → middle.allocated object = true) :
    ExistingLabels first last before after := by
  intro object allocated
  rcases final object (allocation object allocated) with finalSame | finalPublic
  · rcases initial object allocated with firstSame | firstPublic
    · exact .inl (finalSame.trans firstSame)
    · exact .inr (finalSame.trans firstPublic)
  · exact .inr finalPublic

-- §FS-host-boundary.ownership: The actual delta's chosen family update never transfers old custody.
theorem data_change_owned_family {dataObjects : ObjectId → Prop} {initialObjects : ObjectId → Bool}
    {request : Filesystem.Request} {before after : World} {family : Family}
    (change : DataChange dataObjects request before after)
    (graph : FamilyGraph before family initialObjects dataObjects) (wellFormed : NamespaceWellFormed before)
    (allocation : ∀ object, before.allocated object = true → after.allocated object = true)
    (birthYoung : ∀ object, before.allocated object = false → after.allocated object = true → initialObjects object = false)
    (publication : request.op = .renameNew → PublicationMove family request before) :
    ∃ final, FamilyGraph after final initialObjects dataObjects ∧ ExistingLabels before after family final := by
  classical
  cases change with
  | unchanged entries =>
    have earlier : ∀ parent name object, after.entries parent name = some object →
        before.entries parent name = some object := by
      intro parent name object binding
      rw [entries] at binding
      exact binding
    exact ⟨family, family_graph_delete graph allocation earlier, unchanged_existing_labels _ _ _⟩
  | removed operation entries =>
    exact ⟨family, family_graph_delete graph allocation entries, unchanged_existing_labels _ _ _⟩
  | created parent object operation reference parentLive fresh allocated data absent entries =>
    cases parentFamily : family parent.object with
    | some scope =>
      exact ⟨setFamily family object scope,
        family_graph_adjoin graph wellFormed object scope parent.object request.left fresh allocated
          (birthYoung object fresh allocated) data parentLive allocation entries (.inl parentFamily),
        set_family_existing_labels fresh⟩
    | none =>
      cases reserved : PrivateNames.reservedBytes request.left with
      | true =>
        exact ⟨setFamily family object object,
          family_graph_adjoin graph wellFormed object object parent.object request.left fresh allocated
            (birthYoung object fresh allocated) data parentLive allocation entries (.inr ⟨rfl, parentFamily, reserved⟩),
          set_family_existing_labels fresh⟩
      | false =>
        exact ⟨family, family_graph_public_adjoin graph object parent.object request.left fresh parentFamily
          allocation entries, unchanged_existing_labels _ _ _⟩
  | renamed source target object operation sourceReference targetReference targetLive
      sourceBinding targetAbsent sourceGone targetBinding entries =>
    obtain ⟨publicTarget, publicObject | privateRoot⟩ :=
      publication operation source target object sourceReference targetReference sourceBinding
    · exact ⟨family, family_graph_public_move graph object target.object request.right publicObject publicTarget
        allocation entries, unchanged_existing_labels _ _ _⟩
    · exact ⟨clearFamily family object,
        family_graph_publish graph object target.object request.right privateRoot publicTarget allocation entries,
        clear_family_existing_labels _ _ _ _⟩

end LeanCage.Host.Kernel
