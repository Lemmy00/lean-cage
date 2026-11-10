import FilesystemFamilies
import FilesystemRecording

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: Mutating calls use actual retained raw directory operands.
def DirectoryOperands (world : World) (request : Request) : Prop :=
  match request.op with
  | .openAt => request.second = newFileFlags → ∃ parent, world.handles request.first = some parent
  | .mkdirAt | .unlinkAt => ∃ parent, world.handles request.first = some parent
  | .renameNew => (∃ parent, world.handles request.first = some parent) ∧
      ∃ parent, world.handles request.second = some parent
  | .temporary => False
  | _ => True

-- §AR-host-boundary.primitives: This is one syscall's stored-data namespace delta, including loss.
inductive DataChange (dataObjects : ObjectId → Prop) (request : Request) (before after : World) : Prop where
  | unchanged (entries : after.entries = before.entries)
  | created (parent : Handle) (object : ObjectId)
      (operation : request.op = .mkdirAt ∨ (request.op = .openAt ∧ request.second = newFileFlags))
      (reference : before.handles request.first = some parent)
      (parentLive : before.allocated parent.object = true)
      (fresh : before.allocated object = false) (allocated : after.allocated object = true)
      (data : dataObjects object) (absent : before.entries parent.object request.left = none)
      (entries : after.entries = putBinding before.entries parent.object request.left object) :
      DataChange dataObjects request before after
  | removed (operation : request.op = .unlinkAt)
      (entries : ∀ parent name child, after.entries parent name = some child →
        before.entries parent name = some child) : DataChange dataObjects request before after
  | renamed (source target : Handle) (object : ObjectId) (operation : request.op = .renameNew)
      (sourceReference : before.handles request.first = some source)
      (targetReference : before.handles request.second = some target)
      (targetLive : before.allocated target.object = true)
      (sourceBinding : before.entries source.object request.left = some object)
      (targetAbsent : before.entries target.object request.right = none)
      (sourceGone : after.entries source.object request.left = none)
      (targetBinding : after.entries target.object request.right = some object)
      (entries : ∀ parent name child, after.entries parent name = some child →
        (parent = target.object ∧ name = request.right ∧ child = object) ∨
        before.entries parent name = some child) : DataChange dataObjects request before after

structure DataNamespaceContract (kernel : Contract) (dataObjects : ObjectId → Prop) : Prop where
  operation : ∀ before after request observed,
    kernel.step before request observed after → ComponentRequest request → DirectoryOperands before request →
    DataChange dataObjects request before after

theorem data_change_well_formed {dataObjects : ObjectId → Prop} {request : Request} {before after : World}
    (change : DataChange dataObjects request before after) (wellFormed : NamespaceWellFormed before)
    (allocation : ∀ object, before.allocated object = true → after.allocated object = true) :
    NamespaceWellFormed after := by
  classical
  intro parent name child binding
  cases change with
  | unchanged entries => rw [entries] at binding; exact ⟨allocation _ (wellFormed _ _ _ binding).1,
      allocation _ (wellFormed _ _ _ binding).2⟩
  | created source object operation reference parentLive fresh allocated data absent entries =>
    rw [entries] at binding
    unfold putBinding at binding
    split at binding
    · rename_i touched
      have same := Option.some.inj binding
      subst child
      exact ⟨by rw [touched.1]; exact allocation _ parentLive, allocated⟩
    · exact ⟨allocation _ (wellFormed _ _ _ binding).1, allocation _ (wellFormed _ _ _ binding).2⟩
  | removed operation entries =>
    have old := wellFormed _ _ _ (entries _ _ _ binding)
    exact ⟨allocation _ old.1, allocation _ old.2⟩
  | renamed source target object operation sourceReference targetReference targetLive
      sourceBinding targetAbsent sourceGone targetBinding entries =>
    rcases entries _ _ _ binding with ⟨rfl, rfl, rfl⟩ | old
    · exact ⟨allocation _ targetLive, allocation _ (wellFormed _ _ _ sourceBinding).2⟩
    · exact ⟨allocation _ (wellFormed _ _ _ old).1, allocation _ (wellFormed _ _ _ old).2⟩

-- §FS-host-boundary.publication: The application must derive the own-root/public-target move role.
def PublicationMove (family : Family) (request : Request) (before : World) : Prop :=
  ∀ source target object, before.handles request.first = some source →
    before.handles request.second = some target → before.entries source.object request.left = some object →
    family target.object = none ∧ (family object = none ∨ family object = some object)

def PublicRetained (before _after : World) (initial final : Family) : Prop :=
  ∀ object, before.allocated object = true → initial object = none → final object = none

-- §FS-host-boundary.ownership: Family transitions retain existing public objects, also on loss.
theorem data_change_family {dataObjects : ObjectId → Prop} {initialObjects : ObjectId → Bool}
    {request : Request} {before after : World} {family : Family}
    (change : DataChange dataObjects request before after)
    (graph : FamilyGraph before family initialObjects dataObjects) (wellFormed : NamespaceWellFormed before)
    (allocation : ∀ object, before.allocated object = true → after.allocated object = true)
    (birthYoung : ∀ object, before.allocated object = false → after.allocated object = true → initialObjects object = false)
    (publication : request.op = .renameNew → PublicationMove family request before) :
    ∃ final, FamilyGraph after final initialObjects dataObjects ∧ PublicRetained before after family final := by
  classical
  cases change with
  | unchanged entries =>
    exact ⟨family, family_graph_delete graph allocation (by intro parent name child bound; rw [entries] at bound; exact bound),
      by intro object allocated publicObject; exact publicObject⟩
  | removed operation entries =>
    exact ⟨family, family_graph_delete graph allocation entries,
      by intro object allocated publicObject; exact publicObject⟩
  | created parent object operation reference parentLive fresh allocated data absent entries =>
    cases parentFamily : family parent.object with
    | some scope =>
      exact ⟨setFamily family object scope,
        family_graph_adjoin graph wellFormed object scope parent.object request.left fresh allocated
          (birthYoung object fresh allocated) data parentLive allocation entries (.inl parentFamily),
        by intro query existing publicObject; exact set_family_preserves_public fresh existing publicObject⟩
    | none =>
      cases reserved : PrivateNames.reservedBytes request.left with
      | true =>
        exact ⟨setFamily family object object,
          family_graph_adjoin graph wellFormed object object parent.object request.left fresh allocated
            (birthYoung object fresh allocated) data parentLive allocation entries (.inr ⟨rfl, parentFamily, reserved⟩),
          by intro query existing publicObject; exact set_family_preserves_public fresh existing publicObject⟩
      | false =>
        exact ⟨family, family_graph_public_adjoin graph object parent.object request.left fresh parentFamily allocation entries,
          by intro query existing publicObject; exact publicObject⟩
  | renamed source target object operation sourceReference targetReference targetLive
      sourceBinding targetAbsent sourceGone targetBinding entries =>
    obtain ⟨publicTarget, publicObject | privateRoot⟩ :=
      publication operation source target object sourceReference targetReference sourceBinding
    · exact ⟨family, family_graph_public_move graph object target.object request.right publicObject publicTarget allocation entries,
        by intro query existing publicObject; exact publicObject⟩
    · exact ⟨clearFamily family object,
        family_graph_publish graph object target.object request.right privateRoot publicTarget allocation entries,
        by intro query existing publicObject; exact clear_preserves_public family object query publicObject⟩

end LeanCage.Host.Kernel
