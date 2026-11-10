import FilesystemCapabilities

namespace LeanCage.Host.Kernel
open Filesystem

abbrev Family := ObjectId → Option ObjectId

def NamespaceWellFormed (world : World) : Prop :=
  ∀ parent name child, world.entries parent name = some child →
    world.allocated parent = true ∧ world.allocated child = true

-- §FS-host-boundary.ownership: Private families have one reserved root and closed descendants.
structure FamilyGraph (world : World) (family : Family) (initialObjects : ObjectId → Bool)
    (dataObjects : ObjectId → Prop) : Prop where
  live : ∀ object scope, family object = some scope → world.allocated object = true
  young : ∀ object scope, family object = some scope → initialObjects object = false
  data : ∀ object scope, family object = some scope → dataObjects object
  border : ∀ parent name child scope, world.entries parent name = some child → family child = some scope →
    family parent = some scope ∨ (PrivateNames.reservedBytes name = true ∧ child = scope)
  descendants : ∀ parent name child scope, world.entries parent name = some child → family parent = some scope →
    family child = some scope

theorem empty_family_graph (world : World) (initialObjects : ObjectId → Bool) (dataObjects : ObjectId → Prop) :
    FamilyGraph world (fun _ => none) initialObjects dataObjects := by
  constructor
  · intro object scope impossible; cases impossible
  · intro object scope impossible; cases impossible
  · intro object scope impossible; cases impossible
  · intro parent name child scope entry impossible; cases impossible
  · intro parent name child scope entry impossible; cases impossible

def setFamily (family : Family) (object scope : ObjectId) : Family :=
  fun query => if query = object then some scope else family query

noncomputable def putBinding (entries : ObjectId → ByteArray → Option ObjectId)
    (parent : ObjectId) (name : ByteArray) (object : ObjectId) : ObjectId → ByteArray → Option ObjectId := by
  classical
  exact fun query component => if query = parent ∧ component = name then some object else entries query component

theorem family_graph_adjoin {before after : World} {family : Family} {initialObjects : ObjectId → Bool}
    {dataObjects : ObjectId → Prop} (graph : FamilyGraph before family initialObjects dataObjects)
    (wellFormed : NamespaceWellFormed before) (object scope parent : ObjectId) (name : ByteArray)
    (fresh : before.allocated object = false) (allocated : after.allocated object = true)
    (young : initialObjects object = false) (data : dataObjects object)
    (parentAllocated : before.allocated parent = true)
    (oldAllocation : ∀ query, before.allocated query = true → after.allocated query = true)
    (entries : after.entries = putBinding before.entries parent name object)
    (origin : family parent = some scope ∨
      (scope = object ∧ family parent = none ∧ PrivateNames.reservedBytes name = true)) :
    FamilyGraph after (setFamily family object scope) initialObjects dataObjects := by
  classical
  have parentDifferent : parent ≠ object := by intro same; rw [same, fresh] at parentAllocated; cases parentAllocated
  have oldFamily : ∀ query, before.allocated query = true → query ≠ object := by
    intro query allocatedBefore same
    rw [same, fresh] at allocatedBefore
    cases allocatedBefore
  have oldEntry : ∀ query component child, before.entries query component = some child →
      query ≠ object ∧ child ≠ object := by
    intro query component child actual
    have live := wellFormed _ _ _ actual
    exact ⟨oldFamily query live.1, oldFamily child live.2⟩
  constructor
  · intro query owner label
    by_cases same : query = object
    · subst query; exact allocated
    · have earlier : family query = some owner := by simpa only [setFamily, ite_eq_right same] using label
      exact oldAllocation query (graph.live query owner earlier)
  · intro query owner label
    by_cases same : query = object
    · subst query; exact young
    · apply graph.young query owner
      simpa only [setFamily, ite_eq_right same] using label
  · intro query owner label
    by_cases same : query = object
    · subst query; exact data
    · apply graph.data query owner
      simpa only [setFamily, ite_eq_right same] using label
  · intro query component child owner binding label
    rw [entries] at binding
    unfold putBinding at binding
    split at binding
    · rename_i current
      rcases current with ⟨querySame, componentSame⟩
      subst query
      subst component
      have childSame := Option.some.inj binding
      subst child
      have sameOwner : owner = scope := Option.some.inj (by
        simpa only [setFamily, ite_eq_left] using label.symm)
      subst owner
      rcases origin with privateParent | ⟨rfl, publicParent, reserved⟩
      · left; simpa only [setFamily, ite_eq_right parentDifferent] using privateParent
      · exact .inr ⟨reserved, rfl⟩
    · have previous := oldEntry query component child binding
      have earlier : family child = some owner := by
        simpa only [setFamily, ite_eq_right previous.2] using label
      rcases graph.border query component child owner binding earlier with inside | reserved
      · left; simpa only [setFamily, ite_eq_right previous.1] using inside
      · exact .inr reserved
  · intro query component child owner binding label
    rw [entries] at binding
    unfold putBinding at binding
    split at binding
    · rename_i current
      rcases current with ⟨querySame, componentSame⟩
      subst query
      subst component
      have childSame := Option.some.inj binding
      subst child
      have earlier : family parent = some owner := by
        simpa only [setFamily, ite_eq_right parentDifferent] using label
      rcases origin with privateParent | ⟨same, publicParent, reserved⟩
      · have sameOwner : owner = scope := Option.some.inj (earlier.symm.trans privateParent)
        subst owner
        simp only [setFamily, ite_eq_left]
      · rw [publicParent] at earlier; cases earlier
    · have previous := oldEntry query component child binding
      have earlier : family query = some owner := by
        simpa only [setFamily, ite_eq_right previous.1] using label
      have descendant := graph.descendants query component child owner binding earlier
      simpa only [setFamily, ite_eq_right previous.2] using descendant

-- §FS-host-boundary.ownership: Allocating a new object cannot privatize an existing public object.
theorem set_family_preserves_public {world : World} {family : Family} {object query scope : ObjectId}
    (fresh : world.allocated object = false) (existing : world.allocated query = true) (publicObject : family query = none) :
    setFamily family object scope query = none := by
  have different : query ≠ object := by intro same; rw [same, fresh] at existing; cases existing
  simpa only [setFamily, ite_eq_right different] using publicObject

theorem family_initial_public {world : World} {family : Family} {initialObjects : ObjectId → Bool}
    {dataObjects : ObjectId → Prop} (graph : FamilyGraph world family initialObjects dataObjects)
    (object : ObjectId) (initial : initialObjects object = true) : family object = none := by
  cases label : family object with
  | none => rfl
  | some scope => have young := graph.young object scope label; rw [initial] at young; cases young

theorem family_graph_delete {before after : World} {family : Family} {initialObjects : ObjectId → Bool}
    {dataObjects : ObjectId → Prop} (graph : FamilyGraph before family initialObjects dataObjects)
    (allocation : ∀ object, before.allocated object = true → after.allocated object = true)
    (entries : ∀ parent name child, after.entries parent name = some child → before.entries parent name = some child) :
    FamilyGraph after family initialObjects dataObjects := by
  constructor
  · intro object scope label; exact allocation object (graph.live object scope label)
  · exact graph.young
  · exact graph.data
  · intro parent name child scope entry label; exact graph.border _ _ _ _ (entries _ _ _ entry) label
  · intro parent name child scope entry label; exact graph.descendants _ _ _ _ (entries _ _ _ entry) label

theorem family_graph_public_adjoin {before after : World} {family : Family} {initialObjects : ObjectId → Bool}
    {dataObjects : ObjectId → Prop} (graph : FamilyGraph before family initialObjects dataObjects)
    (object parent : ObjectId) (name : ByteArray) (fresh : before.allocated object = false)
    (publicParent : family parent = none)
    (allocation : ∀ query, before.allocated query = true → after.allocated query = true)
    (entries : after.entries = putBinding before.entries parent name object) :
    FamilyGraph after family initialObjects dataObjects := by
  classical
  have publicObject : family object = none := by
    cases label : family object with
    | none => rfl
    | some owner => have live := graph.live _ _ label; rw [fresh] at live; cases live
  constructor
  · intro query scope label; exact allocation query (graph.live query scope label)
  · exact graph.young
  · exact graph.data
  · intro query component child scope entry label
    rw [entries] at entry
    unfold putBinding at entry
    split at entry
    · have same := Option.some.inj entry
      subst child
      rw [publicObject] at label
      cases label
    · exact graph.border _ _ _ _ entry label
  · intro query component child scope entry label
    rw [entries] at entry
    unfold putBinding at entry
    split at entry
    · rename_i touched
      rw [touched.1, publicParent] at label
      cases label
    · exact graph.descendants _ _ _ _ entry label

theorem family_graph_public_move {before after : World} {family : Family} {initialObjects : ObjectId → Bool}
    {dataObjects : ObjectId → Prop} (graph : FamilyGraph before family initialObjects dataObjects)
    (object target : ObjectId) (name : ByteArray) (publicObject : family object = none)
    (publicTarget : family target = none)
    (allocation : ∀ query, before.allocated query = true → after.allocated query = true)
    (entries : ∀ parent component child, after.entries parent component = some child →
      (parent = target ∧ component = name ∧ child = object) ∨ before.entries parent component = some child) :
    FamilyGraph after family initialObjects dataObjects := by
  constructor
  · intro query scope label; exact allocation query (graph.live query scope label)
  · exact graph.young
  · exact graph.data
  · intro parent component child scope entry label
    rcases entries _ _ _ entry with ⟨rfl, rfl, rfl⟩ | old
    · rw [publicObject] at label; cases label
    · exact graph.border _ _ _ _ old label
  · intro parent component child scope entry label
    rcases entries _ _ _ entry with ⟨rfl, rfl, rfl⟩ | old
    · rw [publicTarget] at label; cases label
    · exact graph.descendants _ _ _ _ old label

def clearFamily (family : Family) (scope : ObjectId) : Family :=
  fun object => if family object = some scope then none else family object

theorem clear_family_some {family : Family} {scope object owner : ObjectId}
    (label : clearFamily family scope object = some owner) : family object = some owner ∧ owner ≠ scope := by
  unfold clearFamily at label
  split at label
  · cases label
  · rename_i different
    exact ⟨label, fun same => different (same ▸ label)⟩

theorem clear_family_none {family : Family} {scope object : ObjectId}
    (label : family object = none) : clearFamily family scope object = none := by
  simp only [clearFamily, label, reduceCtorEq, ite_false]

-- §FS-host-boundary.publication: Publication releases only its own private family at its new name.
theorem family_graph_publish {before after : World} {family : Family} {initialObjects : ObjectId → Bool}
    {dataObjects : ObjectId → Prop} (graph : FamilyGraph before family initialObjects dataObjects)
    (scope target : ObjectId) (name : ByteArray) (root : family scope = some scope)
    (publicTarget : family target = none)
    (allocation : ∀ object, before.allocated object = true → after.allocated object = true)
    (entries : ∀ parent component child, after.entries parent component = some child →
      (parent = target ∧ component = name ∧ child = scope) ∨ before.entries parent component = some child) :
    FamilyGraph after (clearFamily family scope) initialObjects dataObjects := by
  constructor
  · intro object owner label
    exact allocation object (graph.live object owner (clear_family_some label).1)
  · intro object owner label; exact graph.young object owner (clear_family_some label).1
  · intro object owner label; exact graph.data object owner (clear_family_some label).1
  · intro parent component child owner entry label
    have previous := clear_family_some label
    rcases entries parent component child entry with ⟨rfl, rfl, rfl⟩ | old
    · rw [root] at previous
      have sameOwner := Option.some.inj previous.1
      exact False.elim (previous.2 sameOwner.symm)
    · rcases graph.border parent component child owner old previous.1 with inside | reserved
      · left
        have different : family parent ≠ some scope := by
          intro same
          have equal := Option.some.inj (inside.symm.trans same)
          exact previous.2 equal
        simpa only [clearFamily, ite_eq_right different] using inside
      · exact .inr reserved
  · intro parent component child owner entry label
    have previous := clear_family_some label
    rcases entries parent component child entry with ⟨rfl, rfl, rfl⟩ | old
    · rw [publicTarget] at previous; cases previous.1
    · have inside := graph.descendants parent component child owner old previous.1
      have different : family child ≠ some scope := by
        intro same
        have equal := Option.some.inj (inside.symm.trans same)
        exact previous.2 equal
      simpa only [clearFamily, ite_eq_right different] using inside

-- §FS-host-boundary.ownership: Releasing one family's label does not grant another private scope.
theorem clear_preserves_public (family : Family) (scope object : ObjectId) (publicObject : family object = none) :
    clearFamily family scope object = none := clear_family_none publicObject

def Capabilities.published (caps : Capabilities) (world : World) (scope : ObjectId) : Capabilities :=
  { caps.retain world with family := clearFamily caps.family scope }

-- §FS-host-boundary.publication: A committed root is retired while every other root stays owned.
theorem published_capabilities_valid {caps : Capabilities} {before after : World} {root : PrivateRoot}
    (valid : caps.Valid before) (member : root ∈ caps.roots)
    (gone : after.entries root.parent root.name ≠ some root.object)
    (allocation : ∀ object, before.allocated object = true → after.allocated object = true) :
    (caps.published after root.object).Valid after := by
  constructor
  · intro query retained
    have previous := List.mem_filter.mp retained
    obtain ⟨object, parent, _, family, publicParent⟩ := valid.1 query previous.1
    have different : query.object ≠ root.object := by
      intro same
      have sameRoot := valid.2 query previous.1 root member same
      subst query
      exact gone (by simpa using previous.2)
    refine ⟨allocation _ object, allocation _ parent, by simpa using previous.2, ?_, ?_⟩
    · have notSelected : caps.family query.object ≠ some root.object := by
        rw [family]
        exact fun same => different (Option.some.inj same)
      simpa only [Capabilities.published, clearFamily, ite_eq_right notSelected] using family
    · exact clear_family_none publicParent
  · intro first firstMember second secondMember same
    exact valid.2 first (List.mem_filter.mp firstMember).1 second (List.mem_filter.mp secondMember).1 same

end LeanCage.Host.Kernel
