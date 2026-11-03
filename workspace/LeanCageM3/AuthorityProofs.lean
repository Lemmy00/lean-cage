import LeanCageM3.Authority

namespace LeanCageM3

-- §AR-workspace.proofs: Live issued handles carry authority independent of a later read check.
def IssuedHandles (s : Authority) : Prop :=
  ∀ fd handle, s.handles fd = some handle → ∃ object,
    deref s handle.ref = some object ∧ readable s.run object.area = true ∧
      (handle.write = true → writable s.run object.area = true)

def RetainsObjects (s t : Authority) : Prop :=
  ∀ id object, s.objects id = some object → ∃ next,
    t.objects id = some next ∧ next.generation = object.generation ∧ next.area = object.area

private theorem deref_spec (s : Authority) (ref : Ref) (object : Object) :
    deref s ref = some object ↔
      s.objects ref.object = some object ∧ object.generation = ref.generation := by
  unfold deref
  cases found : s.objects ref.object with
  | none => simp
  | some old =>
    change (if old.generation == ref.generation then some old else none) = some object ↔ _
    split
    · rename_i equal
      have generation : old.generation = ref.generation := by simpa using equal
      simp_all
      rintro rfl
      assumption
    · rename_i unequal
      simp_all
      rintro rfl
      assumption

private theorem retains_refl (s : Authority) : RetainsObjects s s := by
  intro id object found
  exact ⟨object, found, rfl, rfl⟩

private theorem retains_update (s : Authority) (id : ObjectId) (old next : Object)
    (found : s.objects id = some old) (generation : next.generation = old.generation)
    (area : next.area = old.area) :
    RetainsObjects s { s with objects := fun n => if n = id then some next else s.objects n } := by
  intro n object present
  by_cases equal : n = id
  · subst n
    rw [found] at present
    cases present
    exact ⟨next, by simp, generation, area⟩
  · exact ⟨object, by simpa [equal] using present, rfl, rfl⟩

private theorem retains_allocate (s : Authority) (id : ObjectId) (generation : UInt64)
    (bytes : List UInt8) : RetainsObjects s (allocateObject s id generation bytes) := by
  unfold allocateObject
  split
  · rename_i fresh
    intro n object present
    have different : n ≠ id := by intro equal; subst n; rw [fresh] at present; contradiction
    exact ⟨object, by simpa [different] using present, rfl, rfl⟩
  · exact retains_refl s

-- §FS-workspace.filesystem: Writes can change bytes, never generation or ownership of live objects.
theorem step_retains_objects (s : Authority) (request : Request) :
    RetainsObjects s (authorityStep s request) := by
  cases request with
  | «open» name fd write =>
    simp only [authorityStep, openName]; split
    · exact retains_refl s
    · unfold openObject; split
      · exact retains_refl s
      · split <;> exact retains_refl s
  | dup source target => simp only [authorityStep, dupHandle]; split <;> exact retains_refl s
  | close fd => exact retains_refl s
  | write fd bytes =>
    simp only [authorityStep, writeHandle]; split
    · exact retains_refl s
    · rename_i handle hh
      split
      · exact retains_refl s
      · rename_i object found
        split
        · exact retains_update s handle.ref.object object { object with bytes }
            ((deref_spec s handle.ref object).mp found).1 rfl rfl
        · exact retains_refl s
  | alias name node => exact retains_refl s
  | rename source target => simp only [authorityStep, renameName]; split <;> exact retains_refl s
  | external id bytes =>
    simp only [authorityStep, externalWrite]; split
    · exact retains_refl s
    · rename_i object found
      split <;> split
      all_goals first
        | exact retains_refl s
        | exact retains_update s id object { object with bytes } found rfl rfl
  | allocate id generation bytes => exact retains_allocate s id generation bytes
  | deniedExternal => exact retains_refl s

private theorem retained_deref (s t : Authority) (retains : RetainsObjects s t)
    (ref : Ref) (object : Object) (found : deref s ref = some object) :
    ∃ next, deref t ref = some next ∧ next.area = object.area := by
  have old := (deref_spec s ref object).mp found
  obtain ⟨next, present, generation, area⟩ := retains ref.object object old.1
  exact ⟨next, (deref_spec t ref next).mpr ⟨present, generation.trans old.2⟩, area⟩

private theorem issued_preserved (s t : Authority) (safe : IssuedHandles s)
    (owner : t.run = s.run) (retains : RetainsObjects s t)
    (handles : ∀ fd handle, t.handles fd = some handle → s.handles fd = some handle) :
    IssuedHandles t := by
  intro fd handle present
  obtain ⟨object, found, read, write⟩ := safe fd handle (handles fd handle present)
  obtain ⟨next, nextFound, area⟩ := retained_deref s t retains handle.ref object found
  exact ⟨next, nextFound, by simpa [owner, area] using read, by simpa [owner, area] using write⟩

private theorem open_issued (s : Authority) (safe : IssuedHandles s)
    (ref : Ref) (fd : UInt32) (write : Bool) : IssuedHandles (openObject s ref fd write) := by
  unfold openObject
  split
  · exact safe
  · rename_i object found
    split
    · rename_i allowed
      simp only [Bool.and_eq_true] at allowed
      intro n handle present
      by_cases equal : n = fd
      · subst n
        simp at present
        cases present
        refine ⟨object, found, ?_, ?_⟩
        · exact allowed.1.2
        · intro writableHandle
          change write = true at writableHandle
          simpa [writableHandle] using allowed.2
      · simp [equal] at present
        exact safe n handle present
    · exact safe

-- §AR-workspace.proofs: All alias, allocation and ordinary interference requests preserve issued
-- rights.
theorem issued_handles_step (s : Authority) (safe : IssuedHandles s) (request : Request) :
    IssuedHandles (authorityStep s request) := by
  have retained := step_retains_objects s request
  have owner := authority_owner_persists s request
  cases request with
  | «open» name fd write =>
    simp only [authorityStep, openName]
    split
    · exact safe
    · exact open_issued s safe _ fd write
  | dup source target =>
    simp only [authorityStep, dupHandle]
    split
    · intro fd handle present
      by_cases same : fd = target
      · subst fd; simp at present; exact safe source handle present
      · simp [same] at present; exact safe fd handle present
    · exact safe
  | close fd =>
    apply issued_preserved s _ safe owner retained
    intro n handle present
    simp only [authorityStep, closeHandle] at present
    split at present
    · contradiction
    · exact present
  | write fd bytes =>
    apply issued_preserved s _ safe owner retained
    intro n handle present
    simp only [authorityStep, writeHandle] at present
    split at present
    · exact present
    · split at present
      · exact present
      · split at present <;> exact present
  | alias name node => exact safe
  | rename source target =>
    simp only [authorityStep, renameName]
    split <;> exact safe
  | external id bytes =>
    apply issued_preserved s _ safe owner retained
    intro n handle present
    simp only [authorityStep, externalWrite] at present
    split at present
    · exact present
    · split at present <;> split at present <;> exact present
  | allocate id generation bytes =>
    apply issued_preserved s _ safe owner retained
    intro n handle present
    simp only [authorityStep, allocateObject] at present
    split at present <;> exact present
  | deniedExternal => exact safe

-- §FS-workspace.authority: The initial handle set is empty; no safety premise is imposed on
-- aliases.
theorem reachable_issued_handles (run : RunId) (objects : ObjectId → Option Object)
    (names : Name → Option Node) (requests : List Request) :
    IssuedHandles (executeRequests (cleanAuthority run objects names) requests) := by
  have preserve : ∀ s, IssuedHandles s → IssuedHandles (executeRequests s requests) := by
    induction requests with
    | nil => intro s safe; exact safe
    | cons request rest ih => intro s safe; exact ih _ (issued_handles_step s safe request)
  apply preserve
  simp [IssuedHandles, cleanAuthority]

-- §FS-workspace.filesystem: This read uses the held description with no permission recheck.
def readIssued (s : Authority) (fd : UInt32) : Option (List UInt8) := do
  let handle ← s.handles fd
  let object ← deref s handle.ref
  return object.bytes

theorem issued_read_authorized (s : Authority) (safe : IssuedHandles s) (fd : UInt32) :
    readIssued s fd = readHandle s fd := by
  cases present : s.handles fd with
  | none => simp [readIssued, readHandle, present]
  | some handle =>
    obtain ⟨object, found, readable, _⟩ := safe fd handle present
    simp [readIssued, readHandle, present, found, readable]

-- §AR-workspace.proofs: Arbitrary reachable raw reads expose only runtime or this run's workspace.
theorem reachable_unguarded_read (run : RunId) (objects : ObjectId → Option Object)
    (names : Name → Option Node) (requests : List Request) (fd : UInt32) (bytes : List UInt8)
    (read : readIssued (executeRequests (cleanAuthority run objects names) requests) fd = some bytes) :
    ∃ handle object,
      (executeRequests (cleanAuthority run objects names) requests).handles fd = some handle ∧
      deref (executeRequests (cleanAuthority run objects names) requests) handle.ref = some object ∧
      readable (executeRequests (cleanAuthority run objects names) requests).run object.area = true ∧
      object.bytes = bytes := by
  rw [issued_read_authorized _ (reachable_issued_handles run objects names requests) fd] at read
  exact read_requires_authority _ fd bytes read

-- §FS-workspace.filesystem: Writes also use the issued open mode, without a fresh ownership check.
def writeIssued (s : Authority) (fd : UInt32) (bytes : List UInt8) : Authority :=
  match s.handles fd with
  | none => s
  | some handle =>
    match deref s handle.ref with
    | none => s
    | some object =>
      if handle.write then { s with objects := fun n =>
        if n = handle.ref.object then some { object with bytes } else s.objects n }
      else s

theorem issued_write_authorized (s : Authority) (safe : IssuedHandles s)
    (fd : UInt32) (bytes : List UInt8) : writeIssued s fd bytes = writeHandle s fd bytes := by
  cases present : s.handles fd with
  | none => simp [writeIssued, writeHandle, present]
  | some handle =>
    obtain ⟨object, found, _, write⟩ := safe fd handle present
    cases mode : handle.write with
    | false => simp [writeIssued, writeHandle, present, found, mode]
    | true => simp [writeIssued, writeHandle, present, found, mode, write mode]

theorem issued_write_preserves_protected (s : Authority) (safe : IssuedHandles s)
    (fd : UInt32) (bytes : List UInt8) (id : ObjectId) (object : Object)
    (found : s.objects id = some object) (notWritable : writable s.run object.area = false) :
    (writeIssued s fd bytes).objects id = some object := by
  rw [issued_write_authorized s safe fd bytes]
  exact write_preserves_protected s fd bytes id object found notWritable

end LeanCageM3
