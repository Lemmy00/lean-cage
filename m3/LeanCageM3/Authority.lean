import LeanCageM2.Model

namespace LeanCageM3

-- §AR-workspace.interfaces: Object generations distinguish aliases from recycled machine
-- identities.
abbrev RunId := UInt64
abbrev ObjectId := UInt64

inductive Area where
  | runtime | workspace (run : RunId) | outside
  deriving DecidableEq, Repr

structure Object where
  generation : UInt64
  area : Area
  bytes : List UInt8 := []
  deriving DecidableEq, Repr

structure Ref where
  object : ObjectId
  generation : UInt64
  deriving DecidableEq, Repr

structure Handle where
  ref : Ref
  write : Bool
  deriving DecidableEq, Repr

-- §FS-workspace.filesystem: Names and open descriptions are separate; unlink cannot revoke a
-- handle.
abbrev Name := List UInt8

inductive Node where
  | object (ref : Ref)
  | symlink (target : Name)
  deriving DecidableEq, Repr

structure Authority where
  run : RunId
  objects : ObjectId → Option Object
  names : Name → Option Node
  handles : UInt32 → Option Handle

def readable (run : RunId) (area : Area) : Bool :=
  match area with
  | .runtime => true
  | .workspace owner => owner == run
  | .outside => false

def writable (run : RunId) (area : Area) : Bool := area == .workspace run

def deref (s : Authority) (ref : Ref) : Option Object := do
  let object ← s.objects ref.object
  if object.generation == ref.generation then some object else none

-- §FS-workspace.filesystem: Cyclic and dangling symlinks fail; object permission is checked after
-- lookup.
def resolve (names : Name → Option Node) : Nat → Name → Option Ref
  | 0, _ => none
  | fuel + 1, name => do
    match ← names name with
    | .object ref => some ref
    | .symlink target => resolve names fuel target

def validFd (fd : UInt32) : Bool := 3 ≤ fd && fd ≤ 0x7fffffff

def openObject (s : Authority) (ref : Ref) (fd : UInt32) (write : Bool) : Authority :=
  match deref s ref with
  | none => s
  | some object =>
    if validFd fd && readable s.run object.area && (!write || writable s.run object.area) then
      { s with handles := fun n => if n = fd then some ⟨ref, write⟩ else s.handles n }
    else s

def openName (s : Authority) (name : Name) (fd : UInt32) (write : Bool) : Authority :=
  match resolve s.names 40 name with
  | none => s
  | some ref => openObject s ref fd write

def dupHandle (s : Authority) (source target : UInt32) : Authority :=
  if validFd target then
    { s with handles := fun n => if n = target then s.handles source else s.handles n }
  else s

def closeHandle (s : Authority) (fd : UInt32) : Authority :=
  { s with handles := fun n => if n = fd then none else s.handles n }

def readHandle (s : Authority) (fd : UInt32) : Option (List UInt8) := do
  let h ← s.handles fd
  let object ← deref s h.ref
  if readable s.run object.area then some object.bytes else none

-- §FS-workspace.authority: The local write contract checks object ownership and open-mode rights.
def writeHandle (s : Authority) (fd : UInt32) (bytes : List UInt8) : Authority :=
  match s.handles fd with
  | none => s
  | some handle =>
    match deref s handle.ref with
    | none => s
    | some object =>
      if handle.write && writable s.run object.area then
        { s with objects := fun n =>
            if n = handle.ref.object then some { object with bytes } else s.objects n }
      else s

-- §FS-workspace.filesystem: Guest names may alias arbitrary names; resolution never grants object
-- rights.
def setName (s : Authority) (name : Name) (node : Option Node) : Authority :=
  { s with names := fun n => if n = name then node else s.names n }

def renameName (s : Authority) (source target : Name) : Authority :=
  if source = target then s else setName (setName s source none) target (s.names source)

-- §FS-workspace.filesystem: Ordinary host/sibling writes remain explicit interference.
def externalWrite (s : Authority) (id : ObjectId) (bytes : List UInt8) : Authority :=
  match s.objects id with
  | none => s
  | some object =>
    if object.area == .outside || (match object.area with
        | .workspace other => other != s.run
        | _ => false) then
      { s with objects := fun n => if n = id then some { object with bytes } else s.objects n }
    else s

-- §FS-workspace.filesystem: Allocation uses an unused object identity; open aliases keep old
-- objects live.
def allocateObject (s : Authority) (id : ObjectId) (generation : UInt64)
    (bytes : List UInt8) : Authority :=
  if s.objects id = none then
    { s with objects := fun n => if n = id then some ⟨generation, .workspace s.run, bytes⟩
      else s.objects n }
  else s

-- §AR-workspace.interfaces: Hostile attempts stay explicit even when their local effect is denied.
inductive Request where
  | open (name : Name) (fd : UInt32) (write : Bool)
  | dup (source target : UInt32)
  | close (fd : UInt32)
  | write (fd : UInt32) (bytes : List UInt8)
  | alias (name : Name) (node : Option Node)
  | rename (source target : Name)
  | external (id : ObjectId) (bytes : List UInt8)
  | allocate (id : ObjectId) (generation : UInt64) (bytes : List UInt8)
  | deniedExternal

def authorityStep (s : Authority) : Request → Authority
  | .open name fd write => openName s name fd write
  | .dup source target => dupHandle s source target
  | .close fd => closeHandle s fd
  | .write fd bytes => writeHandle s fd bytes
  | .alias name node => setName s name node
  | .rename source target => renameName s source target
  | .external id bytes => externalWrite s id bytes
  | .allocate id generation bytes => allocateObject s id generation bytes
  | .deniedExternal => s

def GuestRequest : Request → Prop
  | .external _ _ => False
  | _ => True

def HandlesSafe (s : Authority) : Prop :=
  ∀ fd h object, s.handles fd = some h → deref s h.ref = some object →
    readable s.run object.area = true ∧ (h.write = true → writable s.run object.area = true)

-- §AR-workspace.proofs: Inherited malicious handles are removed, not assumed safe in the input.
def cleanAuthority (run : RunId) (objects : ObjectId → Option Object)
    (names : Name → Option Node) : Authority :=
  ⟨run, objects, names, fun _ => none⟩

theorem clean_handles_safe (run : RunId) (objects : ObjectId → Option Object)
    (names : Name → Option Node) : HandlesSafe (cleanAuthority run objects names) := by
  simp [HandlesSafe, cleanAuthority]

-- §AR-workspace.proofs: This statement ranges over every requested fd and notWritable object.
theorem write_preserves_protected (s : Authority) (fd : UInt32) (bytes : List UInt8)
    (id : ObjectId) (object : Object) (found : s.objects id = some object)
    (notWritable : writable s.run object.area = false) :
    (writeHandle s fd bytes).objects id = some object := by
  unfold writeHandle
  split
  · exact found
  · split
    · exact found
    · rename_i handle hh target ht
      split
      · rename_i allowed
        simp only [Bool.and_eq_true] at allowed
        dsimp
        split
        · rename_i same
          have sameObject : object = target := by
            unfold deref at ht
            rw [← same, found] at ht
            dsimp at ht
            split at ht <;> simp_all
          subst target
          simp [notWritable] at allowed
        · exact found
      · exact found

-- §AR-workspace.proofs: Name tricks, dup, unlink and fresh allocation cannot modify a notWritable
-- object.
theorem guest_preserves_protected (s : Authority) (request : Request) (guest : GuestRequest request)
    (id : ObjectId) (object : Object) (found : s.objects id = some object)
    (notWritable : writable s.run object.area = false) :
    (authorityStep s request).objects id = some object := by
  cases request with
  | «open» name fd write =>
    simp only [authorityStep, openName]
    split
    · exact found
    · unfold openObject
      split
      · exact found
      · split <;> exact found
  | dup source target => simp only [authorityStep, dupHandle]; split <;> exact found
  | close fd => exact found
  | write fd bytes => exact write_preserves_protected s fd bytes id object found notWritable
  | alias name node => exact found
  | rename source target => simp only [authorityStep, renameName]; split <;> exact found
  | external target bytes => exact False.elim guest
  | allocate target generation bytes =>
    simp only [authorityStep, allocateObject]
    split
    · rename_i fresh
      dsimp
      split
      · rename_i same
        subst target
        simp [found] at fresh
      · exact found
    · exact found
  | deniedExternal => exact found

theorem authority_owner_persists (s : Authority) (request : Request) :
    (authorityStep s request).run = s.run := by
  cases request <;> simp only [authorityStep]
  · unfold openName; split
    · rfl
    · unfold openObject; split
      · rfl
      · split <;> rfl
  · unfold dupHandle; split <;> rfl
  · rfl
  · unfold writeHandle; split
    · rfl
    · split
      · rfl
      · split <;> rfl
  · rfl
  · unfold renameName; split <;> rfl
  · unfold externalWrite; split
    · rfl
    · split <;> split <;> rfl
  · unfold allocateObject; split <;> rfl

def executeRequests (s : Authority) : List Request → Authority
  | [] => s
  | request :: rest => executeRequests (authorityStep s request) rest

-- §AR-workspace.proofs: Universal finite guest traces; this does not erase permitted outside
-- writes.
theorem guest_trace_preserves_protected (s : Authority) (requests : List Request)
    (guest : ∀ request ∈ requests, GuestRequest request)
    (id : ObjectId) (object : Object) (found : s.objects id = some object)
    (notWritable : writable s.run object.area = false) :
    (executeRequests s requests).objects id = some object := by
  induction requests generalizing s with
  | nil => exact found
  | cons request rest ih =>
    apply ih (authorityStep s request)
    · intro r hr; exact guest r (List.mem_cons_of_mem request hr)
    · exact guest_preserves_protected s request (guest request (by simp)) id object found notWritable
    · simpa only [authority_owner_persists] using notWritable

-- §FS-workspace.observations: Even guessed/stale/forged aliases return no notWritable bytes at this
-- boundary.
theorem read_requires_authority (s : Authority) (fd : UInt32) (bytes : List UInt8)
    (read : readHandle s fd = some bytes) :
    ∃ (h : Handle) (obj : Object), s.handles fd = some h ∧ deref s h.ref = some obj ∧
      readable s.run obj.area = true ∧ obj.bytes = bytes := by
  unfold readHandle at read
  cases hh : s.handles fd with
  | none => simp [hh] at read
  | some handle =>
    cases ho : deref s handle.ref with
    | none => simp [hh, ho] at read
    | some object =>
      simp [hh, ho] at read
      exact ⟨handle, object, rfl, ho, read⟩

-- §AR-workspace.proofs: A concrete write/read/alias witness keeps the safety statement nonvacuous.
def usefulAuthority : Authority :=
  cleanAuthority 1 (fun n => if n = 7 then some ⟨1, .workspace 1, [65]⟩ else none)
    (fun name => if name = [97] then some (.object ⟨7, 1⟩) else none)

theorem useful_read_write :
    readHandle (writeHandle (openName usefulAuthority [97] 3 true) 3 [66]) 3 = some [66] := by
  decide

-- §FS-workspace.filesystem: Host interference is allowed, but it cannot modify the frozen runtime.
theorem external_preserves_runtime (s : Authority) (target : ObjectId) (bytes : List UInt8)
    (id : ObjectId) (object : Object) (found : s.objects id = some object)
    (runtime : object.area = .runtime) :
    (externalWrite s target bytes).objects id = some object := by
  unfold externalWrite
  split
  · exact found
  · rename_i obj ho
    by_cases same : id = target
    · subst target
      rw [found] at ho
      cases ho
      simp [runtime, found]
    · split <;> split <;> simp_all

theorem runtime_preserved_with_interference (s : Authority) (request : Request)
    (id : ObjectId) (object : Object) (found : s.objects id = some object)
    (runtime : object.area = .runtime) :
    (authorityStep s request).objects id = some object := by
  cases request with
  | external target bytes => exact external_preserves_runtime s target bytes id object found runtime
  | _ => apply guest_preserves_protected <;> simp_all [GuestRequest, writable]

theorem runtime_trace_preserved (s : Authority) (requests : List Request)
    (id : ObjectId) (object : Object) (found : s.objects id = some object)
    (runtime : object.area = .runtime) :
    (executeRequests s requests).objects id = some object := by
  induction requests generalizing s with
  | nil => exact found
  | cons request rest ih =>
    exact ih (authorityStep s request) (runtime_preserved_with_interference s request id object found runtime)

-- §AR-workspace.proofs: Every reachable interleaving is covered, including environment writes and
-- aliases.
theorem reachable_authority (s : Authority) (requests : List Request) (fd : UInt32) (bytes : List UInt8)
    (read : readHandle (executeRequests s requests) fd = some bytes) :
    ∃ (h : Handle) (obj : Object), (executeRequests s requests).handles fd = some h ∧
      deref (executeRequests s requests) h.ref = some obj ∧
      readable (executeRequests s requests).run obj.area = true ∧ obj.bytes = bytes :=
  read_requires_authority (executeRequests s requests) fd bytes read

end LeanCageM3
