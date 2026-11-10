import FilesystemNativeDecoding

namespace LeanCage.Host.NativeCode

def encodeHandle (handle : Kernel.Handle) : Handle :=
  ⟨handle.object, handle.description, handle.flags.toNat, handle.rawOwned⟩

def handle? (handle : Handle) : Option Kernel.Handle := do
  let flags ← word? handle.flags
  return ⟨handle.object, handle.description, flags, handle.rawOwned⟩

@[simp] theorem handle_roundtrip (handle : Kernel.Handle) : handle? (encodeHandle handle) = some handle := by
  cases handle
  simp [handle?, encodeHandle]

theorem handle_exact {code : Handle} {handle : Kernel.Handle} (accepted : handle? code = some handle) :
    encodeHandle handle = code := by
  cases code with
  | mk object description flags rawOwned =>
    simp only [handle?] at accepted
    cases parsed : word? flags with
    | none => simp [parsed] at accepted
    | some actual =>
      simp [parsed] at accepted
      cases accepted
      simp only [encodeHandle, (word_exact parsed).1]

def encodeReferences (references : Kernel.NativeReferences) : References :=
  { handles := fun fd =>
      if fd < 2 ^ 64 then (references.handles (UInt64.ofNat fd)).map encodeHandle else none
    closeOnExec := fun fd => if fd < 2 ^ 64 then references.closeOnExec (UInt64.ofNat fd) else false
    workingDirectory := references.workingDirectory }

def decodeReferences (references : References) : Kernel.NativeReferences :=
  { handles := fun fd => (references.handles fd.toNat).bind handle?
    closeOnExec := fun fd => references.closeOnExec fd.toNat
    workingDirectory := references.workingDirectory }

-- §AR-host-boundary.primitives: These bounds concern representation, not permission or custody.
def ReferencesBounded (references : References) : Prop :=
  ∀ fd handle, fd < 2 ^ 64 → references.handles fd = some handle → handle.flags < 2 ^ 64

structure ReferencesInterpret (code : References) (references : Kernel.NativeReferences) : Prop where
  handles : ∀ fd, (references.handles fd).map encodeHandle = code.handles fd.toNat
  closeExec : ∀ fd, references.closeOnExec fd = code.closeOnExec fd.toNat
  directory : references.workingDirectory = code.workingDirectory

@[simp] theorem references_roundtrip (references : Kernel.NativeReferences) :
    decodeReferences (encodeReferences references) = references := by
  cases references with
  | mk handles closeExec workingDirectory =>
    change Kernel.NativeReferences.mk _ _ _ = Kernel.NativeReferences.mk _ _ _
    congr 1
    · funext fd
      simp only [encodeReferences, UInt64.toNat_lt, ↓reduceIte,
        UInt64.ofNat_toNat]
      cases handles fd <;> simp [handle_roundtrip]
    · funext fd
      simp only [encodeReferences, UInt64.toNat_lt, ↓reduceIte,
        UInt64.ofNat_toNat]

-- §FS-host-boundary.ownership: A decoded snapshot preserves every actual bounded FD entry/OFD,
-- including capabilities outside this request and the parent's retained CWD.
theorem references_decode_exact (code : References) (bounded : ReferencesBounded code) :
    ReferencesInterpret code (decodeReferences code) := by
  refine ⟨?_, fun _ => rfl, rfl⟩
  intro fd
  cases selected : code.handles fd.toNat with
  | none => simp only [decodeReferences, selected, Option.bind_none, Option.map_none]
  | some handle =>
    have bound := bounded _ _ fd.toNat_lt selected
    have encoded : encodeHandle
        ⟨handle.object, handle.description, UInt64.ofNat handle.flags, handle.rawOwned⟩ = handle := by
      cases handle
      simp only [encodeHandle, UInt64.toNat_ofNat_of_lt' bound]
    simp only [decodeReferences, selected, handle?, word?, bound, ↓reduceIte,
      bind, Option.bind, pure, Option.map_some, encoded]

theorem handle_encoding_injective : Function.Injective encodeHandle := by
  intro first second same
  have parsed := congrArg handle? same
  simpa only [handle_roundtrip, Option.some.injEq] using parsed

theorem references_interpret_unique {code : References} {first second : Kernel.NativeReferences}
    (initial : ReferencesInterpret code first) (final : ReferencesInterpret code second) : first = second := by
  have sameHandles : first.handles = second.handles := by
    funext fd
    have same := (initial.handles fd).trans (final.handles fd).symm
    cases before : first.handles fd with
    | none =>
      cases after : second.handles fd with
      | none => rfl
      | some handle => simp only [before, after, Option.map_none, Option.map_some] at same; cases same
    | some handle =>
      cases after : second.handles fd with
      | none => simp only [before, after, Option.map_none, Option.map_some] at same; cases same
      | some next =>
        have objects : encodeHandle handle = encodeHandle next := by
          simpa only [before, after, Option.map_some, Option.some.injEq] using same
        exact congrArg some (handle_encoding_injective objects)
  have sameFlags : first.closeOnExec = second.closeOnExec := by
    funext fd
    exact (initial.closeExec fd).trans (final.closeExec fd).symm
  have sameDirectory := initial.directory.trans final.directory.symm
  cases first
  cases second
  cases sameHandles
  cases sameFlags
  cases sameDirectory
  rfl

def encodeCredentials (caller : Kernel.Credentials) : Credentials :=
  ⟨caller.uid, caller.groups, caller.bypassDac, caller.bypassOwner⟩

def decodeCredentials (caller : Credentials) : Kernel.Credentials :=
  ⟨caller.uid, caller.groups, caller.bypassDac, caller.bypassOwner⟩

theorem credentials_roundtrip (caller : Kernel.Credentials) :
    decodeCredentials (encodeCredentials caller) = caller := by cases caller; rfl

theorem credentials_exact (caller : Credentials) : encodeCredentials (decodeCredentials caller) = caller := by
  cases caller
  rfl

end LeanCage.Host.NativeCode
