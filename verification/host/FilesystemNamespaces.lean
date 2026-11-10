import FilesystemPermissions
import FilesystemBorrowing

namespace LeanCage.Host.Kernel
open Filesystem

def ComponentRequest (request : Request) : Prop :=
  match request.op with
  | .openAt => request.second = newFileFlags → Directories.component request.left = true
  | .mkdirAt | .unlinkAt => Directories.component request.left = true
  | .renameNew => Directories.component request.left = true ∧ Directories.component request.right = true
  | .temporary => False
  | _ => True

def NamesEntry (world : World) (fd : UInt64) (name : ByteArray) (parent : ObjectId) (component : ByteArray) : Prop :=
  ∃ handle, world.handles fd = some handle ∧ handle.object = parent ∧ name = component

def TouchesEntry (world : World) (request : Request) (parent : ObjectId) (name : ByteArray) : Prop :=
  match request.op with
  | .openAt => request.second = newFileFlags ∧ NamesEntry world request.first request.left parent name
  | .mkdirAt | .unlinkAt => NamesEntry world request.first request.left parent name
  | .renameNew => NamesEntry world request.first request.left parent name ∨
      NamesEntry world request.second request.right parent name
  | .temporary => True
  | _ => False

def TrackedAttribute (name : ByteArray) : Prop :=
  name = PrivateNames.attributeName ∨ name = Publication.attributeName

-- §AR-host-boundary.primitives: Namespace effects refer to one actual parent/component operation.
structure NamespaceContract (kernel : Contract) : Prop where
  entry_frame : ∀ before after request observed parent name,
    kernel.step before request observed after → ComponentRequest request →
    ¬ TouchesEntry before request parent name → after.entries parent name = before.entries parent name
  nonremoving_entry : ∀ before after request observed parent name object,
    kernel.step before request observed after → ComponentRequest request →
    request.op ≠ .unlinkAt → request.op ≠ .renameNew →
    before.entries parent name = some object → after.entries parent name = some object
  rename_other_source : ∀ before after request observed parent name object,
    kernel.step before request observed after → request.op = .renameNew → ComponentRequest request →
    before.entries parent name = some object → ¬ NamesEntry before request.first request.left parent name →
    after.entries parent name = some object
  open_dot : ∀ before after request reply parent fd,
    kernel.step before request (some reply) after → request.op = .openAt →
    request.second = directoryFlags → before.handles request.first = some parent →
    request.left = ".".toUTF8 → descriptor reply = some fd →
    ∃ handle, after.handles fd = some handle ∧ handle.object = parent.object
  exclusive_component : ∀ before after request reply parent fd,
    kernel.step before request (some reply) after → request.op = .openAt →
    request.second = newFileFlags → before.handles request.first = some parent →
    Directories.component request.left = true → descriptor reply = some fd →
    ∃ object, before.entries parent.object request.left = none ∧
      after.entries parent.object request.left = some object ∧ after.contents object = .empty ∧
      ∃ handle, after.handles fd = some handle ∧ handle.object = object
  attribute_value : ∀ before after request reply handle,
    kernel.step before request (some reply) after → request.op = .getAttribute →
    TrackedAttribute request.left → before.handles request.first = some handle → reply.1.toNat = reply.2.size → nativeError reply = false →
    before.attributes handle.object request.left = some reply.2
  set_attribute : ∀ before after request reply handle,
    kernel.step before request (some reply) after → request.op = .setAttribute →
    TrackedAttribute request.left → before.handles request.first = some handle → reply.1 = 0 → reply.2 = .empty →
    after.attributes handle.object request.left = some request.right
  existing_attribute : ∀ before after request observed handle value,
    kernel.step before request observed after → request.op = .setAttribute →
    TrackedAttribute request.left → before.handles request.first = some handle → before.attributes handle.object request.left = some value →
    after.attributes handle.object request.left = some value
  attribute_other : ∀ before after request observed handle object name,
    kernel.step before request observed after → request.op = .setAttribute →
    TrackedAttribute request.left → TrackedAttribute name → before.handles request.first = some handle →
    (object ≠ handle.object ∨ name ≠ request.left) → after.attributes object name = before.attributes object name
  attribute_passive : ∀ before after request observed object name,
    kernel.step before request observed after → request.op ≠ .setAttribute → TrackedAttribute name →
    before.allocated object = true →
    ((∃ fd handle, after.handles fd = some handle ∧ handle.object = object) ∨
      ∃ parent component, after.entries parent component = some object) →
    after.attributes object name = before.attributes object name

-- §AR-host-boundary.primitives: Existing mount aliases are distinct from underlying directory
-- entries.
structure MountContract (kernel : Contract) (initialObjects : ObjectId → Bool) : Prop where
  open_directory_child : ∀ before after request reply parent fd child,
    kernel.step before request (some reply) after → request.op = .openAt →
    request.second = directoryFlags → before.handles request.first = some parent →
    descriptor reply = some fd → Directories.component request.left = true →
    request.left ≠ ".".toUTF8 → request.left ≠ "..".toUTF8 →
    before.entries parent.object request.left = some child →
    ∃ handle, after.handles fd = some handle ∧
      (handle.object = child ∨ (initialObjects child = true ∧ initialObjects handle.object = true))

-- §FS-host-boundary.ownership: A post-initialization birth cannot be a pre-existing mount cover.
theorem fresh_directory_lookup {kernel : Contract} {initialObjects : ObjectId → Bool}
    (mounts : MountContract kernel initialObjects) {before after : World}
    {request : Request} {reply : Reply} {parent : Handle} {fd : UInt64} {object : ObjectId}
    (step : kernel.step before request (some reply) after) (opening : request.op = .openAt)
    (flags : request.second = directoryFlags) (parentLive : before.handles request.first = some parent)
    (opened : descriptor reply = some fd) (component : Directories.component request.left = true)
    (notDot : request.left ≠ ".".toUTF8) (notUp : request.left ≠ "..".toUTF8)
    (bound : before.entries parent.object request.left = some object) (fresh : initialObjects object = false) :
    ∃ handle, after.handles fd = some handle ∧ handle.object = object := by
  obtain ⟨handle, live, underlying | covered⟩ := mounts.open_directory_child
    _ _ _ _ _ _ _ step opening flags parentLive opened component notDot notUp bound
  · exact ⟨handle, live, underlying⟩
  · rw [fresh] at covered
    cases covered.1

-- §FS-host-boundary.ownership: A passive namespace syscall cannot remove a retained child binding.
theorem untouched_entry {kernel : Contract} (namespaceLaws : NamespaceContract kernel)
    {before after : World} {request : Request} {observed : Option Reply} {parent child : ObjectId} {name : ByteArray}
    (step : kernel.step before request observed after) (component : ComponentRequest request)
    (untouched : ¬ TouchesEntry before request parent name) (bound : before.entries parent name = some child) :
    after.entries parent name = some child := by
  rw [namespaceLaws.entry_frame _ _ _ _ _ _ step component untouched]
  exact bound

end LeanCage.Host.Kernel
