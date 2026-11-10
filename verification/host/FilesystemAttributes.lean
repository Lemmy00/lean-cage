import FilesystemNamespaces

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: These are individual tracked user.* attribute
-- observations/effects. They assert no byte-key pathname frame and therefore
-- apply independently of public directory lookup semantics.
structure TrackedAttributeContract (kernel : Contract) : Prop where
  attribute_value : ∀ before after request reply handle,
    kernel.step before request (some reply) after → request.op = .getAttribute →
    TrackedAttribute request.left → before.handles request.first = some handle →
    reply.1.toNat = reply.2.size → nativeError reply = false → before.attributes handle.object request.left = some reply.2
  set_attribute : ∀ before after request reply handle,
    kernel.step before request (some reply) after → request.op = .setAttribute →
    TrackedAttribute request.left → before.handles request.first = some handle → reply.1 = 0 → reply.2 = .empty →
    after.attributes handle.object request.left = some request.right
  existing_attribute : ∀ before after request observed handle value,
    kernel.step before request observed after → request.op = .setAttribute →
    TrackedAttribute request.left → before.handles request.first = some handle →
    before.attributes handle.object request.left = some value → after.attributes handle.object request.left = some value
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

theorem NamespaceContract.attributes {kernel : Contract} (legacy : NamespaceContract kernel) :
    TrackedAttributeContract kernel :=
  ⟨legacy.attribute_value, legacy.set_attribute, legacy.existing_attribute, legacy.attribute_other, legacy.attribute_passive⟩

end LeanCage.Host.Kernel
