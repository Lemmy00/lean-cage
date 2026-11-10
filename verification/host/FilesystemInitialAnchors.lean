import FilesystemPrimitiveParents
import FilesystemNamespaceState

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: These are initialized lifetime identities, including the
-- mounted visible /tmp object. A mount cover is not identified with its underlying dentry.
structure TemporaryAnchor (initial : World) where
  root : ObjectId
  entry : ObjectId
  visible : ObjectId
  rootInitial : initial.allocated root = true
  entryInitial : initial.allocated entry = true
  visibleInitial : initial.allocated visible = true
  bound : initial.entries root "tmp".toUTF8 = some entry

def TemporaryAnchor.At {initial : World} (anchor : TemporaryAnchor initial) (world : World) : Prop :=
  world.entries anchor.root "tmp".toUTF8 = some anchor.entry

-- §AR-host-boundary.primitives: This is one openat's resolution under the fixed initial root
-- and mount view. Its premise names only the system anchor, not a request's future child path.
structure TemporaryLookupContract (kernel : Contract) {initial : World}
    (anchor : TemporaryAnchor initial) : Prop where
  opened : ∀ before after reply fd handle,
    kernel.step before {op := .openAt, first := cwd, second := directoryFlags, left := "/tmp".toUTF8}
      (some reply) after → anchor.At before → descriptor reply = some fd →
    after.handles fd = some handle → handle.object = anchor.visible

theorem temporary_anchor_initial {initial : World} (anchor : TemporaryAnchor initial) :
    anchor.At initial := anchor.bound

-- §FS-host-boundary.ownership: A real open bound to that initial visible lifetime is public
-- in every derived family graph; this does not depend on the caller's effective UID.
theorem temporary_anchor_open_public {kernel : Contract} {initial before after : World}
    {anchor : TemporaryAnchor initial} (lookup : TemporaryLookupContract kernel anchor)
    {family : Family} {dataObjects : ObjectId → Prop}
    (graph : FamilyGraph before family initial.allocated dataObjects)
    {reply : Reply} {fd : UInt64} {handle : Handle}
    (actual : kernel.step before {op := .openAt, first := cwd, second := directoryFlags, left := "/tmp".toUTF8}
      (some reply) after) (atAnchor : anchor.At before) (opened : descriptor reply = some fd)
    (live : after.handles fd = some handle) : family handle.object = none := by
  have same := lookup.opened _ _ _ _ _ actual atAnchor opened live
  rw [same]
  exact family_initial_public graph anchor.visible anchor.visibleInitial

-- §FS-host-boundary.ownership: This producer retains the exact open occurrence and current
-- OFD. The prefix custody fold supplies anchor state at that occurrence, rather than an FD role.
theorem primitive_run_parent_anchor {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request}
    (descriptors : DescriptorContract kernel) (anchor : TemporaryAnchor initial)
    (lookup : TemporaryLookupContract kernel anchor)
    (source : PrimitiveRunParent runtime initial ticks tick actor engine request)
    (snapshots : ∀ ordinal reply before after,
      SourceReturnAt runtime ticks actor ordinal Reply
        (.filesystem {op := .openAt, first := cwd, second := directoryFlags, left := "/tmp".toUTF8})
        reply before after → anchor.At before)
    {family : Family} {dataObjects : ObjectId → Prop}
    (graph : FamilyGraph tick.before.shared family initial.allocated dataObjects) :
    ∃ parent, engine.references request.first = some parent ∧ parent.rawOwned = true ∧
      parent.object = anchor.visible ∧ family parent.object = none := by
  obtain ⟨opening, live⟩ := primitive_run_parent_open descriptors source
  have same := lookup.opened _ _ _ _ _ opening.actual
    (snapshots _ _ _ _ opening.sampled) opening.recognized opening.live
  refine ⟨opening.handle, live, opening.raw, same, ?_⟩
  rw [same]
  exact family_initial_public graph anchor.visible anchor.visibleInitial

-- §FS-host-boundary.ownership: Exact source bytes compose the per-run path after selecting
-- the system anchor. Randomness is not an assumption that a new name succeeds or is unique.
def TemporaryChildPath (name : ByteArray) : ByteArray :=
  "/tmp/".toUTF8 ++ name

structure TemporaryChildAt {initial : World} (anchor : TemporaryAnchor initial)
    (world : World) (name : ByteArray) (object : ObjectId) : Prop where
  system : anchor.At world
  component : Directories.component name = true
  reserved : PrivateNames.reservedBytes name = true
  bound : world.entries anchor.visible name = some object
  young : initial.allocated object = false

-- §FS-host-boundary.ownership: The kernel cannot install a post-initialization mount cover
-- at this fresh child's lifetime under the initialized mount profile.
theorem temporary_child_data_path {initial world : World} {anchor : TemporaryAnchor initial}
    {dataObjects : ObjectId → Prop} {name : ByteArray} {object : ObjectId}
    (child : TemporaryChildAt anchor world name object) :
    DataPath world initial.allocated dataObjects anchor.root ["tmp".toUTF8, name] object := by
  exact .next (.inr (.inl anchor.visibleInitial)) (.next (.inl child.bound) (.here _))

end LeanCage.Host.Kernel
