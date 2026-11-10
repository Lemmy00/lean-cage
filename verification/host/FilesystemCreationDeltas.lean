import FilesystemByteNamespaces
import FilesystemRootCatalogue

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: This is one committed directory mutation, independent of the
-- observed acknowledgement. The source consumes it only after proving the current operands.
structure FreshDirectoryDelta (dataObjects : ObjectId → Prop) (request : Request) (before after : World) where
  parent : Handle
  object : ObjectId
  reference : before.handles request.first = some parent
  parentLive : before.allocated parent.object = true
  fresh : before.allocated object = false
  allocated : after.allocated object = true
  data : dataObjects object
  absent : before.entries parent.object request.left = none
  entries : after.entries = putBinding before.entries parent.object request.left object

theorem mkdir_delta_cases {dataObjects : ObjectId → Prop} {request : Request} {before after : World}
    (change : DataChange dataObjects request before after) (mkdir : request.op = .mkdirAt) :
    after.entries = before.entries ∨ Nonempty (FreshDirectoryDelta dataObjects request before after) := by
  cases change with
  | unchanged entries => exact .inl entries
  | created parent object operation reference parentLive fresh allocated data absent entries =>
    exact .inr ⟨⟨parent, object, reference, parentLive, fresh, allocated, data, absent, entries⟩⟩
  | removed operation entries => rw [mkdir] at operation; cases operation
  | renamed source target object operation sourceReference targetReference targetLive sourceBinding targetAbsent
      sourceGone targetBinding entries => rw [mkdir] at operation; cases operation

theorem FreshDirectoryDelta.bound {dataObjects : ObjectId → Prop} {request : Request} {before after : World}
    (delta : FreshDirectoryDelta dataObjects request before after) :
    after.entries delta.parent.object request.left = some delta.object := by
  classical
  rw [delta.entries]
  simp only [putBinding, and_self, ite_eq_left]

-- §FS-host-boundary.ownership: Exclusive creation preserves every older binding. This uses
-- the actual one-syscall delta, rather than byte-name laws for hostile public filesystems.
theorem FreshDirectoryDelta.preserves_binding {dataObjects : ObjectId → Prop} {request : Request} {before after : World}
    (delta : FreshDirectoryDelta dataObjects request before after) {parent : ObjectId} {name : ByteArray} {object : ObjectId}
    (bound : before.entries parent name = some object) : after.entries parent name = some object := by
  classical
  rw [delta.entries]
  unfold putBinding
  split
  · rename_i same
    have impossible : before.entries delta.parent.object request.left = some object := by
      simpa only [same.1, same.2] using bound
    rw [delta.absent] at impossible
    cases impossible
  · exact bound

theorem fresh_directory_register_valid {dataObjects : ObjectId → Prop} {request : Request} {before after : World}
    (delta : FreshDirectoryDelta dataObjects request before after) (actor : ActorId) {caps : Capabilities}
    (valid : caps.Valid before) (publicParent : caps.family delta.parent.object = none)
    (allocation : ∀ object, before.allocated object = true → after.allocated object = true) :
    (caps.addRoot ⟨actor, delta.object, delta.parent.object, request.left⟩).Valid after := by
  have different := birth_outside_existing_caps caps before delta.object valid delta.fresh
  have parentDifferent : delta.parent.object ≠ delta.object := by
    intro same
    have old := delta.parentLive
    rw [same, delta.fresh] at old
    cases old
  constructor
  · intro query member
    rcases List.mem_cons.mp member with rfl | old
    · exact ⟨delta.allocated, allocation _ delta.parentLive, delta.bound,
        by simp only [Capabilities.addRoot, ite_eq_left],
        by simpa only [Capabilities.addRoot, ite_eq_right parentDifferent] using publicParent⟩
    · obtain ⟨allocated, parentAllocated, bound, family, publicObject⟩ := valid.1 query old
      exact ⟨allocation _ allocated, allocation _ parentAllocated, delta.preserves_binding bound,
        by simpa only [Capabilities.addRoot, ite_eq_right (Ne.symm (different query old).1)] using family,
        by simpa only [Capabilities.addRoot, ite_eq_right (Ne.symm (different query old).2)] using publicObject⟩
  · intro first firstMember second secondMember same
    rcases List.mem_cons.mp firstMember with rfl | firstOld
    · rcases List.mem_cons.mp secondMember with rfl | secondOld
      · rfl
      · exact False.elim ((different second secondOld).1 same)
    · rcases List.mem_cons.mp secondMember with rfl | secondOld
      · exact False.elim ((different first firstOld).1 same.symm)
      · exact valid.2 first firstOld second secondOld same

-- §FS-host-boundary.ownership: The actual committed birth is entered in the catalogue even
-- when mkdir returns an error or loses its reply. It supplies no child FD or success claim.
def private_root_birth_data {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {position : Nat} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (mkdir : request.op = .mkdirAt) (mode : request.second = 448)
    (component : Directories.component request.left = true) (reserved : PrivateNames.reservedBytes request.left = true)
    {dataObjects : ObjectId → Prop}
    (delta : FreshDirectoryDelta dataObjects request (tick.before.project engine) tick.after.shared) :
    RootBirth runtime ticks ⟨actor, delta.object, delta.parent.object, request.left⟩ := {
  position, tick, selected, engine, present, request, observed, action, mkdir, mode, component, reserved
  parent := delta.parent
  reference := delta.reference
  parentObject := rfl
  name := rfl
  fresh := ⟨delta.fresh, delta.allocated⟩
  absent := delta.absent
  bound := delta.bound }

-- §AR-host-boundary.interfaces: Preserve the run/validator specialization and its exact
-- dependent receipt; the generic source-owned constructor above also serves publication.
def primitive_run_root_birth_data {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (source : PrimitiveRunParent runtime initial ticks tick actor engine request)
    {position : Nat} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) {dataObjects : ObjectId → Prop}
    (delta : FreshDirectoryDelta dataObjects request (tick.before.project engine) tick.after.shared) :
    RootBirth runtime ticks ⟨actor, delta.object, delta.parent.object, request.left⟩ := by
  exact {
    position
    tick
    selected
    engine
    present
    request
    observed
    action
    mkdir := source.mkdir
    mode := source.privateMode
    component := source.component
    reserved := source.reserved
    parent := delta.parent
    reference := delta.reference
    parentObject := rfl
    name := rfl
    fresh := ⟨delta.fresh, delta.allocated⟩
    absent := delta.absent
    bound := delta.bound }

-- §AR-host-boundary.interfaces: Keep the existing existence wrapper and expose the exact
-- constructive receipt above for dependent state/cursor composition.
theorem primitive_run_root_birth {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (source : PrimitiveRunParent runtime initial ticks tick actor engine request)
    {position : Nat} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) {dataObjects : ObjectId → Prop}
    (delta : FreshDirectoryDelta dataObjects request (tick.before.project engine) tick.after.shared) :
    Nonempty (RootBirth runtime ticks ⟨actor, delta.object, delta.parent.object, request.left⟩) :=
  ⟨primitive_run_root_birth_data source selected action present delta⟩

end LeanCage.Host.Kernel
