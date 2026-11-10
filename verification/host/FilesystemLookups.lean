import FilesystemFamilies
import FilesystemCreationSources

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: Data entries and initialized mount covers are separate views.
structure DataLookupContract (kernel : Contract) (initialObjects : ObjectId → Bool)
    (dataObjects : ObjectId → Prop) : Prop where
  child : ∀ before after request reply parent fd handle,
    kernel.step before request (some reply) after → request.op = .openAt →
    (request.second = directoryFlags ∨ request.second = readFlags) →
    before.handles request.first = some parent → descriptor reply = some fd → after.handles fd = some handle →
    Directories.component request.left = true → request.left ≠ ".".toUTF8 → request.left ≠ "..".toUTF8 →
    dataObjects handle.object → before.entries parent.object request.left = some handle.object ∨
      initialObjects handle.object = true
  parent : ∀ before after request reply current fd handle,
    kernel.step before request (some reply) after → request.op = .openAt → request.second = directoryFlags →
    before.handles request.first = some current → request.left = "..".toUTF8 →
    descriptor reply = some fd → after.handles fd = some handle → dataObjects handle.object →
    handle.object = current.object ∨ initialObjects handle.object = true ∨
      ∃ name, before.entries handle.object name = some current.object
  root : ∀ before after request reply fd handle,
    kernel.step before request (some reply) after → request.op = .openAt → request.second = directoryFlags →
    request.first = cwd → request.left = "/".toUTF8 → descriptor reply = some fd →
    after.handles fd = some handle → initialObjects handle.object = true
  cwd : ∀ before after request reply fd handle,
    kernel.step before request (some reply) after → request.op = .openAt → request.second = directoryFlags →
    request.first = Filesystem.cwd → request.left = ".".toUTF8 → descriptor reply = some fd →
    after.handles fd = some handle → handle.object = before.workingDirectory

-- §FS-host-boundary.ownership: A checked public component cannot enter a private data family.
theorem public_child_lookup {kernel : Contract} {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (lookup : DataLookupContract kernel initialObjects dataObjects)
    {before after : World} {family : Family} (graph : FamilyGraph before family initialObjects dataObjects)
    {request : Request} {reply : Reply} {parent handle : Handle} {fd : UInt64}
    (actual : kernel.step before request (some reply) after) (opening : request.op = .openAt)
    (flags : request.second = directoryFlags ∨ request.second = readFlags)
    (parentLive : before.handles request.first = some parent) (opened : descriptor reply = some fd)
    (live : after.handles fd = some handle) (component : Directories.component request.left = true)
    (notDot : request.left ≠ ".".toUTF8) (notUp : request.left ≠ "..".toUTF8)
    (publicParent : family parent.object = none) (publicName : PrivateNames.reservedBytes request.left = false) :
    family handle.object = none := by
  cases privateObject : family handle.object with
  | none => rfl
  | some scope =>
    have data := graph.data handle.object scope privateObject
    rcases lookup.child _ _ _ _ _ _ _ actual opening flags parentLive opened live component notDot notUp data
      with bound | mounted
    · rcases graph.border parent.object request.left handle.object scope bound privateObject with privateParent | reserved
      · rw [publicParent] at privateParent; cases privateParent
      · rw [publicName] at reserved; cases reserved.1
    · have young := graph.young handle.object scope privateObject
      rw [mounted] at young
      cases young

theorem public_parent_lookup {kernel : Contract} {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (lookup : DataLookupContract kernel initialObjects dataObjects)
    {before after : World} {family : Family} (graph : FamilyGraph before family initialObjects dataObjects)
    {request : Request} {reply : Reply} {current handle : Handle} {fd : UInt64}
    (actual : kernel.step before request (some reply) after) (opening : request.op = .openAt)
    (flags : request.second = directoryFlags) (currentLive : before.handles request.first = some current)
    (up : request.left = "..".toUTF8) (opened : descriptor reply = some fd) (live : after.handles fd = some handle)
    (publicCurrent : family current.object = none) : family handle.object = none := by
  cases privateObject : family handle.object with
  | none => rfl
  | some scope =>
    rcases lookup.parent _ _ _ _ _ _ _ actual opening flags currentLive up opened live
      (graph.data handle.object scope privateObject) with same | mounted | ⟨name, entry⟩
    · rw [same, publicCurrent] at privateObject; cases privateObject
    · have young := graph.young handle.object scope privateObject; rw [mounted] at young; cases young
    · have privateCurrent := graph.descendants handle.object name current.object scope entry privateObject
      rw [publicCurrent] at privateCurrent
      cases privateCurrent

def rawComponents (bytes : ByteArray) : List ByteArray :=
  ((bytes.data.toList.splitOn 47).filter (fun part => !part.isEmpty)).map (fun part => ByteArray.mk part.toArray)

-- §AR-host-boundary.primitives: This is the unvalidated byte path returned by getcwd.
inductive DataPath (world : World) (initialObjects : ObjectId → Bool) (dataObjects : ObjectId → Prop) :
    ObjectId → List ByteArray → ObjectId → Prop where
  | here (object : ObjectId) : DataPath world initialObjects dataObjects object [] object
  | next {parent child target : ObjectId} {name : ByteArray} {rest : List ByteArray}
      (entry : world.entries parent name = some child ∨ initialObjects child = true ∨ ¬ dataObjects child)
      (following : DataPath world initialObjects dataObjects child rest target) :
      DataPath world initialObjects dataObjects parent (name :: rest) target

-- §AR-host-boundary.primitives: Absolute internal opens still resolve actual root/data bindings.
structure AbsoluteLookupContract (kernel : Contract) (initialObjects : ObjectId → Bool)
    (dataObjects : ObjectId → Prop) : Prop where
  path : ∀ before after request reply fd handle,
    kernel.step before request (some reply) after → request.op = .openAt →
    request.second = directoryFlags → request.first = cwd → request.left[0]! = 47 →
    descriptor reply = some fd → after.handles fd = some handle → dataObjects handle.object →
    ∃ root, initialObjects root = true ∧
      DataPath before initialObjects dataObjects root (rawComponents request.left) handle.object

structure WorkingDirectoryContract (kernel : Contract) (initialObjects : ObjectId → Bool)
    (dataObjects : ObjectId → Prop) : Prop where
  spelling : ∀ before after request reply,
    kernel.step before request (some reply) after → request.op = .workingDirectory → reply.1 = 0 →
    reply.2.isEmpty = false → reply.2[0]! = 47 →
    ∃ root, initialObjects root = true ∧
      DataPath before initialObjects dataObjects root (rawComponents reply.2) before.workingDirectory

theorem data_path_public {world : World} {family : Family} {initialObjects : ObjectId → Bool}
    {dataObjects : ObjectId → Prop} (graph : FamilyGraph world family initialObjects dataObjects)
    {parent target : ObjectId} {names : List ByteArray}
    (path : DataPath world initialObjects dataObjects parent names target)
    (publicParent : family parent = none) (checked : ∀ name ∈ names, PrivateNames.reservedBytes name = false) :
    family target = none := by
  induction path with
  | here => exact publicParent
  | @next parent child target name rest entry following ih =>
    apply ih _ (fun name member => checked name (by simp [member]))
    cases childLabel : family child with
    | none => rfl
    | some scope =>
      rcases entry with direct | mounted | untracked
      · rcases graph.border parent name child scope direct childLabel with privateParent | reserved
        · rw [publicParent] at privateParent; cases privateParent
        · rw [checked name (by simp)] at reserved; cases reserved.1
      · have young := graph.young child scope childLabel; rw [mounted] at young; cases young
      · exact False.elim (untracked (graph.data child scope childLabel))

theorem absolute_lookup_public {kernel : Contract} {initialObjects : ObjectId → Bool}
    {dataObjects : ObjectId → Prop} (contract : AbsoluteLookupContract kernel initialObjects dataObjects)
    {before after : World} {family : Family} (graph : FamilyGraph before family initialObjects dataObjects)
    {request : Request} {reply : Reply} {fd : UInt64} {handle : Handle}
    (actual : kernel.step before request (some reply) after) (operation : request.op = .openAt)
    (flags : request.second = directoryFlags) (relative : request.first = cwd)
    (absolute : request.left[0]! = 47) (opened : descriptor reply = some fd)
    (live : after.handles fd = some handle)
    (checked : ∀ name ∈ rawComponents request.left, PrivateNames.reservedBytes name = false) :
    family handle.object = none := by
  cases label : family handle.object with
  | none => rfl
  | some scope =>
    obtain ⟨root, initialized, path⟩ := contract.path _ _ _ _ _ _ actual operation flags relative absolute
      opened live (graph.data handle.object scope label)
    have publicObject := data_path_public graph path (family_initial_public graph root initialized) checked
    rw [publicObject] at label
    cases label

-- §FS-host-boundary.ownership: The internal /tmp argument does not invent a private parent.
theorem actual_temporary_lookup_public {kernel : Contract} {initialObjects : ObjectId → Bool}
    {dataObjects : ObjectId → Prop} (contract : AbsoluteLookupContract kernel initialObjects dataObjects)
    {before after : World} {family : Family} (graph : FamilyGraph before family initialObjects dataObjects)
    {reply : Reply} {fd : UInt64} {handle : Handle}
    (actual : kernel.step before {op := .openAt, first := cwd, second := directoryFlags, left := "/tmp".toUTF8}
      (some reply) after) (opened : descriptor reply = some fd) (live : after.handles fd = some handle) :
    family handle.object = none := by
  apply absolute_lookup_public contract graph actual rfl rfl rfl (by decide) opened live
  have names : rawComponents "/tmp".toUTF8 = ["tmp".toUTF8] := by decide
  rw [names]
  intro name member
  have same : name = "tmp".toUTF8 := List.mem_singleton.mp member
  subst name
  decide

-- §FS-host-boundary.ownership: getcwd is interpreted as names of the retained actual CWD object.
theorem working_directory_public {kernel : Contract} {initialObjects : ObjectId → Bool}
    {dataObjects : ObjectId → Prop} (contract : WorkingDirectoryContract kernel initialObjects dataObjects)
    {before after : World} {family : Family} (graph : FamilyGraph before family initialObjects dataObjects)
    {request : Request} {reply : Reply} (actual : kernel.step before request (some reply) after)
    (operation : request.op = .workingDirectory) (accepted : SourcePaths.currentSpelling reply = .ok ()) :
    family before.workingDirectory = none := by
  obtain ⟨success, nonempty, absolute, parts, parsed⟩ := Snapshot.currentSpelling_source reply accepted
  obtain ⟨_, _, same, checked⟩ := Snapshot.sourceComponents_fields reply.2 parts parsed
  obtain ⟨root, initialized, path⟩ := contract.spelling _ _ _ _ actual operation success nonempty absolute
  have publicRoot := family_initial_public graph root initialized
  apply data_path_public graph path publicRoot
  intro name member
  have inParts : name ∈ parts := by simpa only [rawComponents] using same ▸ member
  exact (checked name inParts).2

end LeanCage.Host.Kernel
