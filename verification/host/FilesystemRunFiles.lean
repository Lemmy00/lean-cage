import FilesystemRunReference
import FilesystemSourceOrigins
import FilesystemPublicationContentProfile
import FilesystemOutputSources.Directories

namespace LeanCage.Host.Kernel
open Filesystem

def ExclusiveFile (request : Request) : Prop := request.op = .openAt ∧ request.second = newFileFlags

theorem passive_not_exclusive {request : Request} (passive : NamespacePassive request) : ¬ ExclusiveFile request := by
  rintro ⟨opening, flags⟩
  simp only [NamespacePassive, opening, flags] at passive
  rcases passive with reading | directory
  · exact (by decide : newFileFlags ≠ readFlags) reading
  · exact (by decide : newFileFlags ≠ directoryFlags) directory

private theorem passive_no_exclusive {α : Type} {program : Filesystem.Program α}
    (source : RequestProgram NamespacePassive program) : RequestProgram (fun request => ¬ ExclusiveFile request) program :=
  request_weaken source (fun _ => passive_not_exclusive)

private theorem pure_no_last {α : Type} (value : α) {before : List (Request × Option Reply)}
    {request : Request} {observed : Option Reply}
    (source : Prefix (.pure value) (before ++ [(request, observed)])) : False := by
  have count := congrArg List.length (Snapshot.prefix_pure_empty source)
  simp only [List.length_append, List.length_singleton, List.length_nil] at count
  omega

private theorem exclusive_first {α : Type} (head : Request) (next : Reply → Filesystem.Program α)
    (quiet : ∀ reply, RequestProgram (fun request => ¬ ExclusiveFile request) (next reply))
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (.call head next) (before ++ [(request, observed)])) (exclusive : ExclusiveFile request) :
    before = [] ∧ request = head := by
  cases before with
  | nil => cases observed <;> cases source <;> exact ⟨rfl, rfl⟩
  | cons first rest =>
    cases rest with
    | nil =>
      cases source with
      | returned _ _ reply events following =>
        exact False.elim (request_prefix (quiet reply) following (request, observed) (by simp) exclusive)
    | cons second rest =>
      cases source with
      | returned _ _ reply events following =>
        exact False.elim (request_prefix (quiet reply) following (request, observed) (by simp) exclusive)

theorem writeNew_exclusive_first (parent : UInt64) (name bytes : ByteArray) (mode : UInt64)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (writeNew parent name bytes mode) (before ++ [(request, observed)]))
    (exclusive : ExclusiveFile request) : before = [] ∧
    request = {op := .openAt, first := parent, second := newFileFlags, third := mode, left := name} := by
  unfold writeNew at source
  split at source
  · exact False.elim (pure_no_last _ source)
  · apply exclusive_first _ _ _ source exclusive
    intro reply
    split
    · exact .pure _
    · apply request_bind (passive_no_exclusive (write_loop_namespace_passive _ _ _ _))
      intro written
      exact passive_no_exclusive (read_only_namespace_passive (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _)))

-- §FS-host-boundary.ownership: These two source programs are the actual
-- validator policy writer and request archive writer below the SAME run.
-- No physical ownership or helper footprint is encoded by this data.
inductive RunFileProgram where
  | validator (raw : ByteArray)
  | image (bundle : Validation.Bundle) (overlay : List Image.Entry)

def RunFileProgram.program : RunFileProgram → UInt64 → Filesystem.Program (Result Unit)
  | .validator raw, directory => writeNew directory "policy.json".toUTF8 raw
  | .image bundle overlay, directory => Image.create directory bundle overlay

theorem RunFileProgram.borrowed {kernel : Contract} (descriptors : DescriptorContract kernel)
    (kind : RunFileProgram) (held : UInt64) (handle : Handle) (directory : UInt64) :
    BorrowPost kernel held handle (fun _ => True) (kind.program directory).lower := by
  cases kind with
  | validator raw => exact Lowered.writeNew_borrow descriptors held handle _ _ _ _
  | image bundle overlay => exact Lowered.image_create_borrow descriptors held handle _ _ _

theorem RunFileProgram.nondestructive (kind : RunFileProgram) (directory : UInt64) :
    RequestProgram (fun request => ¬ DestructiveRequest request) (kind.program directory) := by
  cases kind with
  | validator raw => exact writeNew_nondestructive _ _ _ _
  | image bundle overlay =>
    change RequestProgram (fun request => ¬ DestructiveRequest request) (Image.create directory bundle overlay)
    unfold Image.create
    split
    · exact .pure _
    · apply request_bind
      · exact request_weaken (read_only_namespace_passive (Image.copyIdentified_readOnly _ _ _))
          (fun _ => namespace_passive_not_destructive)
      · intro copied
        cases copied with
        | error => exact .pure _
        | ok base =>
          apply RequestProgram.call (by simp [DestructiveRequest])
          intro reply
          dsimp only [Filesystem.Program.bind]
          split
          · exact .pure _
          · apply request_weaken (Image.contentClose_requests _ _ _)
            intro query role destructive
            rcases role with writing | closing
            · rcases destructive with removing | moving
              · rw [writing.1] at removing; cases removing
              · rw [writing.1] at moving; cases moving
            · rcases destructive with removing | moving
              · rw [closing] at removing; cases removing
              · rw [closing] at moving; cases moving

theorem RunFileProgram.arguments (kind : RunFileProgram) (directory : UInt64)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (kind.program directory) (before ++ [(request, observed)])) (exclusive : ExclusiveFile request) :
    request.first = directory ∧ request.third = 384 ∧ Directories.component request.left = true := by
  cases kind with
  | validator raw =>
    have operation := (writeNew_exclusive_first directory "policy.json".toUTF8 raw 384 source exclusive).2
    refine ⟨congrArg Request.first operation, congrArg Request.third operation, ?_⟩
    rw [operation]
    change Directories.component (ByteArray.mk #[112, 111, 108, 105, 99, 121, 46, 106, 115, 111, 110]) = true
    simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem]
  | image bundle overlay =>
    change Prefix (Image.create directory bundle overlay) _ at source
    unfold Image.create at source
    split at source
    · exact False.elim (pure_no_last _ source)
    · rcases filesystem_last_bind_split _ _ source with copying |
          ⟨copying, result, inside, copied, following, trace⟩
      · exact False.elim (request_prefix (passive_no_exclusive
          (read_only_namespace_passive (Image.copyIdentified_readOnly _ _ _))) copying (request, observed) (by simp) exclusive)
      · cases result with
        | error error => exact False.elim (pure_no_last _ following)
        | ok base =>
          have operation := (exclusive_first _ _ (fun reply => by
            dsimp only [Filesystem.Program.bind]
            split
            · exact .pure _
            · apply request_weaken (Image.contentClose_requests _ _ _)
              intro query role other
              have opening : query.op = .openAt := other.1
              rcases role with writing | closing
              · rw [writing.1] at opening
                cases opening
              · rw [closing] at opening
                cases opening) following exclusive).2
          refine ⟨congrArg Request.first operation, congrArg Request.third operation, ?_⟩
          rw [operation]
          change Directories.component (ByteArray.mk #[114, 101, 113, 117, 101, 115, 116, 46, 99, 112, 105, 111]) = true
          simp [Directories.component, ByteArray.isEmpty, ByteArray.size, Array.contains_eq_mem]

structure RunFileCall (before : List Program.Event) (request : Request) where
  directory : RunDirectory.Owned
  outside : List Program.Event
  creating : List (Request × Reply)
  created : Returns RunDirectory.create creating (.ok directory)
  kind : RunFileProgram
  inside : List (Request × Option Reply)
  active : Prefix (kind.program directory.directory.fd) (inside ++ [(request, none)])
  trace : before = outside ++ creating.map Program.filesystemEvent ++ inside.map Program.filesystemPrefixEvent

def RunFileCall.prepend {before inside : List Program.Event} {request : Request}
    (call : RunFileCall inside request) (outside : List Program.Event) (trace : before = outside ++ inside) :
    RunFileCall before request := {call with
  outside := outside ++ call.outside
  trace := trace.trans ((congrArg (outside ++ ·) call.trace).trans (by simp only [List.append_assoc])) }

end LeanCage.Host.Kernel
