import FilesystemWriteSources.ReadOnly
import FilesystemPublicationSource

namespace LeanCage.Host.Kernel.WriteSources
open Filesystem

structure FileSite (before : List (Request × Option Reply)) (event : Request × Option Reply) where
  parent : UInt64
  name : ByteArray
  bytes : ByteArray
  mode : UInt64
  context : List (Request × Option Reply)
  inside : List (Request × Option Reply)
  active : Prefix (writeNew parent name bytes mode) (inside ++ [event])
  trace : before = context ++ inside

def FileSite.outer {before inside : List (Request × Option Reply)} {event : Request × Option Reply}
    (source : FileSite inside event) (context : List (Request × Option Reply))
    (trace : before = context ++ inside) : FileSite before event :=
  { source with
    context := context ++ source.context
    trace := trace.trans ((congrArg (context ++ ·) source.trace).trans
      (List.append_assoc context source.context source.inside).symm) }

-- §FS-host-boundary.ownership: This is proved over actual executable source programs.
-- It identifies an exact nested writer call; no physical freshness or ownership is assumed.
def FileWriters {α : Type} (program : Filesystem.Program α) : Prop :=
  ∀ before request observed, Prefix program (before ++ [(request, observed)]) → request.op = .write →
    Nonempty (FileSite before (request, observed))

theorem file_pure {α : Type} (value : α) : FileWriters (.pure value) := by
  intro before request observed source writing
  have empty := Snapshot.prefix_pure_empty source
  have length := congrArg List.length empty
  simp only [List.length_append, List.length_singleton, List.length_nil] at length
  omega

theorem file_bind {α β : Type} {program : Filesystem.Program α} {next : α → Filesystem.Program β}
    (first : FileWriters program) (tail : ∀ value, FileWriters (next value)) : FileWriters (program.bind next) := by
  intro before request observed source writing
  rcases filesystem_last_bind_split program next source with earlier |
      ⟨completed, value, inside, returned, active, trace⟩
  · exact first before request observed earlier writing
  · obtain ⟨site⟩ := tail value inside request observed active writing
    exact ⟨site.outer (Publication.completed completed) trace⟩

theorem file_no_write {α : Type} {program : Filesystem.Program α}
    (source : RequestProgram NoWrite program) : FileWriters program := by
  intro before request observed active writing
  exact False.elim (request_prefix source active (request, observed) (by simp) writing)

theorem file_effect (request : Request) (notWrite : request.op ≠ .write) :
    FileWriters (Filesystem.Program.effect request) :=
  file_no_write (.call notWrite (fun _ => .pure _))

theorem file_call {α : Type} {request : Request} {next : Reply → Filesystem.Program α}
    (notWrite : request.op ≠ .write) (tail : ∀ reply, FileWriters (next reply)) : FileWriters (.call request next) :=
  file_bind (file_effect request notWrite) tail

theorem file_writeNew (parent : UInt64) (name bytes : ByteArray) (mode : UInt64 := 384) :
    FileWriters (writeNew parent name bytes mode) := by
  intro before request observed source writing
  exact ⟨⟨parent, name, bytes, mode, [], before, source, rfl⟩⟩

theorem file_forIn {α β : Type} (items : List α) (initial : β)
    (body : α → β → Filesystem.Program (ForInStep β))
    (source : ∀ item ∈ items, ∀ state, FileWriters (body item state)) : FileWriters (forIn items initial body) := by
  induction items generalizing initial with
  | nil => exact file_pure _
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply file_bind (source item (by simp) initial)
    intro step
    cases step with
    | done => exact file_pure _
    | yield state => exact ih state (fun item member => source item (by simp [member]))

theorem file_closeResult {α : Type} (fd : UInt64) (value : Result α) : FileWriters (closeResult fd value) := by
  apply file_bind (file_effect _ (by intro wrong; cases wrong))
  intro reply
  cases value with
  | error => exact file_pure _
  | ok => dsimp only; split <;> exact file_pure _

end LeanCage.Host.Kernel.WriteSources
