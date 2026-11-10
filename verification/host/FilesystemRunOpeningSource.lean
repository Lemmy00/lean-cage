import FilesystemChildOpenSource
import FilesystemMarkerBindings.Invocation

namespace LeanCage.Host.Kernel
open Filesystem

private theorem fs_prefix_bind_return {α β : Type} {program : Filesystem.Program α}
    {next : α → Filesystem.Program β} {first : List (Request × Reply)} {last : List (Request × Option Reply)}
    {value : α} (source : Returns program first value) (tail : Prefix (next value) last) :
    Prefix (program.bind next) (Publication.completed first ++ last) := by
  induction source with
  | pure => exact tail
  | call request continuation reply events value rest ih =>
    exact .returned request (fun reply => (continuation reply).bind next) reply _ (ih tail)

private theorem fs_prefix_bind_left {α β : Type} {program : Filesystem.Program α}
    {next : α → Filesystem.Program β} {events : List (Request × Option Reply)}
    (source : Prefix program events) : Prefix (program.bind next) events := by
  induction source with
  | empty => exact .empty _
  | lost request continuation => exact .lost request (fun reply => (continuation reply).bind next)
  | returned request continuation reply tail rest ih =>
    exact .returned request (fun reply => (continuation reply).bind next) reply tail ih

private theorem no_open_last {α : Type} {program : Filesystem.Program α}
    (profile : RequestProgram (fun request => request.op ≠ .openAt) program)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix program (before ++ [(request, observed)])) (opening : request.op = .openAt) : False :=
  request_prefix profile source (request, observed) (by simp) opening

private theorem pure_no_last {α : Type} (value : α) {before : List (Request × Option Reply)}
    {event : Request × Option Reply} (source : Prefix (.pure value) (before ++ [event])) : False := by
  have empty := Snapshot.prefix_pure_empty source
  have lengths := congrArg List.length empty
  simp only [List.length_append, List.length_singleton, List.length_nil] at lengths
  omega

inductive RunDirectoryOpening (before : List (Request × Option Reply)) (request : Request)
    (observed : Option Reply) : Type 1 where
  | selecting (active : Prefix Directories.temporaryParent (before ++ [(request, observed)])) :
      RunDirectoryOpening before request observed
  | child (container : Directories.Opened) (path : String) (uid : Nat)
      (selecting : List (Request × Reply))
      (selected : Returns Directories.temporaryParent selecting (.ok (container, path, uid)))
      (inside : List (Request × Option Reply))
      (active : Prefix (Directories.newChild uid container.fd PrivateNames.prefixText) (inside ++ [(request, observed)]))
      (trace : before = Publication.completed selecting ++ inside) : RunDirectoryOpening before request observed

-- §FS-host-boundary.ownership: An actual run-directory open either selects its public
-- temporary parent or reopens its freshly created child. All setup failures remain branches.
theorem actual_run_directory_opening {before : List (Request × Option Reply)} {request : Request}
    {observed : Option Reply} (source : Prefix RunDirectory.create (before ++ [(request, observed)]))
    (opening : request.op = .openAt) : Nonempty (RunDirectoryOpening before request observed) := by
  unfold RunDirectory.create at source
  rcases filesystem_last_bind_split _ _ source with selecting |
      ⟨selecting, result, inside, selected, following, trace⟩
  · exact ⟨.selecting selecting⟩
  · cases result with
    | error error => exact False.elim (pure_no_last _ following)
    | ok area =>
      rcases area with ⟨container, path, uid⟩
      rcases filesystem_last_bind_split _ _ following with creating |
          ⟨created, result, afterChild, finished, remaining, afterTrace⟩
      · exact ⟨.child container path uid selecting selected inside creating trace⟩
      · cases result with
        | error error =>
          exact False.elim (no_open_last
            (RequestProgram.call (by intro impossible; cases impossible) (fun _ => .pure _)) remaining opening)
        | ok child =>
          apply False.elim
          apply no_open_last (program := _) ?_ remaining opening
          repeat' first
            | exact .pure _
            | dsimp only [Filesystem.Program.bind]
            | split
            | apply RequestProgram.call (by intro impossible; cases impossible); intro reply

-- §FS-host-boundary.ownership: The actual successful random/name prefix also proves
-- the earlier original mkdir callsite, without treating random bytes as freshness evidence.
theorem new_child_mkdir_prefix {uid : Nat} {parent : UInt64} {prefixName : String}
    {before : List (Request × Option Reply)} {request : Request}
    (child : NewChildOpening uid parent prefixName before request) :
    Prefix (Directories.newChild uid parent prefixName)
      (Publication.completed child.randomEvents ++ [({
        op := .mkdirAt
        first := parent
        second := 448
        left := (prefixName ++ Snapshot.hex child.random).toUTF8 }, none)]) := by
  unfold Directories.newChild
  apply fs_prefix_bind_return child.randomness
  dsimp only
  rw [child.component]
  exact .lost _ _

-- §FS-host-boundary.ownership: The caller's actual preceding temporary-parent selection
-- places that mkdir inside this SAME RunDirectory.create invocation and source context.
def run_root_mkdir_invocation (container : Directories.Opened) (path : String) (uid : Nat)
    {selecting : List (Request × Reply)}
    (selected : Returns Directories.temporaryParent selecting (.ok (container, path, uid)))
    {inside : List (Request × Option Reply)} {request : Request}
    (child : NewChildOpening uid container.fd PrivateNames.prefixText inside request)
    (outside : List Program.Event) :
    RunCreationPrefix (outside ++ selecting.map Program.filesystemEvent ++ child.randomEvents.map Program.filesystemEvent)
      { op := .mkdirAt, first := container.fd, second := 448,
        left := (PrivateNames.prefixText ++ Snapshot.hex child.random).toUTF8 } none := by
  refine ⟨outside, Publication.completed selecting ++ Publication.completed child.randomEvents, ?_, ?_⟩
  · unfold RunDirectory.create
    rw [List.append_assoc]
    apply fs_prefix_bind_return selected
    exact fs_prefix_bind_left (new_child_mkdir_prefix child)
  · simp only [List.map_append, completed_filesystem_events, List.append_assoc]

end LeanCage.Host.Kernel
