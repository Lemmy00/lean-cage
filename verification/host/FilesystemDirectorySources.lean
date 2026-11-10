import FilesystemPublicationSource

namespace LeanCage.Host.Kernel
open Filesystem

private theorem readonly_no_mkdir {α : Type} {program : Filesystem.Program α}
    (source : Retrieval.ReadOnly program) : RequestProgram (fun request => request.op ≠ .mkdirAt) program := by
  induction source with
  | pure => exact .pure _
  | @call request next allowed following ih =>
    apply RequestProgram.call _ ih
    intro mkdir
    unfold Retrieval.Allowed at allowed
    rw [mkdir] at allowed
    exact allowed

private theorem source_no_mkdir {α : Type} {program : Filesystem.Program α}
    (profile : RequestProgram (fun request => request.op ≠ .mkdirAt) program)
    {before : List (Request × Option Reply)} {event : Request × Option Reply}
    (source : Prefix program (before ++ [event])) (mkdir : event.1.op = .mkdirAt) : False :=
  request_prefix profile source event (by simp) mkdir

private theorem pure_no_last {α : Type} (value : α) {before : List (Request × Option Reply)}
    {event : Request × Option Reply} (source : Prefix (.pure value) (before ++ [event])) : False := by
  have empty := Snapshot.prefix_pure_empty source
  have lengths := congrArg List.length empty
  simp only [List.length_append, List.length_singleton, List.length_nil] at lengths
  omega

private theorem call_last_mkdir {α : Type} (request : Request) (next : Reply → Filesystem.Program α)
    (tail : ∀ reply, RequestProgram (fun request => request.op ≠ .mkdirAt) (next reply))
    {before : List (Request × Option Reply)} {event : Request × Option Reply}
    (source : Prefix (.call request next) (before ++ [event])) (mkdir : event.1.op = .mkdirAt) :
    before = [] ∧ event.1 = request := by
  cases before with
  | nil =>
    rcases event with ⟨operation, observed⟩
    cases observed <;> cases source <;> exact ⟨rfl, rfl⟩
  | cons first rest =>
    cases rest with
    | nil =>
      change Prefix (.call request next) [first, event] at source
      cases source with
      | returned _ _ reply events following =>
        exact False.elim (source_no_mkdir (tail reply) (before := []) following mkdir)
    | cons second rest =>
      change Prefix (.call request next) (first :: second :: (rest ++ [event])) at source
      cases source with
      | returned _ _ reply events following =>
        exact False.elim (source_no_mkdir (tail reply) (before := second :: rest) following mkdir)

structure NewChildCall (uid : Nat) (parent : UInt64) (prefixName : String)
    (before : List (Request × Option Reply)) (request : Request) where
  random : ByteArray
  randomEvents : List (Request × Reply)
  randomness : Returns (Directories.randomBytes 17 16 .empty) randomEvents (.ok random)
  trace : before = Publication.completed randomEvents
  component : Directories.component (prefixName ++ Snapshot.hex random).toUTF8 = true
  operation : request = {
    op := .mkdirAt
    first := parent
    second := 448
    left := (prefixName ++ Snapshot.hex random).toUTF8 }

-- §FS-host-boundary.ownership: Even a lost mkdir has the actual checked name and random prefix.
theorem actual_new_child_call (uid : Nat) (parent : UInt64) (prefixName : String)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (active : Prefix (Directories.newChild uid parent prefixName) (before ++ [(request, observed)]))
    (mkdir : request.op = .mkdirAt) : Nonempty (NewChildCall uid parent prefixName before request) := by
  unfold Directories.newChild at active
  rcases filesystem_last_bind_split _ _ active with randomizing |
      ⟨randomEvents, result, inside, randomness, following, shape⟩
  · have noMkdir : RequestProgram (fun request => request.op ≠ .mkdirAt)
        (Directories.randomBytes 17 16 .empty) := by
      apply request_weaken (random_namespace_passive _ _ _)
      intro request passive mkdir
      unfold NamespacePassive at passive
      rw [mkdir] at passive
      exact passive
    exact False.elim (source_no_mkdir noMkdir randomizing mkdir)
  · cases result with
    | error error => exact False.elim (pure_no_last _ following)
    | ok random =>
      dsimp only at following
      split at following
      · exact False.elim (pure_no_last _ following)
      · rename_i checked
        have tail : ∀ reply, RequestProgram (fun request => request.op ≠ .mkdirAt)
            ((fun made =>
              if made.1 != 0 || !made.2.isEmpty then
                pure (.error (failure "fresh stage mkdirat" made))
              else do
                let opened ← Directories.openAt uid parent (prefixName ++ Snapshot.hex random).toUTF8
                match opened with
                | .error error => return .error error
                | .ok directory =>
                  if directory.information.uid != uid || (directory.information.mode &&& 511) != 448 then
                    closeResult directory.fd (.error "fresh stage authority differs")
                  else return .ok (⟨directory, (prefixName ++ Snapshot.hex random).toUTF8⟩ : Directories.NewDirectory)) reply) := by
          intro reply
          dsimp only
          split
          · exact .pure _
          · apply request_bind (readonly_no_mkdir (Retrieval.openAt_readOnly _ _ _))
            intro opened
            cases opened with
            | error => exact .pure _
            | ok directory =>
              dsimp only
              split
              · exact readonly_no_mkdir (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
              · exact .pure _
        obtain ⟨rfl, same⟩ := call_last_mkdir _ _ tail following mkdir
        exact ⟨⟨random, randomEvents, randomness, by simpa using shape,
          by simpa using checked, same⟩⟩

structure FreshChildCall (parent : Directories.Parent)
    (before : List (Request × Option Reply)) (request : Request) where
  container : Directories.Opened
  opening : List (Request × Reply)
  opened : Returns (Directories.openAt parent.uid parent.directory.fd ".".toUTF8) opening (.ok container)
  inside : List (Request × Option Reply)
  child : NewChildCall parent.uid container.fd PrivateNames.prefixText inside request
  trace : before = Publication.completed opening ++ inside

-- §FS-host-boundary.ownership: Publication creation retains its actual public-parent alias.
theorem actual_fresh_child_call (parent : Directories.Parent)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (active : Prefix (Directories.fresh parent) (before ++ [(request, observed)]))
    (mkdir : request.op = .mkdirAt) : Nonempty (FreshChildCall parent before request) := by
  unfold Directories.fresh at active
  rcases filesystem_last_bind_split _ _ active with opening |
      ⟨opening, result, afterOpen, opened, following, shape⟩
  · exact False.elim (source_no_mkdir (readonly_no_mkdir (Retrieval.openAt_readOnly _ _ _)) opening mkdir)
  · cases result with
    | error error => exact False.elim (pure_no_last _ following)
    | ok container =>
      rcases filesystem_last_bind_split _ _ following with creating |
          ⟨creating, result, afterCreate, created, following, createShape⟩
      · obtain ⟨child⟩ := actual_new_child_call _ _ _ creating mkdir
        exact ⟨⟨container, opening, opened, afterOpen, child, shape⟩⟩
      · cases result with
        | error error => exact False.elim (source_no_mkdir
            (readonly_no_mkdir (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))) following mkdir)
        | ok child => exact False.elim (pure_no_last _ following)

private theorem temporary_parent_no_mkdir :
    RequestProgram (fun request => request.op ≠ .mkdirAt) Directories.temporaryParent := by
  unfold Directories.temporaryParent
  apply RequestProgram.call (by decide)
  intro reply
  dsimp only [Filesystem.Program.bind]
  split
  · exact .pure _
  · apply request_bind (readonly_no_mkdir (Retrieval.openAt_readOnly _ _ _))
    intro result
    cases result <;> exact .pure _

structure RunChildCall (before : List (Request × Option Reply)) (request : Request) where
  container : Directories.Opened
  uid : Nat
  selecting : List (Request × Reply)
  selected : Returns Directories.temporaryParent selecting (.ok (container, "/tmp", uid))
  inside : List (Request × Option Reply)
  child : NewChildCall uid container.fd PrivateNames.prefixText inside request
  trace : before = Publication.completed selecting ++ inside

-- §FS-host-boundary.ownership: Validator/VM roots use the actual checked temporary parent.
theorem actual_run_child_call {before : List (Request × Option Reply)} {request : Request}
    {observed : Option Reply} (active : Prefix RunDirectory.create (before ++ [(request, observed)]))
    (mkdir : request.op = .mkdirAt) : Nonempty (RunChildCall before request) := by
  unfold RunDirectory.create at active
  rcases filesystem_last_bind_split _ _ active with selecting |
      ⟨selecting, result, afterSelect, selected, following, shape⟩
  · exact False.elim (source_no_mkdir temporary_parent_no_mkdir selecting mkdir)
  · cases result with
    | error error => exact False.elim (pure_no_last _ following)
    | ok area =>
      rcases area with ⟨container, path, uid⟩
      obtain ⟨samePath, _⟩ := RunDirectory.temporaryParent_source selected
      dsimp only at samePath
      subst path
      rcases filesystem_last_bind_split _ _ following with creating |
          ⟨creating, result, afterCreate, created, following, createShape⟩
      · obtain ⟨child⟩ := actual_new_child_call _ _ _ creating mkdir
        exact ⟨⟨container, uid, selecting, selected, afterSelect, child, shape⟩⟩
      · cases result with
        | error error => exact False.elim (source_no_mkdir
            (readonly_no_mkdir (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))) following mkdir)
        | ok child =>
          apply False.elim
          apply source_no_mkdir (program := _) _ following mkdir
          dsimp only
          apply RequestProgram.call (by change Op.setAttribute ≠ Op.mkdirAt; decide)
          intro marked
          dsimp only [Filesystem.Program.bind]
          split
          · apply RequestProgram.call (by change Op.close ≠ Op.mkdirAt; decide)
            intro reply
            dsimp only [Filesystem.Program.bind]
            apply RequestProgram.call (by change Op.unlinkAt ≠ Op.mkdirAt; decide)
            intro reply
            dsimp only [Filesystem.Program.bind]
            exact readonly_no_mkdir (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
          · split
            · apply RequestProgram.call (by change Op.close ≠ Op.mkdirAt; decide)
              intro reply
              dsimp only [Filesystem.Program.bind]
              exact readonly_no_mkdir (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
            · split
              · apply RequestProgram.call (by change Op.close ≠ Op.mkdirAt; decide)
                intro reply
                dsimp only [Filesystem.Program.bind]
                exact readonly_no_mkdir (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _))
              · exact .pure _

end LeanCage.Host.Kernel
