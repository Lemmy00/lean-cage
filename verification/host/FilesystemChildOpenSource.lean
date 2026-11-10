import FilesystemDirectorySources

namespace LeanCage.Host.Kernel
open Filesystem

private theorem source_no_open {α : Type} {program : Filesystem.Program α}
    (profile : RequestProgram (fun request => request.op ≠ .openAt) program)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix program (before ++ [(request, observed)])) (opening : request.op = .openAt) : False :=
  request_prefix profile source (request, observed) (by simp) opening

private theorem pure_no_open {α : Type} (value : α)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (.pure value) (before ++ [(request, observed)])) : False := by
  have lengths := congrArg List.length (Snapshot.prefix_pure_empty source)
  simp only [List.length_append, List.length_singleton, List.length_nil] at lengths
  omega

private theorem inspect_no_open (uid : Nat) (fd : UInt64) :
    RequestProgram (fun request => request.op ≠ .openAt) (Directories.inspect uid fd) := by
  unfold Directories.inspect
  apply RequestProgram.call (by intro invalid; cases invalid)
  intro reply
  repeat' first | exact .pure _ | split |
    exact RequestProgram.call (by intro invalid; cases invalid) (fun _ => .pure _)

private theorem call_last_open {α : Type} (head : Request) (next : Reply → Filesystem.Program α)
    (tail : ∀ reply, RequestProgram (fun request => request.op ≠ .openAt) (next reply))
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (.call head next) (before ++ [(request, observed)])) (opening : request.op = .openAt) :
    before = [] ∧ request = head := by
  cases before with
  | nil => cases observed <;> cases source <;> exact ⟨rfl, rfl⟩
  | cons first rest =>
    cases rest with
    | nil =>
      change Prefix (.call head next) [first, (request, observed)] at source
      cases source with
      | returned _ _ reply events following =>
        exact False.elim (source_no_open (tail reply) (before := []) following opening)
    | cons second rest =>
      change Prefix (.call head next) (first :: second :: (rest ++ [(request, observed)])) at source
      cases source with
      | returned _ _ reply events following =>
        exact False.elim (source_no_open (tail reply) (before := second :: rest) following opening)

private theorem opening_is_first (uid : Nat) (parent : UInt64) (name : ByteArray)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (Directories.openAt uid parent name) (before ++ [(request, observed)]))
    (opening : request.op = .openAt) :
    before = [] ∧ request = {op := .openAt, first := parent, second := directoryFlags, left := name} := by
  apply call_last_open _ _ _ source opening
  intro reply
  split
  · exact .pure _
  · exact inspect_no_open _ _

-- §FS-host-boundary.ownership: The source directory helper has one exact opening call;
-- subsequent inspection failures and closing replies cannot create another open occurrence.
theorem actual_directory_opening_first (uid : Nat) (parent : UInt64) (name : ByteArray)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (Directories.openAt uid parent name) (before ++ [(request, observed)]))
    (opening : request.op = .openAt) :
    before = [] ∧ request = {op := .openAt, first := parent, second := directoryFlags, left := name} :=
  opening_is_first uid parent name source opening

private theorem skip_other_call {α : Type} (head : Request) (next : Reply → Filesystem.Program α)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix (.call head next) (before ++ [(request, observed)]))
    (different : head.op ≠ request.op) :
    ∃ reply inside, before = (head, some reply) :: inside ∧ Prefix (next reply) (inside ++ [(request, observed)]) := by
  cases before with
  | nil => cases observed <;> cases source <;> exact False.elim (different rfl)
  | cons first rest =>
    cases rest with
    | nil =>
      change Prefix (.call head next) [first, (request, observed)] at source
      cases source with
      | returned _ _ reply events following => exact ⟨reply, [], rfl, following⟩
    | cons second rest =>
      change Prefix (.call head next) (first :: second :: (rest ++ [(request, observed)])) at source
      cases source with
      | returned _ _ reply events following => exact ⟨reply, second :: rest, rfl, following⟩

private theorem random_no_open (fuel count : Nat) (bytes : ByteArray) :
    RequestProgram (fun request => request.op ≠ .openAt) (Directories.randomBytes fuel count bytes) := by
  induction fuel generalizing bytes with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold Directories.randomBytes
    split
    · exact .pure _
    · split
      · exact .pure _
      · apply RequestProgram.call (by intro invalid; cases invalid)
        intro reply
        repeat' first | exact .pure _ | split | exact ih _

structure NewChildOpening (uid : Nat) (parent : UInt64) (prefixName : String)
    (before : List (Request × Option Reply)) (request : Request) where
  random : ByteArray
  randomEvents : List (Request × Reply)
  randomness : Returns (Directories.randomBytes 17 16 .empty) randomEvents (.ok random)
  component : Directories.component (prefixName ++ Snapshot.hex random).toUTF8 = true
  made : Reply
  acknowledged : made.1 = 0 ∧ made.2.isEmpty = true
  trace : before = Publication.completed randomEvents ++ [({
    op := .mkdirAt, first := parent, second := 448, left := (prefixName ++ Snapshot.hex random).toUTF8 }, some made)]
  operation : request = {
    op := .openAt, first := parent, second := directoryFlags, left := (prefixName ++ Snapshot.hex random).toUTF8 }

-- §FS-host-boundary.ownership: The actual child reopen, including its lost reply, follows
-- that SAME acknowledged mkdir. Random bytes are inputs to the name, never freshness evidence.
theorem actual_new_child_opening (uid : Nat) (parent : UInt64) (prefixName : String)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (active : Prefix (Directories.newChild uid parent prefixName) (before ++ [(request, observed)]))
    (opening : request.op = .openAt) : Nonempty (NewChildOpening uid parent prefixName before request) := by
  unfold Directories.newChild at active
  rcases filesystem_last_bind_split _ _ active with randomizing |
      ⟨randomEvents, result, inside, randomness, following, shape⟩
  · exact False.elim (source_no_open (random_no_open _ _ _) randomizing opening)
  · cases result with
    | error error => exact False.elim (pure_no_open _ following)
    | ok random =>
      dsimp only at following
      split at following
      · exact False.elim (pure_no_open _ following)
      · rename_i checked
        obtain ⟨made, inside, madeShape, afterMkdir⟩ := skip_other_call _ _ following (by rw [opening]; intro invalid; cases invalid)
        dsimp only [Filesystem.Program.bind] at afterMkdir
        split at afterMkdir
        · exact False.elim (pure_no_open _ afterMkdir)
        · rename_i accepted
          rcases filesystem_last_bind_split _ _ afterMkdir with opened |
              ⟨openingEvents, result, last, returned, rest, restShape⟩
          · obtain ⟨rfl, requestShape⟩ := opening_is_first _ _ _ opened opening
            refine ⟨⟨random, randomEvents, randomness, by simpa using checked, made, ?_, ?_, requestShape⟩⟩
            · simpa [Bool.or_eq_true] using accepted
            · simpa only [madeShape, List.singleton_append, List.append_nil] using shape
          · cases result with
            | error error => exact False.elim (pure_no_open _ rest)
            | ok directory =>
              dsimp only at rest
              split at rest
              · exact False.elim (source_no_open
                  (RequestProgram.call (by intro invalid; cases invalid) (fun _ => .pure _)) rest opening)
              · exact False.elim (pure_no_open _ rest)

end LeanCage.Host.Kernel
