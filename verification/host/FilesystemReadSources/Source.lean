import FilesystemReadSources.Effects
import FilesystemReads

namespace LeanCage.Host.Kernel
open Filesystem

inductive GuardedCopyStart : UInt64 → Type where
  | path (path : ByteArray) (fd : UInt64) (opening : List (Request × Reply))
      (opened : Returns (SourcePaths.open path false) opening (.ok fd)) : GuardedCopyStart fd
  | child (parent : UInt64) (name : ByteArray) (fd : UInt64) (opening : List (Request × Reply))
      (opened : Returns (SourcePaths.openAt parent name false) opening (.ok fd))
      (reply : Reply) (information : Stat) (parsed : parseStat reply = some information)
      (regular : information.regular = true) (linked : information.links = 1) : GuardedCopyStart fd

def GuardedCopyStart.events {fd : UInt64} : GuardedCopyStart fd → List (Request × Reply)
  | .path _ _ opening _ => opening
  | .child _ _ _ opening _ reply _ _ _ _ => opening ++ [({op := .stat, first := fd}, reply)]

structure GuardedCopyCall (before : List (Request × Option Reply)) (request : Request) (observed : Option Reply) where
  fd : UInt64
  limit : Nat
  start : GuardedCopyStart fd
  context : List (Request × Option Reply)
  inside : List (Request × Option Reply)
  active : Prefix (copyOpened fd limit) (inside ++ [(request, observed)])
  trace : before = context ++ Publication.completed start.events ++ inside

-- §FS-host-boundary.snapshot: Earlier completed source phases retain their exact position.
def GuardedCopyCall.prepend {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : GuardedCopyCall before request observed) (earlier : List (Request × Option Reply)) :
    GuardedCopyCall (earlier ++ before) request observed := {
  source with
  context := earlier ++ source.context
  trace := by simp only [source.trace, List.append_assoc] }

def ReadSources {α : Type} (program : Filesystem.Program α) : Prop :=
  ∀ before request observed, Prefix program (before ++ [(request, observed)]) → request.op = .read →
    Nonempty (GuardedCopyCall before request observed)

private theorem noRead_last {α : Type} {program : Filesystem.Program α}
    (profile : RequestProgram NoRead program) {before : List (Request × Option Reply)}
    {request : Request} {observed : Option Reply}
    (source : Prefix program (before ++ [(request, observed)])) (reading : request.op = .read) : False :=
  request_prefix profile source (request, observed) (by simp) reading

theorem noRead_sources {α : Type} {program : Filesystem.Program α} (profile : RequestProgram NoRead program) :
    ReadSources program := fun _ _ _ source reading => False.elim (noRead_last profile source reading)

theorem read_sources_bind {α β : Type} {program : Filesystem.Program α} {next : α → Filesystem.Program β}
    (first : ReadSources program) (tail : ∀ value, ReadSources (next value)) : ReadSources (program.bind next) := by
  intro before request observed active reading
  rcases filesystem_last_bind_split _ _ active with earlier |
      ⟨initial, value, inside, returned, ending, shape⟩
  · exact first _ _ _ earlier reading
  · obtain ⟨source⟩ := tail value _ _ _ ending reading
    exact ⟨shape ▸ source.prepend (Publication.completed initial)⟩

private theorem noRead_call_tail {α : Type} {operation : Request} {next : Reply → Filesystem.Program α}
    (notRead : NoRead operation) {before : List (Request × Option Reply)}
    {request : Request} {observed : Option Reply}
    (active : Prefix (.call operation next) (before ++ [(request, observed)])) (reading : request.op = .read) :
    ∃ reply inside, before = (operation, some reply) :: inside ∧
      Prefix (next reply) (inside ++ [(request, observed)]) := by
  cases before with
  | nil =>
    cases observed <;> cases active
    all_goals exact False.elim (notRead reading)
  | cons event rest =>
    cases rest with
    | nil =>
      change Prefix (.call operation next) [event, (request, observed)] at active
      cases active with
      | returned _ _ reply events source => exact ⟨reply, [], rfl, source⟩
    | cons second rest =>
      change Prefix (.call operation next) (event :: second :: (rest ++ [(request, observed)])) at active
      cases active with
      | returned _ _ reply events source => exact ⟨reply, second :: rest, rfl, source⟩

private theorem pure_no_read {α : Type} (value : α) : ReadSources (.pure value) := noRead_sources (.pure _)

private theorem guarded_copy_read {fd : UInt64} (start : GuardedCopyStart fd) (limit : Nat)
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (active : Prefix ((copyOpened fd limit).bind (closeResult fd)) (before ++ [(request, observed)]))
    (reading : request.op = .read) :
    Nonempty (GuardedCopyCall (Publication.completed start.events ++ before) request observed) := by
  rcases filesystem_last_bind_split _ _ active with copying |
      ⟨initial, result, inside, returned, ending, shape⟩
  · exact ⟨⟨fd, limit, start, [], before, copying, by simp⟩⟩
  · exact False.elim (noRead_last (closeResult_noRead _ _) ending reading)

private theorem after_copy_read {fd : UInt64} (start : GuardedCopyStart fd) (limit : Nat)
    {α : Type} (next : Result CopiedFile → Filesystem.Program α)
    (following : ∀ result, ReadSources (next result))
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (active : Prefix (((copyOpened fd limit).bind (closeResult fd)).bind next)
      (before ++ [(request, observed)])) (reading : request.op = .read) :
    Nonempty (GuardedCopyCall (Publication.completed start.events ++ before) request observed) := by
  rcases filesystem_last_bind_split _ _ active with copying |
      ⟨initial, result, inside, returned, ending, shape⟩
  · exact guarded_copy_read start limit copying reading
  · obtain ⟨source⟩ := following result _ _ _ ending reading
    have produced := source.prepend (Publication.completed start.events ++ Publication.completed initial)
    exact ⟨by simpa only [shape, List.append_assoc] using produced⟩

-- §FS-host-boundary.snapshot: Every recursive file read follows the actual final-child guard.
theorem traversal_read_sources (fuel : Nat) :
    (∀ limits fd prefixName state, ReadSources (Snapshot.walk fuel limits fd prefixName state)) ∧
    (∀ limits parent prefixName names state, ReadSources (Snapshot.walkChildren fuel limits parent prefixName names state)) := by
  induction fuel with
  | zero =>
    constructor
    · intro limits fd prefixName state
      simpa only [Snapshot.walk] using noRead_sources (closeResult_noRead fd
        (.error "snapshot traversal made no bounded progress" : Result Snapshot.State))
    · intro limits parent prefixName names state
      cases names <;> exact pure_no_read _
  | succ fuel ih =>
    constructor
    · intro limits fd prefixName state before request observed active reading
      unfold Snapshot.walk at active
      obtain ⟨initial, afterInitial, initialShape, rest⟩ := noRead_call_tail
        (by change Op.stat ≠ Op.read; decide) active reading
      split at rest
      · exact False.elim (noRead_last (closeResult_noRead _ _) rest reading)
      · split at rest
        · exact False.elim (noRead_last (closeResult_noRead _ _) rest reading)
        · obtain ⟨opened, afterOpened, openedShape, rest⟩ := noRead_call_tail
            (by change Op.dirOpen ≠ Op.read; decide) rest reading
          split at rest
          · exact False.elim (noRead_last (closeResult_noRead _ _) rest reading)
          · split at rest
            · exact False.elim (noRead_last (.pure _) rest reading)
            · dsimp only at rest
              split at rest
              · exact False.elim (noRead_last (.pure _) rest reading)
              · rcases filesystem_last_bind_split _ _ rest with enumerating |
                    ⟨listing, result, afterListing, listed, rest, listingShape⟩
                · exact False.elim (noRead_last (enumerate_noRead _ _ _ _ _) enumerating reading)
                · cases result with
                  | error => exact False.elim (noRead_last (closeDirectory_noRead _ _ _) rest reading)
                  | ok names =>
                    rcases filesystem_last_bind_split _ _ rest with children |
                        ⟨copied, result, afterCopied, copiedSource, rest, copiedShape⟩
                    · obtain ⟨source⟩ := ih.2 _ _ _ _ _ _ _ _ children reading
                      have earlier := source.prepend ([( {op := .stat, first := fd}, some initial),
                        ({op := .dirOpen, first := fd}, some opened)] ++ Publication.completed listing)
                      exact ⟨by simpa only [initialShape, openedShape, listingShape, List.cons_append,
                        List.nil_append, List.append_assoc] using earlier⟩
                    · cases result with
                      | error => exact False.elim (noRead_last (closeDirectory_noRead _ _ _) rest reading)
                      | ok state =>
                        obtain ⟨reply, afterFinal, finalShape, rest⟩ := noRead_call_tail
                          (by change Op.stat ≠ Op.read; decide) rest reading
                        split at rest
                        · exact False.elim (noRead_last (closeDirectory_noRead _ _ _) rest reading)
                        · exact False.elim (noRead_last (closeDirectory_noRead _ _ _) rest reading)
    · intro limits parent prefixName names state before request observed active reading
      cases names with
      | nil => exact False.elim (noRead_last (.pure _) active reading)
      | cons name names =>
        unfold Snapshot.walkChildren at active
        split at active
        · exact False.elim (noRead_last (.pure _) active reading)
        · split at active
          · exact False.elim (noRead_last (.pure _) active reading)
          · split at active
            · exact False.elim (noRead_last (.pure _) active reading)
            · dsimp only at active
              split at active
              · rcases filesystem_last_bind_split _ _ active with opening |
                    ⟨opening, opened, afterOpening, openSource, rest, openShape⟩
                · exact False.elim (noRead_last (sourceOpenAt_noRead _ _ _) opening reading)
                · cases opened with
                  | error => exact False.elim (noRead_last (.pure _) rest reading)
                  | ok fd =>
                    obtain ⟨information, afterInformation, infoShape, rest⟩ := noRead_call_tail
                      (by change Op.stat ≠ Op.read; decide) rest reading
                    split at rest
                    · exact False.elim (noRead_last (closeResult_noRead _ _) rest reading)
                    · rename_i stat parsed
                      split at rest
                      · split at rest
                        · exact False.elim (noRead_last (closeResult_noRead _ _) rest reading)
                        · rename_i nextState appended
                          have permitted := read_sources_bind (next := fun result => match result with
                            | .error error => pure (.error error)
                            | .ok after => Snapshot.walkChildren fuel limits parent prefixName names after)
                            (ih.1 limits fd ((prefixName ++ name) ++ "/") nextState) (fun result => by
                            cases result with
                            | error => exact pure_no_read _
                            | ok after => exact ih.2 _ _ _ _ _)
                          obtain ⟨source⟩ := permitted _ _ _ rest reading
                          have earlier := source.prepend (Publication.completed opening ++
                            [({op := .stat, first := fd}, some information)])
                          exact ⟨by simpa only [openShape, infoShape, List.append_assoc, List.cons_append, List.nil_append] using earlier⟩
                      · split at rest
                        · rename_i regular
                          have fields : stat.regular = true ∧ stat.links = 1 := by simpa using regular
                          let start := GuardedCopyStart.child parent name.toUTF8 fd opening openSource
                            information stat parsed fields.1 fields.2
                          have tails : ∀ (result : Result CopiedFile), ReadSources (match result with
                              | .error error => pure (.error error)
                              | .ok copied => (Filesystem.hash copied.bytes).bind fun hashed =>
                                match hashed with
                                | .error error => pure (.error error)
                                | .ok digest =>
                                  match Snapshot.addBlob state.blobs digest copied.bytes with
                                  | .error error => pure (.error error)
                                  | .ok blobs =>
                                    let entry := Snapshot.Entry.file ⟨prefixName ++ name, by assumption⟩
                                      (copied.stat.mode &&& 73 != 0) copied.bytes.size digest
                                    match Snapshot.appendEntry limits { state with blobs := blobs } entry with
                                    | .error error => pure (.error error)
                                    | .ok after => Snapshot.walkChildren fuel limits parent prefixName names after) := by
                            intro result
                            cases result with
                            | error => exact pure_no_read _
                            | ok copied =>
                              apply read_sources_bind (noRead_sources (hash_noRead _))
                              intro hashed
                              cases hashed with
                              | error => exact pure_no_read _
                              | ok digest =>
                                dsimp only
                                split
                                · exact pure_no_read _
                                · split
                                  · exact pure_no_read _
                                  · exact ih.2 _ _ _ _ _
                          obtain ⟨source⟩ := after_copy_read start _ _ tails rest reading
                          exact ⟨by simpa only [openShape, infoShape, GuardedCopyStart.events,
                            Publication.completed, List.map_append, List.map_singleton, List.append_assoc,
                            List.cons_append, List.nil_append, start]
                            using source⟩
                        · exact False.elim (noRead_last (closeResult_noRead _ _) rest reading)
              · exact False.elim (noRead_last (.pure _) active reading)

theorem workspace_read_sources (workspace : Option ByteArray) (limits : Snapshot.Limits) :
    ReadSources (Snapshot.copyWorkspace workspace limits) := by
  cases workspace with
  | none => exact pure_no_read _
  | some path =>
    unfold Snapshot.copyWorkspace
    apply read_sources_bind (noRead_sources (sourceOpen_noRead _ _))
    intro result
    cases result with
    | error => exact pure_no_read _
    | ok fd => exact (traversal_read_sources _).1 _ _ _ _

theorem file_read_sources (path : ByteArray) (limit : Nat) : ReadSources (SourcePaths.copyFile path limit) := by
  intro before request observed active reading
  unfold SourcePaths.copyFile at active
  rcases filesystem_last_bind_split _ _ active with opening |
      ⟨opening, result, inside, opened, rest, shape⟩
  · exact False.elim (noRead_last (sourceOpen_noRead _ _) opening reading)
  · cases result with
    | error => exact False.elim (noRead_last (.pure _) rest reading)
    | ok fd =>
      obtain ⟨source⟩ := guarded_copy_read (.path path fd opening opened) limit rest reading
      exact ⟨by simpa only [GuardedCopyStart.events] using shape ▸ source⟩

theorem stdin_read_sources (stdin : Snapshot.Stdin) (limit : Nat) : ReadSources (Snapshot.copyStdin stdin limit) := by
  cases stdin with
  | absent => exact pure_no_read _
  | bytes bytes =>
    simp only [Snapshot.copyStdin]
    split <;> exact pure_no_read _
  | file path => exact read_sources_bind (file_read_sources _ _) (fun _ => pure_no_read _)

-- §FS-host-boundary.snapshot: The actual complete freeze caller preserves every guarded-read cut.
theorem freeze_read_sources (workspace : Option ByteArray) (stdin : Snapshot.Stdin) (limits : Snapshot.Limits) :
    ReadSources (Snapshot.freeze workspace stdin limits) := by
  unfold Snapshot.freeze
  split
  · exact pure_no_read _
  · apply read_sources_bind (workspace_read_sources _ _)
    intro copied
    cases copied with
    | error => exact pure_no_read _
    | ok state =>
      apply read_sources_bind (stdin_read_sources _ _)
      intro copiedInput
      cases copiedInput with
      | error => exact pure_no_read _
      | ok input =>
        apply read_sources_bind (noRead_sources (identify_noRead _))
        intro treeHash
        cases treeHash with
        | error => exact pure_no_read _
        | ok treeDigest =>
          apply read_sources_bind (noRead_sources (identify_noRead _))
          intro inputHash
          cases inputHash <;> exact pure_no_read _

theorem guarded_copy_call_descriptor {before : List (Request × Option Reply)} {request : Request}
    {observed : Option Reply} (source : GuardedCopyCall before request observed) (reading : request.op = .read) :
    request.first = source.fd :=
  request_prefix (copyOpened_reads_descriptor _ _) source.active (request, observed) (by simp) reading

end LeanCage.Host.Kernel
