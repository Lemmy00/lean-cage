import SnapshotProofs.Blobs
import SnapshotProofs.SourcePaths

namespace LeanCage.Host.Snapshot

open Filesystem

inductive PublicPath : String → Prop where
  | first (name : String) (component : ValidComponent name)
      (notPrivate : PrivateNames.reservedBytes name.toUTF8 = false) : PublicPath name
  | child (parent name : String) (before : PublicPath parent) (component : ValidComponent name)
      (notPrivate : PrivateNames.reservedBytes name.toUTF8 = false) : PublicPath (parent ++ "/" ++ name)

def PublicPrefix (prefixName : String) : Prop :=
  prefixName = "" ∨ ∃ parent, PublicPath parent ∧ prefixName = parent ++ "/"

theorem public_child (prefixName name : String) (prefixPublic : PublicPrefix prefixName)
    (component : ValidComponent name) (notPrivate : PrivateNames.reservedBytes name.toUTF8 = false) :
    PublicPath (prefixName ++ name) := by
  rcases prefixPublic with rfl | ⟨parent, before, rfl⟩
  · simpa only [String.empty_append] using PublicPath.first name component notPrivate
  · exact PublicPath.child parent name before component notPrivate

-- §FS-host-boundary.snapshot: Rows are justified by ordered calls and the exact observed copy.
inductive Acquired (limits : Limits) : State → List (Request × Reply) → State → Prop where
  | unchanged (state : State) (events : List (Request × Reply)) : Acquired limits state events state
  | sequence {before middle after : State} {first last : List (Request × Reply)}
      (initial : Acquired limits before first middle) (final : Acquired limits middle last after) :
      Acquired limits before (first ++ last) after
  | directory {before after : State} (parent child : UInt64) (prefixName name : String)
      (component : ValidComponent name) (notPrivate : PrivateNames.reservedBytes name.toUTF8 = false) (path : RelativePath)
      (pathValue : path.text = prefixName ++ name) (publicPath : PublicPath path.text)
      (opened : List (Request × Reply)) (information : Reply) (stat : Stat)
      (descriptorValue : SourceOpening parent name.toUTF8 false opened child) (statValue : parseStat information = some stat)
      (directory : stat.directory = true)
      (appended : appendEntry limits before (.directory path) = .ok after) :
      Acquired limits before
        (opened ++ [({ op := .stat, first := child }, information)]) after
  | file {before after : State} (parent child : UInt64) (prefixName name : String)
      (component : ValidComponent name) (notPrivate : PrivateNames.reservedBytes name.toUTF8 = false) (path : RelativePath)
      (pathValue : path.text = prefixName ++ name) (publicPath : PublicPath path.text)
      (opened : List (Request × Reply)) (information : Reply) (stat : Stat)
      (descriptorValue : SourceOpening parent name.toUTF8 false opened child) (statValue : parseStat information = some stat)
      (regular : stat.regular = true) (linked : stat.links = 1)
      (copied : CopiedFile) (reads : List (Request × Reply)) (closed : Reply) (digest : ByteArray)
      (copyValue : CopiedObservation child reads copied)
      (bounded : copied.bytes.size ≤ limits.workspaceBytes - before.total)
      (closeValue : closed.1 = 0) (closeBytes : closed.2 = .empty) (digestSize : digest.size = 32)
      (blobs : List Blob) (blobValue : addBlob before.blobs digest copied.bytes = .ok blobs)
      (appended : appendEntry limits { before with blobs := blobs }
        (.file path (copied.stat.mode &&& 73 != 0) copied.bytes.size digest) = .ok after) :
      Acquired limits before
        (opened ++ [({ op := .stat, first := child }, information)] ++ reads ++
          [({ op := .close, first := child }, closed),
           ({ op := .sha256, left := copied.bytes }, (0, digest))]) after

theorem acquired_frame {limits : Limits} {before after : State} {events : List (Request × Reply)}
    (observed : Acquired limits before events after) (leading trailing : List (Request × Reply)) :
    Acquired limits before (leading ++ events ++ trailing) after :=
  .sequence (.sequence (.unchanged before leading) observed) (.unchanged after trailing)

theorem appendEntry_update (limits : Limits) (before : State) (entry : Entry) {after : State}
    (accepted : appendEntry limits before entry = .ok after) :
    after.entries = before.entries.push entry ∧ after.tree = before.tree ++ entry.line ∧
      after.count = before.count + 1 ∧ after.total = before.total + entry.size ∧
      after.blobs = before.blobs := by
  unfold appendEntry at accepted
  dsimp only at accepted
  repeat' first | split at accepted | cases accepted
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem appendEntry_blobs (limits : Limits) (before : State) (entry : Entry) {after : State}
    (accepted : appendEntry limits before entry = .ok after) : after.blobs = before.blobs := by
  unfold appendEntry at accepted
  dsimp only at accepted
  repeat' first | split at accepted | cases accepted
  rfl

-- §FS-host-boundary.snapshot: The source producer retains every ordered file acquisition segment.
private theorem walk_acquired_pair (fuel : Nat) :
    (∀ limits fd name state events after,
      PublicPrefix name → Returns (walk fuel limits fd name state) events (.ok after) → Acquired limits state events after) ∧
    (∀ limits fd name names state events after,
      PublicPrefix name → Returns (walkChildren fuel limits fd name names state) events (.ok after) →
        Acquired limits state events after) := by
  induction fuel with
  | zero =>
    constructor
    · intro limits fd name state events after prefixPublic run
      simp only [walk] at run
      have impossible := (closeResult_provenance _ _ run).1
      cases impossible
    · intro limits fd name names state events after prefixPublic run
      cases names with
      | nil => cases run; exact .unchanged state []
      | cons => cases run
  | succ fuel ih =>
    constructor
    · intro limits fd name state events after prefixPublic run
      simp only [walk] at run
      obtain ⟨initialReply, tailEvents, rfl, tail⟩ := returns_call_split run
      split at tail
      · have impossible := (closeResult_provenance _ _ tail).1
        cases impossible
      · split at tail
        · have impossible := (closeResult_provenance _ _ tail).1
          cases impossible
        · obtain ⟨opened, restEvents, rfl, rest⟩ := returns_call_split tail
          split at rest
          · have impossible := (closeResult_provenance _ _ rest).1
            cases impossible
          · split at rest
            · cases rest
            · split at rest
              · cases rest
              · obtain ⟨enumerationEvents, listing, last, listingRun, afterListing, listShape⟩ :=
                  returns_bind_split _ _ rest
                cases listing with
                | error error =>
                  have impossible := closeDirectory_value _ _ afterListing
                  cases impossible
                | ok names =>
                  obtain ⟨childEvents, result, finalEvents, childRun, finished, childShape⟩ :=
                    returns_bind_split _ _ afterListing
                  cases result with
                  | error error =>
                    have impossible := closeDirectory_value _ _ finished
                    cases impossible
                  | ok next =>
                    obtain ⟨finalReply, closedEvents, finalShape, closedRun⟩ := returns_call_split finished
                    split at closedRun
                    · have impossible := closeDirectory_value _ _ closedRun
                      cases impossible
                    · have same := closeDirectory_value _ _ closedRun
                      split at same
                      · cases same
                        have observed := ih.2 _ _ _ _ _ _ _ prefixPublic childRun
                        have framed := acquired_frame observed
                          ([({ op := .stat, first := fd }, initialReply), ({ op := .dirOpen, first := fd }, opened)] ++
                            enumerationEvents)
                          (({ op := .stat, first := fd }, finalReply) :: closedEvents)
                        simpa only [listShape, childShape, finalShape, List.append_assoc,
                          List.cons_append, List.nil_append] using framed
                      · cases same
    · intro limits fd name names state events after prefixPublic run
      cases names with
      | nil => cases run; exact .unchanged state []
      | cons childName remaining =>
        simp only [walkChildren] at run
        split at run
        · cases run
        · rename_i notPrivate
          split at run
          · cases run
          · rename_i component
            split at run
            · cases run
            · split at run
              · rename_i pathValid
                obtain ⟨opening, result, restEvents, openRun, rest, openShape⟩ := returns_bind_split _ _ run
                cases result with
                | error => cases rest
                | ok child =>
                  have owned := sourceOpenAt_source _ _ _ openRun
                  obtain ⟨information, tailEvents, rfl, tail⟩ := returns_call_split rest
                  split at tail
                  · have impossible := (closeResult_provenance _ _ tail).1
                    cases impossible
                  · rename_i stat statValue
                    split at tail
                    · rename_i directory
                      split at tail
                      · have impossible := (closeResult_provenance _ _ tail).1
                        cases impossible
                      · rename_i next appended
                        obtain ⟨childEvents, result, siblingEvents, childRun, siblings, shape⟩ :=
                          returns_bind_split _ _ tail
                        cases result with
                        | error error => cases siblings
                        | ok copied =>
                          have publicPath := public_child name childName prefixPublic (by simpa using component)
                            (Bool.eq_false_iff.mpr notPrivate)
                          have first := Acquired.directory fd child name childName (by simpa using component)
                            (Bool.eq_false_iff.mpr notPrivate)
                            ⟨name ++ childName, pathValid⟩ rfl publicPath opening information stat owned statValue directory appended
                          have child := ih.1 _ _ _ _ _ _ (.inr ⟨name ++ childName, publicPath, rfl⟩) childRun
                          have last := ih.2 _ _ _ _ _ _ _ prefixPublic siblings
                          have observed := Acquired.sequence first (Acquired.sequence child last)
                          simpa only [openShape, shape, List.append_assoc, List.cons_append, List.nil_append] using observed
                    · split at tail
                      · rename_i regular
                        obtain ⟨copyEvents, result, lastEvents, copyRun, hashedRun, copyShape⟩ :=
                          returns_bind_split _ _ tail
                        cases result with
                        | error error => cases hashedRun
                        | ok copied =>
                          obtain ⟨hashEvents, hashed, siblingEvents, hashRun, final, hashShape⟩ :=
                            returns_bind_split _ _ hashedRun
                          cases hashed with
                          | error error => cases final
                          | ok digest =>
                            dsimp only at final
                            split at final
                            · cases final
                            · rename_i blobs blobAdded
                              split at final
                              · cases final
                              · rename_i next appended
                                obtain ⟨reads, input, closes, readRun, closeRun, readShape⟩ :=
                                  returns_bind_split _ _ copyRun
                                obtain ⟨same, closed, closeShape, closeValue, closeBytes⟩ :=
                                  closeResult_provenance _ _ closeRun
                                cases same
                                obtain ⟨bounded, copiedValue⟩ := copyOpened_provenance _ _ readRun
                                obtain ⟨reply, exactHash, zero, bytesEqual, digestSize⟩ := hash_provenance _ hashRun
                                have replyEqual : reply = (0, digest) := Prod.ext zero bytesEqual
                                have regularFields : stat.regular = true ∧ stat.links = 1 := by simpa using regular
                                have publicPath := public_child name childName prefixPublic (by simpa using component)
                                  (Bool.eq_false_iff.mpr notPrivate)
                                have source := Acquired.file fd child name childName (by simpa using component)
                                  (Bool.eq_false_iff.mpr notPrivate)
                                  ⟨name ++ childName, pathValid⟩ rfl publicPath opening information stat owned statValue
                                  regularFields.1 regularFields.2 copied reads closed digest copiedValue bounded
                                  closeValue closeBytes digestSize blobs blobAdded appended
                                have sibling := ih.2 _ _ _ _ _ _ _ prefixPublic final
                                have observed := Acquired.sequence source sibling
                                simpa only [openShape, copyShape, hashShape, readShape, closeShape, exactHash, replyEqual,
                                  List.append_assoc, List.cons_append, List.nil_append] using observed
                      · have impossible := (closeResult_provenance _ _ tail).1
                        cases impossible
              · cases run

theorem walk_acquired (fuel : Nat) (limits : Limits) (fd : UInt64) (name : String) (before : State)
    {events : List (Request × Reply)} {after : State}
    (prefixPublic : PublicPrefix name)
    (run : Returns (walk fuel limits fd name before) events (.ok after)) :
    Acquired limits before events after := (walk_acquired_pair fuel).1 _ _ _ _ _ _ prefixPublic run

theorem walkChildren_acquired (fuel : Nat) (limits : Limits) (fd : UInt64) (name : String)
    (names : List String) (before : State) {events : List (Request × Reply)} {after : State}
    (prefixPublic : PublicPrefix name)
    (run : Returns (walkChildren fuel limits fd name names before) events (.ok after)) :
    Acquired limits before events after := (walk_acquired_pair fuel).2 _ _ _ _ _ _ _ prefixPublic run

def WorkspaceOrigin (workspace : Option ByteArray) (limits : Limits)
    (events : List (Request × Reply)) (after : State) : Prop :=
  match workspace with
  | none => events = [] ∧ after = {}
  | some path => ∃ fd opening middle,
      events = opening ++ middle ∧ SourcePathObservation path true opening fd ∧
      Returns (walk (2 * limits.workspaceInodes + 1) limits fd "" {}) middle (.ok after)

theorem copyWorkspace_origin (workspace : Option ByteArray) (limits : Limits)
    {events : List (Request × Reply)} {after : State}
    (run : Returns (copyWorkspace workspace limits) events (.ok after)) :
    WorkspaceOrigin workspace limits events after := by
  cases workspace with
  | none => cases run; exact ⟨rfl, rfl⟩
  | some path =>
    simp only [copyWorkspace] at run
    obtain ⟨opening, result, middle, opened, final, shape⟩ := returns_bind_split _ _ run
    cases result with
    | error => cases final
    | ok fd => exact ⟨fd, opening, middle, shape, sourceOpen_source _ _ opened, final⟩

-- §FS-host-boundary.snapshot: Checked retained ancestors supply the actual root descriptor.
theorem copyWorkspace_acquired (workspace : Option ByteArray) (limits : Limits)
    {events : List (Request × Reply)} {after : State}
    (run : Returns (copyWorkspace workspace limits) events (.ok after)) :
    Acquired limits {} events after := by
  have origin := copyWorkspace_origin _ _ run
  cases workspace with
  | none => rcases origin with ⟨rfl, rfl⟩; exact .unchanged {} []
  | some path =>
    obtain ⟨fd, opening, middle, rfl, _, walked⟩ := origin
    have observed := walk_acquired _ _ _ _ _ (.inl rfl) walked
    simpa only [List.append_nil] using acquired_frame observed opening []

end LeanCage.Host.Snapshot
