import CallerPrefixCuts
import PublicationProofs.Loops
import FilesystemLoweredReads

namespace LeanCage.Host.BootstrapProofs
open Filesystem

-- §FS-host-boundary.caller: This is the actual loader's pure inventory-loop body.
-- The equality used below checks its complete executable expansion.
private def inventoryBody (root : String) (entry : String × Json.Value)
    (state : Option (Result Validation.Bundle) × List String) :
    Filesystem.Program (ForInStep (Option (Result Validation.Bundle) × List String)) := do
  let directories := state.2
  let (name, value) := entry
  if !Validation.canonicalName name then
    return .done (some (.error "noncanonical bundle component path"), directories)
  let .string digest := value
    | return .done (some (.error "invalid bundle component digest"), directories)
  if digest.utf8ByteSize != 64 || !digest.toList.all (fun c =>
      ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')) then
    return .done (some (.error "invalid bundle component digest"), directories)
  if name.startsWith "lib/" then
    let parent := String.intercalate "/" (name.splitOn "/").dropLast
    let directory := root ++ "/" ++ parent
    if !directories.contains directory then
      return .yield (none, directory :: directories)
  return .yield (none, directories)

private theorem inventory_done_error (root : String) (entry : String × Json.Value)
    (state after : Option (Result Validation.Bundle) × List String)
    {events : List (Request × Reply)}
    (source : Returns (inventoryBody root entry state) events (.done after)) :
    ∃ error, after.1 = some (.error error) := by
  rcases entry with ⟨name, value⟩
  unfold inventoryBody at source
  dsimp only at source
  split at source
  · have same := (Snapshot.returns_pure_eq source).2
    cases same
    exact ⟨_, rfl⟩
  · split at source
    · split at source
      · have same := (Snapshot.returns_pure_eq source).2
        cases same
        exact ⟨_, rfl⟩
      · split at source
        · split at source <;> cases source
        · cases source
    · have same := (Snapshot.returns_pure_eq source).2
      cases same
      exact ⟨_, rfl⟩

private theorem inventory_yield_valid (root : String) (entry : String × Json.Value)
    (state after : Option (Result Validation.Bundle) × List String)
    {events : List (Request × Reply)}
    (source : Returns (inventoryBody root entry state) events (.yield after)) :
    Validation.canonicalName entry.1 = true ∧ after.1 = none := by
  rcases entry with ⟨name, value⟩
  unfold inventoryBody at source
  dsimp only at source
  split at source
  · cases source
  · rename_i canonical
    have canonical : Validation.canonicalName name = true := by simpa using canonical
    split at source
    · split at source
      · cases source
      · split at source
        · split at source <;>
            have same := (Snapshot.returns_pure_eq source).2 <;>
            cases same <;> exact ⟨canonical, rfl⟩
        · have same := (Snapshot.returns_pure_eq source).2
          cases same
          exact ⟨canonical, rfl⟩
    · cases source

private theorem inventory_loop_cases (root : String)
    {files : List (String × Json.Value)}
    {before after : Option (Result Validation.Bundle) × List String}
    {events : List (Request × Reply)}
    (source : Publication.ForInTrace (inventoryBody root) files before events after)
    (empty : before.1 = none) :
    (after.1 = none ∧ ∀ field ∈ files, Validation.canonicalName field.1 = true) ∨
      ∃ error, after.1 = some (.error error) := by
  induction source with
  | empty => exact .inl ⟨empty, by simp⟩
  | done item rest before after events source =>
    exact .inr (inventory_done_error root item before after source)
  | yield item rest before middle after first last source tail ih =>
    obtain ⟨canonical, none⟩ := inventory_yield_valid root item before middle source
    rcases ih none with success | failed
    · exact .inl ⟨success.1, by simpa only [List.mem_cons, forall_eq_or_imp] using
        (And.intro canonical success.2)⟩
    · exact .inr failed

structure Loaded (input : ByteArray) (bundle : Validation.Bundle) : Prop where
  root : Validation.rootString input = .ok bundle.root
  inventory : ∃ files, Validation.bundleFiles bundle.manifest = some files ∧
    ∀ field ∈ files, Validation.canonicalName field.1 = true

structure ManifestRead (input : ByteArray) (bundle : Validation.Bundle)
    (events : List (Request × Reply)) where
  raw : ByteArray
  reading : List (Request × Reply)
  following : List (Request × Reply)
  root : Validation.rootString input = .ok bundle.root
  copied : Returns (readBounded (bundle.root ++ "/manifest.json").toUTF8 treeMax) reading (.ok raw)
  trace : events = reading ++ following
  parsed : Json.parse raw treeMax = .ok bundle.manifest

-- §FS-host-boundary.caller: Success requires the whole original inventory loop,
-- so every actual component path is canonical, including entries late in the list.
theorem load_bundle_source (input : ByteArray) {bundle : Validation.Bundle}
    {events : List (Request × Reply)}
    (source : Returns (Validation.loadBundle input) events (.ok bundle)) : Loaded input bundle := by
  unfold Validation.loadBundle at source
  split at source
  · rename_i root selected
    obtain ⟨_, raw, _, _, source, _⟩ := Snapshot.returns_bind_split _ _ source
    cases raw with
    | error => cases source
    | ok raw =>
      obtain ⟨_, digest, _, _, source, _⟩ := Snapshot.returns_bind_split _ _ source
      cases digest with
      | error => cases source
      | ok digest =>
        obtain ⟨_, parsed, _, parsing, source, _⟩ := Snapshot.returns_bind_split _ _ source
        have same := (Snapshot.returns_pure_eq parsing).2
        subst parsed
        split at source
        · rename_i manifest parsed
          split at source
          · cases source
          · split at source
            · rename_i files inventory
              obtain ⟨loopEvents, state, _, loopSource, source, _⟩ := Snapshot.returns_bind_split _ _ source
              have loopSource' : Returns (forIn files (none, []) (inventoryBody root)) loopEvents state := by
                refine Eq.mp (congrArg (fun program => Returns program loopEvents state) ?_) loopSource
                apply congrArg (fun body => forIn files (none, []) body)
                funext entry state
                rcases entry with ⟨name, value⟩
                rfl
              have traced := Publication.forIn_source _ _ _ loopSource'
              rcases inventory_loop_cases root traced rfl with success | failed
              · simp only [success.1] at source
                have same := (Snapshot.returns_pure_eq source).2
                cases same
                exact ⟨selected, ⟨files, inventory, success.2⟩⟩
              · obtain ⟨error, failed⟩ := failed
                simp only [failed] at source
                cases source
            · cases source
        · cases source
  · cases source

-- §FS-host-boundary.caller: The manifest is parsed from THIS actual read; neither
-- its digest nor a successful later component check supplies the bytes.
theorem load_bundle_manifest_read (input : ByteArray) {bundle : Validation.Bundle}
    {events : List (Request × Reply)}
    (source : Returns (Validation.loadBundle input) events (.ok bundle)) :
    Nonempty (ManifestRead input bundle events) := by
  unfold Validation.loadBundle at source
  split at source
  · rename_i root selected
    obtain ⟨reading, raw, rest, copied, source, trace⟩ := Snapshot.returns_bind_split _ _ source
    cases raw with
    | error => cases source
    | ok raw =>
      obtain ⟨hashing, digest, afterHash, _, source, hashTrace⟩ := Snapshot.returns_bind_split _ _ source
      cases digest with
      | error => cases source
      | ok digest =>
        obtain ⟨parsing, parsed, afterParse, pureParse, source, parseTrace⟩ := Snapshot.returns_bind_split _ _ source
        have same := (Snapshot.returns_pure_eq pureParse).2
        subst parsed
        split at source
        · rename_i manifest parsed
          split at source
          · cases source
          · split at source
            · rename_i files inventory
              obtain ⟨loopEvents, state, _, loopSource, source, _⟩ := Snapshot.returns_bind_split _ _ source
              have loopSource' : Returns (forIn files (none, []) (inventoryBody root)) loopEvents state := by
                refine Eq.mp (congrArg (fun program => Returns program loopEvents state) ?_) loopSource
                apply congrArg (fun body => forIn files (none, []) body)
                funext entry state
                rcases entry with ⟨name, value⟩
                rfl
              rcases inventory_loop_cases root (Publication.forIn_source _ _ _ loopSource') rfl with success | failed
              · simp only [success.1] at source
                have result := (Snapshot.returns_pure_eq source).2
                cases result
                exact ⟨⟨raw, reading, rest, selected, copied, trace, parsed⟩⟩
              · obtain ⟨error, failed⟩ := failed
                simp only [failed] at source
                cases source
            · cases source
        · cases source
  · cases source

def ExactOpen (path : ByteArray) (request : Request) : Prop :=
  request.op = .openAt → request = {op := .openAt, first := cwd, second := readFlags, left := path}

def BundleOpen (root : String) (request : Request) : Prop :=
  request.op = .openAt → ∃ name, Validation.canonicalName name = true ∧
    request = {op := .openAt, first := cwd, second := readFlags, left := (root ++ "/" ++ name).toUTF8}

theorem manifest_canonical : Validation.canonicalName "manifest.json" = true := by decide_cbv

private theorem profile_requests {α : Type} {program : Filesystem.Program α}
    {allowed required : Request → Prop} (profile : RequestProfile allowed program)
    (includes : ∀ request, allowed request → required request) : RequestProgram required program := by
  induction profile with
  | pure => exact .pure _
  | call request next permitted rest ih => exact .call (includes request permitted) ih

private theorem copy_requests {fd : UInt64} {limit : Nat} {allowed : Request → Prop}
    (permitted : ∀ request, (request.op = .read ∨ request.op = .stat) → allowed request) :
    RequestProgram allowed (copyOpened fd limit) :=
  profile_requests (Kernel.Lowered.copy_profile fd limit) permitted

private theorem close_requests {α : Type} (fd : UInt64) (result : Result α) {allowed : Request → Prop}
    (permitted : allowed {op := .close, first := fd}) : RequestProgram allowed (closeResult fd result) := by
  apply RequestProgram.call permitted
  intro reply
  cases result with
  | error => exact .pure _
  | ok => dsimp only; split <;> exact .pure _

theorem read_bounded_opens (path : ByteArray) (limit : Nat) :
    RequestProgram (ExactOpen path) (readBounded path limit) := by
  unfold readBounded
  apply request_bind
  · unfold copyAt
    split
    · exact .pure _
    · apply RequestProgram.call (fun _ => rfl)
      intro reply
      split
      · exact .pure _
      · apply request_bind
        · apply copy_requests
          intro request kind opening
          rcases kind with reading | stat
          · rw [reading] at opening; cases opening
          · rw [stat] at opening; cases opening
        · intro result
          exact close_requests _ result (by intro impossible; cases impossible)
  · intro result
    exact .pure _

private theorem hash_requests (bytes : ByteArray) {allowed : Request → Prop}
    (permitted : allowed {op := .sha256, left := bytes}) : RequestProgram allowed (Filesystem.hash bytes) := by
  apply RequestProgram.call permitted
  intro reply
  split <;> exact .pure _

-- §FS-host-boundary.caller: Even an interrupted first manifest open has already
-- decoded the exact caller bundle field. No later loader success is required.
theorem load_bundle_opens (input : ByteArray) :
    RequestProgram (fun request => request.op = .openAt → ∃ root,
      Validation.rootString input = .ok root ∧
        request = {op := .openAt, first := cwd, second := readFlags, left := (root ++ "/manifest.json").toUTF8})
      (Validation.loadBundle input) := by
  unfold Validation.loadBundle
  split
  · rename_i root selected
    apply request_bind
    · apply request_weaken (read_bounded_opens _ _)
      intro request permitted opening
      exact ⟨root, selected, permitted opening⟩
    · intro raw
      cases raw with
      | error => exact .pure _
      | ok raw =>
        apply request_bind (hash_requests raw (by intro impossible; cases impossible))
        intro digest
        cases digest with
        | error => exact .pure _
        | ok digest =>
          apply request_bind (.pure _)
          intro parsed
          cases parsed with
          | error => exact .pure _
          | ok manifest =>
            dsimp only
            split
            · exact .pure _
            · split
              · apply request_bind (request_forIn _ _ _ _ ?_)
                · intro state
                  rcases state with ⟨stopped, directories⟩
                  cases stopped <;> exact .pure _
                · intro entry member state
                  rcases entry with ⟨name, value⟩
                  dsimp only
                  repeat' first | exact .pure _ | split
              · exact .pure _
  · exact .pure _

theorem identified_opens (bundle : Validation.Bundle) (name : String) (limit : Nat)
    (canonical : Validation.canonicalName name = true) :
    RequestProgram (BundleOpen bundle.root) (Validation.copyIdentified bundle name limit) := by
  unfold Validation.copyIdentified
  split
  · split
    · apply request_bind
      · apply request_weaken (read_bounded_opens _ _)
        intro request permitted opening
        exact ⟨name, canonical, permitted opening⟩
      · intro content
        cases content with
        | error => exact .pure _
        | ok bytes =>
          apply request_bind (hash_requests bytes (by intro impossible; cases impossible))
          intro digest
          cases digest with
          | error => exact .pure _
          | ok value => dsimp only; split <;> exact .pure _
    · exact .pure _
  · exact .pure _

theorem checked_file_opens (bundle : Validation.Bundle) (name : String) (limit : Nat)
    (canonical : Validation.canonicalName name = true) :
    RequestProgram (BundleOpen bundle.root) (Validation.checkFile bundle name limit) :=
  request_bind (identified_opens bundle name limit canonical) (fun _ => .pure _)

-- §FS-host-boundary.caller: Each check loop access uses the SAME loaded inventory,
-- whose canonicality was established by the actual preceding successful loader.
theorem checked_bundle_opens {input : ByteArray} {bundle : Validation.Bundle}
    (loaded : Loaded input bundle) : RequestProgram (BundleOpen bundle.root) (Validation.checkBundle bundle) := by
  obtain ⟨files, selected, canonical⟩ := loaded.inventory
  unfold Validation.checkBundle
  rw [selected]
  apply request_bind (request_forIn _ _ _ _ ?_)
  · intro result
    rcases result with ⟨stopped, state⟩
    cases stopped <;> exact .pure _
  · intro entry member state
    apply request_bind (checked_file_opens bundle entry.1 workspaceMax (canonical entry member))
    intro result
    cases result <;> exact .pure _

theorem engine_identity_no_open (bundle : Validation.Bundle) :
    RequestProgram (fun request => request.op ≠ .openAt) (Validation.checkEngineIdentity bundle) := by
  unfold Validation.checkEngineIdentity
  split
  · split
    · apply RequestProgram.call (by decide)
      intro reply
      dsimp only [Filesystem.Program.bind]
      split
      · apply request_bind
        · apply request_bind
          · apply copy_requests
            intro request kind opening
            rcases kind with reading | stat
            · rw [reading] at opening; cases opening
            · rw [stat] at opening; cases opening
          · intro result
            exact close_requests _ result (by intro impossible; cases impossible)
        · intro copied
          cases copied with
          | error => exact .pure _
          | ok copied =>
            apply request_bind (hash_requests copied.bytes (by intro impossible; cases impossible))
            intro digest
            cases digest with
            | error => exact .pure _
            | ok digest => dsimp only; split <;> exact .pure _
      · exact .pure _
    · exact .pure _
  · exact .pure _

-- §FS-host-boundary.publication: This source role is deliberately private bootstrap
-- access, and is distinct from caller-selectable public path traversal.
theorem authentication_key_opens {input : ByteArray} {bundle : Validation.Bundle}
    (loaded : Loaded input bundle) :
    RequestProgram (BundleOpen bundle.root) (Publication.authenticationKey bundle) := by
  obtain ⟨files, inventory, canonical⟩ := loaded.inventory
  unfold Publication.authenticationKey
  simp only [inventory]
  split
  · rename_i storedName expected found
    have matchedName := List.find?_some found
    have keySelected : storedName = Publication.keyName := eq_of_beq matchedName
    have keyCanonical : Validation.canonicalName Publication.keyName = true := by
      rw [← keySelected]
      exact canonical (storedName, .string expected) (List.mem_of_find?_eq_some found)
    apply RequestProgram.call (by intro impossible; cases impossible)
    intro uid
    dsimp only [Filesystem.Program.bind]
    split
    · exact .pure _
    · apply RequestProgram.call (fun _ => ⟨Publication.keyName, keyCanonical, rfl⟩)
      intro opened
      dsimp only [Filesystem.Program.bind]
      split
      · apply RequestProgram.call (by intro impossible; cases impossible)
        intro privateReply
        dsimp only [Filesystem.Program.bind]
        split
        · exact close_requests _ _ (by intro impossible; cases impossible)
        · apply request_bind
          · apply request_bind
            · apply copy_requests
              intro request kind opening
              rcases kind with reading | stat
              · rw [reading] at opening; cases opening
              · rw [stat] at opening; cases opening
            · intro result
              exact close_requests _ result (by intro impossible; cases impossible)
          · intro copied
            cases copied with
            | error => exact .pure _
            | ok copied =>
              dsimp only
              split
              · exact .pure _
              · apply request_bind (hash_requests copied.bytes (by intro impossible; cases impossible))
                intro identified
                cases identified with
                | error => exact .pure _
                | ok digest => dsimp only; split <;> exact .pure _
      · exact .pure _
  · exact .pure _

theorem key_gate_opens {input : ByteArray} {bundle : Validation.Bundle} (loaded : Loaded input bundle) :
    RequestProgram (BundleOpen bundle.root) (CallerPrefixCuts.keyGate bundle) :=
  request_bind (authentication_key_opens loaded) (fun _ => .pure _)

theorem startup_no_open (descriptors : List UInt64) :
    RequestProgram (fun request => request.op ≠ .openAt) (Startup.sealDescriptors descriptors) := by
  induction descriptors with
  | nil => exact .pure _
  | cons fd rest ih =>
    apply RequestProgram.call (by intro impossible; cases impossible)
    intro reply
    split
    · exact .pure _
    · exact ih

private theorem packet_exact_no_open (fuel : Nat) (fd : UInt64) (amount : Nat) (bytes : ByteArray) :
    RequestProgram (fun request => request.op ≠ .openAt) (Packet.readExact fuel fd amount bytes) := by
  induction fuel generalizing bytes with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold Packet.readExact
    split
    · exact .pure _
    · split
      · exact .pure _
      · apply RequestProgram.call (by intro impossible; cases impossible)
        intro reply
        repeat' first | exact .pure _ | exact ih _ | split

theorem packet_no_open (fd : UInt64) : RequestProgram (fun request => request.op ≠ .openAt) (Packet.read fd) := by
  unfold Packet.read
  apply request_bind (packet_exact_no_open _ _ _ _)
  intro header
  cases header with
  | error => exact .pure _
  | ok header =>
    dsimp only
    split
    · exact .pure _
    · apply request_bind (packet_exact_no_open _ _ _ _)
      intro payload
      cases payload with
      | error => exact .pure _
      | ok payload =>
        apply RequestProgram.call (by intro impossible; cases impossible)
        intro reply
        dsimp only [Filesystem.Program.bind]
        split
        · exact .pure _
        · split <;> exact .pure _

theorem write_loop_no_open (fuel : Nat) (fd : UInt64) (bytes : ByteArray) (offset : Nat) :
    RequestProgram (fun request => request.op ≠ .openAt) (writeLoop fuel fd bytes offset) := by
  induction fuel generalizing offset with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold writeLoop
    split
    · exact .pure _
    · apply RequestProgram.call (by intro impossible; cases impossible)
      intro reply
      repeat' first | exact .pure _ | exact ih _ | split

end LeanCage.Host.BootstrapProofs
