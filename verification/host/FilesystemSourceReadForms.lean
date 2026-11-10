import BootstrapProofs
import FilesystemCwdFrames

namespace LeanCage.Host.SourceReadForms
open Filesystem Snapshot

def DescriptorFits (fd : UInt64) : Prop := fd.toNat ≤ 2147483647

def ReadForm (request : Request) : Prop :=
  request.op = .openAt →
    request = {op := .openAt, first := cwd, second := directoryFlags, left := "/".toUTF8} ∨
    request = {op := .openAt, first := cwd, second := directoryFlags, left := ".".toUTF8} ∨
    DescriptorFits request.first ∧ (request.second = directoryFlags ∨ request.second = readFlags) ∧
      Directories.component request.left = true ∧ PrivateNames.reservedBytes request.left = false

theorem descriptor_fits {reply : Reply} {fd : UInt64} (recognized : descriptor reply = some fd) :
    DescriptorFits fd := by
  unfold descriptor at recognized
  split at recognized
  · cases recognized
  · rename_i bounded
    have fields : nativeError reply = false ∧ reply.2.isEmpty = true ∧ reply.1.toNat ≤ 2147483647 := by
      simpa [and_assoc] using bounded
    have same := Option.some.inj recognized
    simpa only [DescriptorFits, same] using fields.2.2

theorem descriptor_not_cwd {fd : UInt64} (fits : DescriptorFits fd) : fd ≠ cwd := by
  intro same
  subst fd
  change 18446744073709551516 ≤ 2147483647 at fits
  omega

theorem bind_requests {α β : Type} {program : Filesystem.Program α} {next : α → Filesystem.Program β}
    {post : α → Prop} (source : RequestProgram ReadForm program) (result : PostProgram post program)
    (tail : ∀ value, post value → RequestProgram ReadForm (next value)) :
    RequestProgram ReadForm (program.bind next) := by
  induction source with
  | pure value =>
    cases result with
    | pure property => exact tail value property
  | call permitted rest ih =>
    cases result with
    | call following => exact .call permitted (fun reply => ih reply (following reply))

theorem close_requests {α : Type} (fd : UInt64) (result : Result α) :
    RequestProgram ReadForm (closeResult fd result) := by
  apply RequestProgram.call (by intro impossible; cases impossible)
  intro reply
  cases result with
  | error => exact .pure _
  | ok => dsimp only; split <;> exact .pure _

theorem public_handle_requests (fd : UInt64) : RequestProgram ReadForm (SourcePaths.publicHandle fd) := by
  unfold SourcePaths.publicHandle
  apply RequestProgram.call (by intro impossible; cases impossible)
  intro reply
  split
  · exact .pure _
  · exact close_requests _ _

theorem source_open_at_post (parent : UInt64) (name : ByteArray) (directory : Bool) :
    PostProgram (Successful DescriptorFits) (SourcePaths.openAt parent name directory) := by
  apply post_of_returns
  intro events result source
  cases result with
  | error => trivial
  | ok fd =>
    obtain ⟨reply, observed, shape, recognized, rest⟩ := sourceOpenAt_source parent name directory source
    exact descriptor_fits recognized

theorem source_open_at_requests (parent : UInt64) (name : ByteArray) (directory : Bool)
    (form : ReadForm {op := .openAt, first := parent, second := if directory then directoryFlags else readFlags, left := name}) :
    RequestProgram ReadForm (SourcePaths.openAt parent name directory) := by
  unfold SourcePaths.openAt
  apply RequestProgram.call form
  intro reply
  split
  · exact .pure _
  · exact public_handle_requests _

theorem release_parent_post (parent : UInt64) (child : Result UInt64) (fits : Successful DescriptorFits child) :
    PostProgram (Successful DescriptorFits) (SourcePaths.releaseParent parent child) := by
  unfold SourcePaths.releaseParent
  apply post_bind (closeResult_post DescriptorFits parent child fits)
  intro result valid
  cases result with
  | ok => exact .pure valid
  | error =>
    cases child with
    | error => exact .pure True.intro
    | ok fd => exact closeResult_post DescriptorFits fd (.error _) True.intro

theorem release_parent_requests (parent : UInt64) (child : Result UInt64) :
    RequestProgram ReadForm (SourcePaths.releaseParent parent child) := by
  unfold SourcePaths.releaseParent
  apply request_bind (close_requests _ _)
  intro result
  cases result with
  | ok => exact .pure _
  | error =>
    cases child with
    | error => exact .pure _
    | ok => exact close_requests _ _

theorem walk_post (parent : UInt64) (names : List ByteArray) (directory : Bool) (fits : DescriptorFits parent) :
    PostProgram (Successful DescriptorFits) (SourcePaths.walk parent names directory) := by
  induction names generalizing parent with
  | nil => exact .pure fits
  | cons name rest ih =>
    unfold SourcePaths.walk
    apply post_bind (source_open_at_post _ _ _)
    intro opened valid
    apply post_bind (release_parent_post _ _ valid)
    intro released valid
    cases released with
    | error => exact .pure True.intro
    | ok child => exact ih child valid

-- §FS-host-boundary.snapshot: Every actual child open uses a checked component and
-- a descriptor number obtained from a recognized prior reply, even on later loss.
theorem walk_requests (parent : UInt64) (names : List ByteArray) (directory : Bool)
    (fits : DescriptorFits parent)
    (checked : ∀ name ∈ names, Directories.component name = true ∧ PrivateNames.reservedBytes name = false) :
    RequestProgram ReadForm (SourcePaths.walk parent names directory) := by
  induction names generalizing parent with
  | nil => exact .pure _
  | cons name rest ih =>
    unfold SourcePaths.walk
    apply bind_requests (source_open_at_requests _ _ _ (by
      intro opening
      exact .inr (.inr ⟨fits, (by cases directory || !rest.isEmpty <;> simp), checked name (by simp)⟩)))
      (source_open_at_post _ _ _)
    intro opened valid
    apply bind_requests (release_parent_requests _ _) (release_parent_post _ _ valid)
    intro released valid
    cases released with
    | error => exact .pure _
    | ok child => exact ih child valid (by intro name member; exact checked name (by simp [member]))

private theorem identity_requests (fd : UInt64) : RequestProgram ReadForm (SourcePaths.identity fd) := by
  apply RequestProgram.call (by intro impossible; cases impossible)
  intro reply
  split <;> exact .pure _

theorem ancestry_requests (fuel : Nat) (current : UInt64) (root : ByteArray) (fits : DescriptorFits current) :
    RequestProgram ReadForm (SourcePaths.ancestry fuel current root) := by
  induction fuel generalizing current with
  | zero => exact close_requests _ _
  | succ fuel ih =>
    unfold SourcePaths.ancestry
    apply request_bind (identity_requests _)
    intro observed
    cases observed with
    | error => exact close_requests _ _
    | ok observed =>
      dsimp only
      split
      · exact close_requests _ _
      · apply bind_requests (source_open_at_requests current "..".toUTF8 true
          (by
            intro opening
            exact .inr (.inr ⟨fits, .inl rfl,
              by change Directories.component "..".toUTF8 = true; decide_cbv,
              by change PrivateNames.reservedBytes "..".toUTF8 = false; decide⟩)))
          (source_open_at_post _ _ _)
        intro parent valid
        apply bind_requests (release_parent_requests _ _) (release_parent_post _ _ valid)
        intro released valid
        cases released with
        | error => exact .pure _
        | ok parent => exact ih parent valid

theorem check_ancestry_requests (base : UInt64) (fits : DescriptorFits base) :
    RequestProgram ReadForm (SourcePaths.checkAncestry base) := by
  unfold SourcePaths.checkAncestry
  apply request_bind (source_open_at_requests cwd "/".toUTF8 true (fun _ => .inl rfl))
  intro root
  cases root with
  | error => exact .pure _
  | ok root =>
    apply request_bind (request_bind (identity_requests _) (close_requests _))
    intro observed
    cases observed with
    | error => exact .pure _
    | ok rootIdentity =>
      apply bind_requests (source_open_at_requests base ".".toUTF8 true
        (by
          intro opening
          exact .inr (.inr ⟨fits, .inl rfl,
            by change Directories.component ".".toUTF8 = true; decide_cbv,
            by change PrivateNames.reservedBytes ".".toUTF8 = false; decide⟩)))
        (source_open_at_post _ _ _)
      intro duplicate valid
      cases duplicate with
      | error => exact .pure _
      | ok duplicate => exact ancestry_requests _ _ _ valid

def StartedValid (selected : SourcePaths.Started) : Prop :=
  DescriptorFits selected.base ∧ ∀ name ∈ selected.parts,
    Directories.component name = true ∧ PrivateNames.reservedBytes name = false

theorem start_post (path : ByteArray) : PostProgram (Successful StartedValid) (SourcePaths.start path) := by
  apply post_of_returns
  intro events result source
  cases result with
  | error => trivial
  | ok selected =>
    have actual := sourceStart_source path source
    cases actual with
    | absolute events components selectedPath opening =>
      obtain ⟨reply, attributeReply, trace, recognized, rest⟩ := opening
      exact ⟨descriptor_fits recognized, Kernel.source_components_are_components _ _ components⟩
    | relative events checking spelling components selectedPath opening spelled checked =>
      obtain ⟨reply, attributeReply, trace, recognized, rest⟩ := opening
      exact ⟨descriptor_fits recognized, Kernel.source_components_are_components _ _ components⟩

-- §FS-host-boundary.caller: Relative inputs retain the genuine CWD FD; getcwd
-- checks a spelling without selecting a replacement directory.
theorem start_requests (path : ByteArray) : RequestProgram ReadForm (SourcePaths.start path) := by
  unfold SourcePaths.start
  split
  · exact .pure _
  · split
    · apply request_bind (source_open_at_requests cwd "/".toUTF8 true (fun _ => .inl rfl))
      intro root
      exact .pure _
    · apply bind_requests (source_open_at_requests cwd ".".toUTF8 true (fun _ => .inr (.inl rfl)))
        (source_open_at_post _ _ _)
      intro base valid
      cases base with
      | error => exact .pure _
      | ok base =>
        apply RequestProgram.call (by intro impossible; cases impossible)
        intro spelling
        dsimp only [Filesystem.Program.bind]
        split
        · exact close_requests _ _
        · apply request_bind (check_ancestry_requests base valid)
          intro checked
          cases checked with
          | error => exact close_requests _ _
          | ok => exact .pure _

theorem open_requests (path : ByteArray) (directory : Bool) : RequestProgram ReadForm (SourcePaths.open path directory) := by
  unfold SourcePaths.open
  apply bind_requests (start_requests path) (start_post path)
  intro selected valid
  cases selected with
  | error => exact .pure _
  | ok selected => exact walk_requests selected.base selected.parts directory valid.1 valid.2

theorem open_post (path : ByteArray) (directory : Bool) :
    PostProgram (Successful DescriptorFits) (SourcePaths.open path directory) := by
  unfold SourcePaths.open
  apply post_bind (start_post path)
  intro selected valid
  cases selected with
  | error => exact .pure True.intro
  | ok selected => exact walk_post selected.base selected.parts directory valid.1

private theorem copy_profile_requests {α : Type} {program : Filesystem.Program α}
    (profile : RequestProfile Kernel.Lowered.CopyOperation program) : RequestProgram ReadForm program := by
  induction profile with
  | pure => exact .pure _
  | call request next permitted rest ih =>
    apply RequestProgram.call _ ih
    intro opening
    rcases permitted with reading | stat
    · rw [reading] at opening; cases opening
    · rw [stat] at opening; cases opening

theorem copy_opened_requests (fd : UInt64) (limit : Nat) : RequestProgram ReadForm (copyOpened fd limit) :=
  copy_profile_requests (Kernel.Lowered.copy_profile fd limit)

theorem copy_file_requests (path : ByteArray) (limit : Nat) :
    RequestProgram ReadForm (SourcePaths.copyFile path limit) := by
  unfold SourcePaths.copyFile
  apply request_bind (open_requests path false)
  intro opened
  cases opened with
  | error => exact .pure _
  | ok fd => exact request_bind (copy_opened_requests fd limit) (close_requests fd)

theorem hash_requests (bytes : ByteArray) : RequestProgram ReadForm (Filesystem.hash bytes) := by
  apply RequestProgram.call (by intro impossible; cases impossible)
  intro reply
  split <;> exact .pure _

end LeanCage.Host.SourceReadForms
