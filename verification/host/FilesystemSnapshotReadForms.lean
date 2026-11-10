import FilesystemSourceReadForms

namespace LeanCage.Host.SourceReadForms
open Filesystem Snapshot

theorem valid_component_form (name : String) (valid : ValidComponent name) :
    Directories.component name.toUTF8 = true := by
  have nonempty : name.toUTF8.size ≠ 0 := Nat.ne_of_gt valid.1
  rcases valid with ⟨positive, bounded, notDot, notUp, noNul, noSlash⟩
  simp_all [Directories.component, ByteArray.isEmpty]

private theorem close_directory_requests {α : Type} (fd cursor : UInt64) (result : Result α) :
    RequestProgram ReadForm (closeDirectory fd cursor result) := by
  apply RequestProgram.call (by intro impossible; cases impossible)
  intro reply
  cases result with
  | error => exact .pure _
  | ok => dsimp only; split <;> exact .pure _

private theorem enumerate_requests (fuel : Nat) (cursor : UInt64) (remaining : Nat) (seen names : List String) :
    RequestProgram ReadForm (enumerate fuel cursor remaining seen names) := by
  induction fuel generalizing seen names with
  | zero => exact .pure _
  | succ fuel ih =>
    unfold enumerate
    apply RequestProgram.call (by intro impossible; cases impossible)
    intro reply
    repeat' first | exact .pure _ | exact ih _ _ | split

-- §FS-host-boundary.snapshot: The recursive source checks every readdir name before
-- opening it, preserves the original parent number, and propagates recognized child FDs.
private theorem walk_requests_pair (fuel : Nat) :
    (∀ limits fd name state, DescriptorFits fd → RequestProgram ReadForm (walk fuel limits fd name state)) ∧
    (∀ limits fd name names state, DescriptorFits fd →
      RequestProgram ReadForm (walkChildren fuel limits fd name names state)) := by
  induction fuel with
  | zero =>
    constructor
    · intro limits fd name state fits
      simpa only [walk] using close_requests fd
        (.error "snapshot traversal made no bounded progress" : Result State)
    · intro limits fd name names state fits
      cases names with
      | nil => exact .pure _
      | cons => exact .pure _
  | succ fuel ih =>
    constructor
    · intro limits fd name state fits
      unfold walk
      apply RequestProgram.call (by intro impossible; cases impossible)
      intro initialReply
      split
      · exact close_requests _ _
      · split
        · exact close_requests _ _
        · apply RequestProgram.call (by intro impossible; cases impossible)
          intro opened
          split
          · exact close_requests _ _
          · split
            · exact .pure _
            · dsimp only
              split
              · exact .pure _
              · apply request_bind (enumerate_requests _ _ _ _ _)
                intro listing
                cases listing with
                | error => exact close_directory_requests _ _ _
                | ok names =>
                  apply request_bind (ih.2 _ _ _ _ _ fits)
                  intro copied
                  cases copied with
                  | error => exact close_directory_requests _ _ _
                  | ok after =>
                    apply RequestProgram.call (by intro impossible; cases impossible)
                    intro finalReply
                    split
                    · exact close_directory_requests _ _ _
                    · exact close_directory_requests _ _ _
    · intro limits parent prefixName names state fits
      cases names with
      | nil => exact .pure _
      | cons name rest =>
        unfold walkChildren
        split
        · exact .pure _
        · rename_i publicName
          have publicName : PrivateNames.reservedBytes name.toUTF8 = false := by simpa using publicName
          split
          · exact .pure _
          · rename_i component
            have component : ValidComponent name := by simpa using component
            split
            · exact .pure _
            · dsimp only
              split
              · apply bind_requests (source_open_at_requests parent name.toUTF8 false (by
                  intro opening
                  exact .inr (.inr ⟨fits, .inr rfl, valid_component_form name component, publicName⟩)))
                  (source_open_at_post _ _ _)
                intro opened valid
                cases opened with
                | error => exact .pure _
                | ok child =>
                  apply RequestProgram.call (by intro impossible; cases impossible)
                  intro information
                  split
                  · exact close_requests _ _
                  · split
                    · split
                      · exact close_requests _ _
                      · apply request_bind (ih.1 _ _ _ _ valid)
                        intro result
                        cases result with
                        | error => exact .pure _
                        | ok after => exact ih.2 _ _ _ _ _ fits
                    · split
                      · apply request_bind (request_bind (copy_opened_requests _ _) (close_requests _))
                        intro result
                        cases result with
                        | error => exact .pure _
                        | ok copied =>
                          apply request_bind (hash_requests _)
                          intro hashed
                          cases hashed with
                          | error => exact .pure _
                          | ok digest =>
                            split
                            · exact .pure _
                            · split
                              · exact .pure _
                              · split
                                · exact .pure _
                                · exact ih.2 _ _ _ _ _ fits
                      · exact close_requests _ _
              · exact .pure _

theorem workspace_requests (workspace : Option ByteArray) (limits : Limits) :
    RequestProgram ReadForm (copyWorkspace workspace limits) := by
  cases workspace with
  | none => exact .pure _
  | some path =>
    unfold copyWorkspace
    apply bind_requests (open_requests path true) (open_post path true)
    intro opened valid
    cases opened with
    | error => exact .pure _
    | ok fd => exact (walk_requests_pair _).1 _ _ _ _ valid

theorem stdin_requests (stdin : Stdin) (limit : Nat) : RequestProgram ReadForm (copyStdin stdin limit) := by
  cases stdin with
  | absent => exact .pure _
  | bytes bytes => dsimp only [copyStdin]; split <;> exact .pure _
  | file path => exact request_bind (copy_file_requests path limit) (fun _ => .pure _)

private theorem identify_requests (input : Option ByteArray) : RequestProgram ReadForm (identify input) := by
  cases input with
  | none => exact .pure _
  | some bytes => exact request_bind (hash_requests bytes) (fun _ => .pure _)

-- §FS-host-boundary.snapshot: The real freeze producer supplies all read-open
-- arguments for workspace and file stdin; raw bytes and absent inputs cause no opens.
theorem freeze_requests (workspace : Option ByteArray) (stdin : Stdin) (limits : Limits) :
    RequestProgram ReadForm (freeze workspace stdin limits) := by
  unfold freeze
  split
  · exact .pure _
  · apply request_bind (workspace_requests _ _)
    intro copied
    cases copied with
    | error => exact .pure _
    | ok state =>
      apply request_bind (stdin_requests _ _)
      intro input
      cases input with
      | error => exact .pure _
      | ok input =>
        apply request_bind (identify_requests _)
        intro treeHash
        cases treeHash with
        | error => exact .pure _
        | ok treeDigest =>
          apply request_bind (identify_requests _)
          intro inputHash
          cases inputHash <;> exact .pure _

end LeanCage.Host.SourceReadForms
