import SnapshotProofs.State

namespace LeanCage.Host.Snapshot

open Filesystem

def Successful {α : Type} (property : α → Prop) : Result α → Prop
  | .ok value => property value
  | .error _ => True

theorem closeResult_post {α : Type} (property : α → Prop) (fd : UInt64) (result : Result α)
    (valid : Successful property result) : PostProgram (Successful property) (closeResult fd result) := by
  apply PostProgram.call
  intro reply
  cases result with
  | error => exact .pure True.intro
  | ok value =>
    dsimp only
    split
    · exact .pure valid
    · exact .pure True.intro

theorem closeDirectory_post {α : Type} (property : α → Prop) (cursor : UInt64) (result : Result α)
    (valid : Successful property result) : PostProgram (Successful property) (closeDirectory cursor result) := by
  apply PostProgram.call
  intro reply
  cases result with
  | error => exact .pure True.intro
  | ok value =>
    dsimp only
    split
    · exact .pure valid
    · exact .pure True.intro

theorem closeDirectory_value {α : Type} (cursor : UInt64) (input : Result α)
    {events : List (Request × Reply)} {value : α}
    (run : Returns (closeDirectory cursor input) events (.ok value)) : input = .ok value := by
  apply post_returns (post := Successful (fun value => input = .ok value))
    (closeDirectory_post _ _ input (by cases input <;> trivial)) run

theorem state_blobs (limits : Limits) (state : State) (blobs : List Blob)
    (valid : StateValid limits state) : StateValid limits { state with blobs := blobs } :=
  ⟨valid.count_exact, valid.bytes_exact, valid.tree_exact, valid.inodes_bound,
    valid.bytes_bound, valid.tree_bound, valid.unique⟩

-- §FS-host-boundary.snapshot: Complete successful paths retain exact format and policy aggregates.
private theorem walk_state_pair (fuel : Nat) :
    (∀ limits fd name state, StateValid limits state →
      PostProgram (Successful (StateValid limits)) (walk fuel limits fd name state)) ∧
    (∀ limits fd name names state, StateValid limits state →
      PostProgram (Successful (StateValid limits)) (walkChildren fuel limits fd name names state)) := by
  induction fuel with
  | zero =>
    constructor
    · intro limits fd name state valid
      simpa only [walk] using closeResult_post (StateValid limits) fd
        (.error "snapshot traversal made no bounded progress") True.intro
    · intro limits fd name names state valid
      cases names with
      | nil => exact .pure valid
      | cons => exact .pure True.intro
  | succ fuel ih =>
    constructor
    · intro limits fd name state valid
      unfold walk
      apply PostProgram.call
      intro initialReply
      split
      · exact closeResult_post _ _ _ True.intro
      · split
        · exact closeResult_post _ _ _ True.intro
        · apply PostProgram.call
          intro opened
          split
          · exact closeResult_post _ _ _ True.intro
          · split
            · exact .pure True.intro
            · dsimp only
              split
              · exact .pure True.intro
              · apply post_bind (post_true _)
                intro listing _
                cases listing with
                | error => exact closeDirectory_post _ _ _ True.intro
                | ok names =>
                  apply post_bind (ih.2 _ _ _ _ _ valid)
                  intro result verified
                  cases result with
                  | error => exact closeDirectory_post _ _ _ True.intro
                  | ok after =>
                    apply PostProgram.call
                    intro finalReply
                    split
                    · exact closeDirectory_post _ _ _ True.intro
                    · apply closeDirectory_post
                      split
                      · exact verified
                      · trivial
    · intro limits fd name names state valid
      cases names with
      | nil => exact .pure valid
      | cons child rest =>
        unfold walkChildren
        split
        · exact .pure True.intro
        · split
          · exact .pure True.intro
          · split
            · exact .pure True.intro
            · dsimp only
              split
              · apply post_bind (post_true _)
                intro opened _
                cases opened with
                | error => exact .pure True.intro
                | ok child =>
                  apply PostProgram.call
                  intro information
                  split
                  · exact closeResult_post _ _ _ True.intro
                  · split
                    · split
                      · exact closeResult_post _ _ _ True.intro
                      · rename_i next appended
                        apply post_bind (ih.1 _ _ _ _ (appendEntry_preserves _ _ _ valid appended))
                        intro result verified
                        cases result with
                        | error => exact .pure True.intro
                        | ok after => exact ih.2 _ _ _ _ _ verified
                    · split
                      · apply post_bind (post_true _)
                        intro result _
                        cases result with
                        | error => exact .pure True.intro
                        | ok copied =>
                          apply post_bind (post_true _)
                          intro hashed _
                          cases hashed with
                          | error => exact .pure True.intro
                          | ok digest =>
                            split
                            · exact .pure True.intro
                            · split
                              · exact .pure True.intro
                              · split
                                · exact .pure True.intro
                                · rename_i after appended
                                  exact ih.2 _ _ _ _ _
                                    (appendEntry_preserves _ _ _ (state_blobs _ _ _ valid) appended)
                      · exact closeResult_post _ _ _ True.intro
              · exact .pure True.intro

theorem walk_state_valid (fuel : Nat) (limits : Limits) (fd : UInt64) (name : String) (state : State)
    (valid : StateValid limits state) {events : List (Request × Reply)} {after : State}
    (run : Returns (walk fuel limits fd name state) events (.ok after)) : StateValid limits after :=
  post_returns (post := Successful (StateValid limits)) ((walk_state_pair fuel).1 _ _ _ _ valid) run

theorem walkChildren_state_valid (fuel : Nat) (limits : Limits) (fd : UInt64) (name : String)
    (names : List String) (state : State) (valid : StateValid limits state)
    {events : List (Request × Reply)} {after : State}
    (run : Returns (walkChildren fuel limits fd name names state) events (.ok after)) : StateValid limits after :=
  post_returns (post := Successful (StateValid limits)) ((walk_state_pair fuel).2 _ _ _ _ _ valid) run

theorem copyWorkspace_state_valid (workspace : Option ByteArray) (limits : Limits)
    (minimum : 2 ≤ limits.workspaceInodes) :
    PostProgram (Successful (StateValid limits)) (copyWorkspace workspace limits) := by
  cases workspace with
  | none => exact .pure (initial_state_valid _ minimum)
  | some path =>
    simp only [copyWorkspace]
    apply post_bind (post_true _)
    intro opened _
    cases opened with
    | error => exact .pure True.intro
    | ok fd => exact (walk_state_pair _).1 _ _ _ _ (initial_state_valid _ minimum)

end LeanCage.Host.Snapshot
