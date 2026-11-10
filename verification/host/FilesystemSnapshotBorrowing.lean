import FilesystemLoweredPaths

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: Op11 checks dirfd(cursor) equals request.second before
-- closedir. This single adapter operation cannot retire any different descriptor.
structure DirectoryRetirementContract (kernel : Contract) : Prop where
  other : ∀ before after request observed held,
    kernel.step before request observed after → request.op = .dirClose → held ≠ request.second →
    after.handles held = before.handles held

namespace Lowered

theorem snapshot_close_directory_borrow {kernel : Contract}
    (directories : DirectoryRetirementContract kernel) (held : UInt64) (handle : Handle)
    {α : Type} (fd cursor : UInt64) (result : Result α) (different : fd ≠ held) :
    BorrowPost kernel held handle (fun _ => True) (Snapshot.closeDirectory fd cursor result).lower := by
  apply BorrowPost.call
  · intro before after observed actual live
    rw [directories.other _ _ _ _ _ actual rfl (Ne.symm different)]
    exact live
  · intro before after reply actual live
    cases result with
    | error => exact .pure True.intro
    | ok value =>
      change BorrowPost kernel held handle (fun _ => True)
        (if reply.1 == 0 && reply.2.isEmpty then Filesystem.Program.pure (.ok value : Result α)
          else Filesystem.Program.pure (.error (failure "closedir" reply))).lower
      split <;> exact .pure True.intro

theorem snapshot_enumerate_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (fuel : Nat) (cursor : UInt64) (remaining : Nat)
    (seen names : List String) :
    BorrowPost kernel held handle (fun _ => True) (Snapshot.enumerate fuel cursor remaining seen names).lower := by
  induction fuel generalizing seen names with
  | zero => exact .pure True.intro
  | succ fuel ih =>
    unfold Snapshot.enumerate
    apply passive_call laws held handle (by simp [RetainsDescriptors])
    intro reply
    repeat' first | exact .pure True.intro | exact ih _ _ | split

-- §FS-host-boundary.snapshot: Fresh opens and the checked expected-FD close preserve
-- inherited raw references at every nested scan, error and lost-operation boundary.
private theorem snapshot_walk_borrow_pair {kernel : Contract} (laws : DescriptorContract kernel)
    (directories : DirectoryRetirementContract kernel) (held : UInt64) (handle : Handle) (fuel : Nat) :
    (∀ limits fd name state, fd ≠ held →
      BorrowPost kernel held handle (fun _ => True) (Snapshot.walk fuel limits fd name state).lower) ∧
    (∀ limits fd name names state,
      BorrowPost kernel held handle (fun _ => True) (Snapshot.walkChildren fuel limits fd name names state).lower) := by
  induction fuel with
  | zero =>
    constructor
    · intro limits fd name state different
      change BorrowPost kernel held handle (fun _ => True)
        (closeResult fd (.error "snapshot traversal made no bounded progress" : Result Snapshot.State)).lower
      apply borrow_weaken (close_borrow laws fd held handle _ (Ne.symm different))
      intro _ _; trivial
    · intro limits fd name names state
      cases names <;> exact .pure True.intro
  | succ fuel ih =>
    constructor
    · intro limits fd name state different
      unfold Snapshot.walk
      apply passive_call laws held handle (by simp [RetainsDescriptors])
      intro initialReply
      split
      · apply borrow_weaken (close_borrow laws fd held handle _ (Ne.symm different))
        intro _ _; trivial
      · split
        · apply borrow_weaken (close_borrow laws fd held handle _ (Ne.symm different))
          intro _ _; trivial
        · apply passive_call laws held handle (by simp [RetainsDescriptors])
          intro opened
          split
          · apply borrow_weaken (close_borrow laws fd held handle _ (Ne.symm different))
            intro _ _; trivial
          · split
            · exact .pure True.intro
            · dsimp only
              split
              · exact .pure True.intro
              · apply borrow_bind (snapshot_enumerate_borrow laws held handle _ _ _ _ _)
                intro listing _
                cases listing with
                | error => exact snapshot_close_directory_borrow directories held handle _ _ _ different
                | ok names =>
                  apply borrow_bind (ih.2 _ _ _ _ _)
                  intro copied _
                  cases copied with
                  | error => exact snapshot_close_directory_borrow directories held handle _ _ _ different
                  | ok after =>
                    apply passive_call laws held handle (by simp [RetainsDescriptors])
                    intro finalReply
                    split
                    · exact snapshot_close_directory_borrow directories held handle _ _ _ different
                    · exact snapshot_close_directory_borrow directories held handle _ _ _ different
    · intro limits parent prefixName names state
      cases names with
      | nil => exact .pure True.intro
      | cons name rest =>
        unfold Snapshot.walkChildren
        split
        · exact .pure True.intro
        · split
          · exact .pure True.intro
          · split
            · exact .pure True.intro
            · dsimp only
              split
              · apply borrow_bind (sourceOpenAt_borrow laws held handle _ _ _)
                intro opened fresh
                cases opened with
                | error => exact .pure True.intro
                | ok child =>
                  apply passive_call laws held handle (by simp [RetainsDescriptors])
                  intro information
                  split
                  · apply borrow_weaken (close_borrow laws child held handle _ (Ne.symm fresh))
                    intro _ _; trivial
                  · split
                    · split
                      · apply borrow_weaken (close_borrow laws child held handle _ (Ne.symm fresh))
                        intro _ _; trivial
                      · apply borrow_bind (ih.1 _ _ _ _ fresh)
                        intro copied _
                        cases copied with
                        | error => exact .pure True.intro
                        | ok after => exact ih.2 _ _ _ _ _
                    · split
                      · apply borrow_bind (pre := fun _ => True)
                        · apply borrow_bind (copyOpened_borrow laws held handle _ _)
                          intro copied _
                          apply borrow_weaken (close_borrow laws child held handle copied (Ne.symm fresh))
                          intro _ _; trivial
                        · intro copied _
                          cases copied with
                          | error => exact .pure True.intro
                          | ok copied =>
                            apply borrow_bind (hash_borrow laws held handle _)
                            intro hashed _
                            cases hashed with
                            | error => exact .pure True.intro
                            | ok digest =>
                              repeat' first | exact .pure True.intro | exact ih.2 _ _ _ _ _ | split
                      · apply borrow_weaken (close_borrow laws child held handle _ (Ne.symm fresh))
                        intro _ _; trivial
              · exact .pure True.intro

theorem snapshot_workspace_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (directories : DirectoryRetirementContract kernel) (held : UInt64) (handle : Handle)
    (workspace : Option ByteArray) (limits : Snapshot.Limits) :
    BorrowPost kernel held handle (fun _ => True) (Snapshot.copyWorkspace workspace limits).lower := by
  cases workspace with
  | none => exact .pure True.intro
  | some path =>
    unfold Snapshot.copyWorkspace
    apply borrow_bind (sourceOpen_borrow laws held handle path true)
    intro opened fresh
    cases opened with
    | error => exact .pure True.intro
    | ok fd => exact (snapshot_walk_borrow_pair laws directories held handle _).1 _ _ _ _ fresh

theorem snapshot_stdin_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (stdin : Snapshot.Stdin) (limit : Nat) :
    BorrowPost kernel held handle (fun _ => True) (Snapshot.copyStdin stdin limit).lower := by
  cases stdin with
  | absent => exact .pure True.intro
  | bytes bytes =>
    change BorrowPost kernel held handle (fun _ => True)
      (if bytes.size ≤ limit then Filesystem.Program.pure (.ok (some bytes) : Result (Option ByteArray))
        else Filesystem.Program.pure (.error "stdin exceeds policy limit")).lower
    split <;> exact .pure True.intro
  | file path =>
    apply borrow_bind (sourceCopyFile_borrow laws held handle path limit)
    intro copied _
    exact .pure True.intro

theorem snapshot_identify_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) (bytes : Option ByteArray) :
    BorrowPost kernel held handle (fun _ => True) (Snapshot.identify bytes).lower := by
  cases bytes with
  | none => exact .pure True.intro
  | some bytes =>
    apply borrow_bind (hash_borrow laws held handle bytes)
    intro hashed _
    exact .pure True.intro

theorem snapshot_freeze_borrow {kernel : Contract} (laws : DescriptorContract kernel)
    (directories : DirectoryRetirementContract kernel) (held : UInt64) (handle : Handle)
    (workspace : Option ByteArray) (stdin : Snapshot.Stdin) (limits : Snapshot.Limits) :
    BorrowPost kernel held handle (fun _ => True) (Snapshot.freeze workspace stdin limits).lower := by
  unfold Snapshot.freeze
  split
  · exact .pure True.intro
  · apply borrow_bind (snapshot_workspace_borrow laws directories held handle _ _)
    intro copied _
    cases copied with
    | error => exact .pure True.intro
    | ok state =>
      apply borrow_bind (snapshot_stdin_borrow laws held handle _ _)
      intro input _
      cases input with
      | error => exact .pure True.intro
      | ok input =>
        apply borrow_bind (snapshot_identify_borrow laws held handle _)
        intro treeHash _
        cases treeHash with
        | error => exact .pure True.intro
        | ok treeDigest =>
          apply borrow_bind (snapshot_identify_borrow laws held handle _)
          intro inputHash _
          cases inputHash with
          | error => exact .pure True.intro
          | ok stdinDigest => exact .pure True.intro

end Lowered
end LeanCage.Host.Kernel
