import FilesystemVirtualMachineBorrowing.Effects

namespace LeanCage.Host.VirtualMachine
open Filesystem Kernel

private theorem after_send_borrow {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle)
    (fuel : Nat) {configuration : IO.Process.StdioConfig} (child : IO.Process.Child configuration)
    (path : ByteArray) (boot diagnostic : UInt64) (began duration now : Nat)
    (state : State) (fresh : ConnectionFresh held state)
    (next : ∀ state, ConnectionFresh held state → ActorBorrowPost runtime actor held handle
      (ConnectionFresh held) (loop fuel child path boot diagnostic began duration state)) :
    ActorBorrowPost runtime actor held handle (ConnectionFresh held)
      (loopAfterSend fuel child path boot diagnostic began duration now state) := by
  unfold loopAfterSend
  split
  · exact .pure fresh
  · split
    · exact .pure fresh
    · apply actor_borrow_bind (poll_borrow laws actor held handle _ _)
      intro ready _
      cases ready with
      | error error => exact .pure fresh
      | ok ready =>
        apply actor_borrow_bind (consume_ready_borrow laws actor held handle _ ready _ _ _ state fresh)
        intro changed changedFresh
        split
        · exact .pure changedFresh
        · exact next changed changedFresh

private theorem after_connection_borrow {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle)
    (fuel : Nat) {configuration : IO.Process.StdioConfig} (child : IO.Process.Child configuration)
    (path : ByteArray) (boot diagnostic : UInt64) (began duration now : Nat)
    (state : State) (fresh : ConnectionFresh held state)
    (next : ∀ state, ConnectionFresh held state → ActorBorrowPost runtime actor held handle
      (ConnectionFresh held) (loop fuel child path boot diagnostic began duration state)) :
    ActorBorrowPost runtime actor held handle (ConnectionFresh held)
      (loopAfterConnection fuel child path boot diagnostic began duration now state) := by
  unfold loopAfterConnection
  split
  · exact .pure fresh
  · split
    · exact .pure fresh
    · split
      · split
        · apply actor_borrow_bind (first := ConnectionFresh held) (.pure fresh)
          intro changed changedFresh
          exact after_send_borrow laws actor held handle _ child _ _ _ _ _ _ _ changedFresh next
        · apply actor_borrow_bind (perform_passive_borrow laws actor held handle _ (by simp [RetainsDescriptors]))
          intro sent _
          split
          · apply actor_borrow_bind (first := ConnectionFresh held) (.pure fresh)
            intro changed changedFresh
            exact after_send_borrow laws actor held handle _ child _ _ _ _ _ _ _ changedFresh next
          · apply actor_borrow_bind (first := ConnectionFresh held) (.pure fresh)
            intro changed changedFresh
            exact after_send_borrow laws actor held handle _ child _ _ _ _ _ _ _ changedFresh next
      · apply actor_borrow_bind (first := ConnectionFresh held) (.pure fresh)
        intro changed changedFresh
        exact after_send_borrow laws actor held handle _ child _ _ _ _ _ _ _ changedFresh next

private theorem after_wait_borrow {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle)
    (fuel : Nat) {configuration : IO.Process.StdioConfig} (child : IO.Process.Child configuration)
    (path : ByteArray) (boot diagnostic : UInt64) (began duration : Nat)
    (state : State) (fresh : ConnectionFresh held state)
    (next : ∀ state, ConnectionFresh held state → ActorBorrowPost runtime actor held handle
      (ConnectionFresh held) (loop fuel child path boot diagnostic began duration state)) :
    ActorBorrowPost runtime actor held handle (ConnectionFresh held)
      (loopAfterWait fuel child path boot diagnostic began duration state) := by
  unfold loopAfterWait
  split
  · exact .pure fresh
  · apply actor_borrow_bind (clock_borrow laws actor held handle)
    intro clock _
    cases clock with
    | error error => exact .pure fresh
    | ok now =>
      change ActorBorrowPost runtime actor held handle (ConnectionFresh held)
        (match deadlineError state began duration now with
         | some error => pure (state.fail error)
         | _ => _)
      split
      · exact .pure fresh
      · change ActorBorrowPost runtime actor held handle (ConnectionFresh held)
          (if state.connection.isNone then _ else _)
        split
        · apply actor_borrow_bind (connect_borrow laws actor held handle path)
          intro connected permitted
          cases connected with
          | error error =>
            apply actor_borrow_bind (first := ConnectionFresh held) (.pure fresh)
            intro changed changedFresh
            exact after_connection_borrow laws actor held handle _ child _ _ _ _ _ _ _ changedFresh next
          | ok connection =>
            have changedFresh : ConnectionFresh held ({state with connection} : State) := permitted
            apply actor_borrow_bind (first := ConnectionFresh held) (.pure changedFresh)
            intro changed changedFresh
            exact after_connection_borrow laws actor held handle _ child _ _ _ _ _ _ _ changedFresh next
        · apply actor_borrow_bind (first := ConnectionFresh held) (.pure fresh)
          intro changed changedFresh
          exact after_connection_borrow laws actor held handle _ child _ _ _ _ _ _ _ changedFresh next

-- §FS-host-boundary.ownership: The actual loop retains every live raw directory reference.
theorem loop_borrow {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : DescriptorContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (raw : handle.rawOwned = true)
    (fuel : Nat) {configuration : IO.Process.StdioConfig} (child : IO.Process.Child configuration)
    (path : ByteArray) (boot diagnostic : UInt64) (began duration : Nat)
    (state : State) (fresh : ConnectionFresh held state) :
    ActorBorrowPost runtime actor held handle (ConnectionFresh held)
      (loop fuel child path boot diagnostic began duration state) := by
  induction fuel generalizing state with
  | zero => exact .pure fresh
  | succ fuel ih =>
    rw [loop_borrow_source]
    apply actor_borrow_bind (runtime_effect_borrow sdk actor held handle (.tryWait child) True.intro raw)
    intro observed _
    have observedFresh : ConnectionFresh held (afterWait state observed) := by
      cases observed with
      | error error => exact fresh
      | ok status => cases status <;> exact fresh
    exact after_wait_borrow laws actor held handle _ child _ _ _ _ _ _ observedFresh ih

end LeanCage.Host.VirtualMachine
