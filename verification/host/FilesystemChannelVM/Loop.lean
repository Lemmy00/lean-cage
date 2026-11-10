import FilesystemChannelVM.Effects

namespace LeanCage.Host.VirtualMachine
open Filesystem Kernel

private theorem channel_after_send {kernel : Contract} {sourceProgram : Program UInt32} {runtime : ActorRuntime kernel sourceProgram}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle)
    (fuel : Nat) {configuration : IO.Process.StdioConfig} (child : IO.Process.Child configuration)
    (path : ByteArray) (boot diagnostic : UInt64) (began duration now : Nat)
    (state : State) (fresh : ConnectionFresh held state)
    (next : ∀ state, ConnectionFresh held state → ChannelWritePost runtime actor held handle
      (ConnectionFresh held) (loop fuel child path boot diagnostic began duration state)) :
    ChannelWritePost runtime actor held handle (ConnectionFresh held)
      (loopAfterSend fuel child path boot diagnostic began duration now state) := by
  unfold loopAfterSend
  split
  · exact .pure fresh
  · split
    · exact .pure fresh
    · apply channel_bind (channel_poll laws actor held handle _ _)
      intro ready _
      cases ready with
      | error error => exact .pure fresh
      | ok ready =>
        apply channel_bind (channel_consume_ready laws actor held handle _ ready _ _ _ state fresh)
        intro changed changedFresh
        split
        · exact .pure changedFresh
        · exact next changed changedFresh

private theorem channel_after_connection {kernel : Contract} {sourceProgram : Program UInt32} {runtime : ActorRuntime kernel sourceProgram}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle)
    (fuel : Nat) {configuration : IO.Process.StdioConfig} (child : IO.Process.Child configuration)
    (path : ByteArray) (boot diagnostic : UInt64) (began duration now : Nat)
    (state : State) (fresh : ConnectionFresh held state)
    (next : ∀ state, ConnectionFresh held state → ChannelWritePost runtime actor held handle
      (ConnectionFresh held) (loop fuel child path boot diagnostic began duration state)) :
    ChannelWritePost runtime actor held handle (ConnectionFresh held)
      (loopAfterConnection fuel child path boot diagnostic began duration now state) := by
  unfold loopAfterConnection
  split
  · exact .pure fresh
  · split
    · exact .pure fresh
    · split
      · split
        · apply channel_bind (first := ConnectionFresh held) (.pure fresh)
          intro changed changedFresh
          exact channel_after_send laws actor held handle _ child _ _ _ _ _ _ _ changedFresh next
        · apply channel_bind (channel_perform laws actor held handle _ (by simp [RetainsDescriptors]) (by intro _; exact fresh _ (by assumption)) rfl)
          intro sent _
          split
          · apply channel_bind (first := ConnectionFresh held) (.pure fresh)
            intro changed changedFresh
            exact channel_after_send laws actor held handle _ child _ _ _ _ _ _ _ changedFresh next
          · apply channel_bind (first := ConnectionFresh held) (.pure fresh)
            intro changed changedFresh
            exact channel_after_send laws actor held handle _ child _ _ _ _ _ _ _ changedFresh next
      · apply channel_bind (first := ConnectionFresh held) (.pure fresh)
        intro changed changedFresh
        exact channel_after_send laws actor held handle _ child _ _ _ _ _ _ _ changedFresh next

private theorem channel_after_wait {kernel : Contract} {sourceProgram : Program UInt32} {runtime : ActorRuntime kernel sourceProgram}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle)
    (fuel : Nat) {configuration : IO.Process.StdioConfig} (child : IO.Process.Child configuration)
    (path : ByteArray) (boot diagnostic : UInt64) (began duration : Nat)
    (state : State) (fresh : ConnectionFresh held state)
    (next : ∀ state, ConnectionFresh held state → ChannelWritePost runtime actor held handle
      (ConnectionFresh held) (loop fuel child path boot diagnostic began duration state)) :
    ChannelWritePost runtime actor held handle (ConnectionFresh held)
      (loopAfterWait fuel child path boot diagnostic began duration state) := by
  unfold loopAfterWait
  split
  · exact .pure fresh
  · apply channel_bind (channel_clock laws actor held handle)
    intro clock _
    cases clock with
    | error error => exact .pure fresh
    | ok now =>
      change ChannelWritePost runtime actor held handle (ConnectionFresh held)
        (match deadlineError state began duration now with
         | some error => pure (state.fail error)
         | _ => _)
      split
      · exact .pure fresh
      · change ChannelWritePost runtime actor held handle (ConnectionFresh held)
          (if state.connection.isNone then _ else _)
        split
        · apply channel_bind (channel_connect laws actor held handle path)
          intro connected permitted
          cases connected with
          | error error =>
            apply channel_bind (first := ConnectionFresh held) (.pure fresh)
            intro changed changedFresh
            exact channel_after_connection laws actor held handle _ child _ _ _ _ _ _ _ changedFresh next
          | ok connection =>
            have changedFresh : ConnectionFresh held ({state with connection} : State) := permitted
            apply channel_bind (first := ConnectionFresh held) (.pure changedFresh)
            intro changed changedFresh
            exact channel_after_connection laws actor held handle _ child _ _ _ _ _ _ _ changedFresh next
        · apply channel_bind (first := ConnectionFresh held) (.pure fresh)
          intro changed changedFresh
          exact channel_after_connection laws actor held handle _ child _ _ _ _ _ _ _ changedFresh next

-- §FS-host-boundary.caller: The actual loop preserves the live response channel
-- and never writes to it.
theorem channel_loop {kernel : Contract} {sourceProgram : Program UInt32} {runtime : ActorRuntime kernel sourceProgram}
    (laws : DescriptorContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) (raw : handle.rawOwned = true)
    (fuel : Nat) {configuration : IO.Process.StdioConfig} (child : IO.Process.Child configuration)
    (path : ByteArray) (boot diagnostic : UInt64) (began duration : Nat)
    (state : State) (fresh : ConnectionFresh held state) :
    ChannelWritePost runtime actor held handle (ConnectionFresh held)
      (loop fuel child path boot diagnostic began duration state) := by
  induction fuel generalizing state with
  | zero => exact .pure fresh
  | succ fuel ih =>
    rw [loop_borrow_source]
    apply channel_bind (channel_runtime sdk actor held handle (.tryWait child) True.intro raw)
    intro observed _
    have observedFresh : ConnectionFresh held (afterWait state observed) := by
      cases observed with
      | error error => exact fresh
      | ok status => cases status <;> exact fresh
    exact channel_after_wait laws actor held handle _ child _ _ _ _ _ _ observedFresh ih

end LeanCage.Host.VirtualMachine
