import FilesystemChannelWrites
import FilesystemVirtualMachineBorrowing.Effects

namespace LeanCage.Host.Kernel
open Filesystem

theorem channel_perform {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle) (request : Request)
    (passive : RetainsDescriptors request.op) (avoid : request.op = .write → request.first ≠ held)
    (raw : PrimitiveFilesystem.lowerEffect (.filesystem request) = Program.effect (.filesystem request)) :
    ChannelWritePost runtime actor held handle (fun _ => True) (Runtime.perform request) := by
  apply ChannelWritePost.call (effect := .filesystem request) avoid raw
  · intro before after observed actual live
    rw [laws.retained _ _ _ _ actual passive]
    exact live
  · intro before after reply actual live
    exact .pure True.intro

theorem channel_allocate {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle) (request : Request)
    (allocating : AllocatesDescriptor request.op)
    (raw : PrimitiveFilesystem.lowerEffect (.filesystem request) = Program.effect (.filesystem request)) :
    ChannelWritePost runtime actor held handle (fun reply => ∀ fd, descriptor reply = some fd → fd ≠ held)
      (Runtime.perform request) := by
  apply ChannelWritePost.call (effect := .filesystem request)
  · intro writing
    rcases allocating with opening | socket | executable
    · rw [opening] at writing; cases writing
    · rw [socket] at writing; cases writing
    · rw [executable] at writing; cases writing
  · exact raw
  · intro before after observed actual live
    exact laws.allocate_existing _ _ _ _ _ _ actual allocating live
  · intro before after reply actual live
    apply ChannelWritePost.pure
    intro fd recognized same
    have absent := (laws.allocated_fresh _ _ _ _ _ actual allocating recognized).1
    subst fd
    rw [live] at absent
    cases absent

theorem channel_close {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle)
    (fd : UInt64) (different : fd ≠ held) :
    ChannelWritePost runtime actor held handle (fun _ => True) (VirtualMachine.close fd) := by
  apply ChannelWritePost.call (effect := .filesystem {op := .close, first := fd})
  · intro wrong; cases wrong
  · rfl
  · intro before after observed actual live
    rw [laws.close_other _ _ _ _ _ actual rfl (Ne.symm different)]
    exact live
  · intro before after reply actual live
    exact .pure True.intro

theorem channel_clock {kernel : Contract} {sourceProgram : Program UInt32} {runtime : ActorRuntime kernel sourceProgram}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle) :
    ChannelWritePost runtime actor held handle (fun _ => True) Runtime.clock := by
  unfold Runtime.clock
  apply channel_bind (channel_perform laws actor held handle _ (by simp [RetainsDescriptors]) (by intro wrong; cases wrong) rfl)
  intro reply _
  split
  · exact .pure True.intro
  · dsimp only; split <;> exact .pure True.intro

theorem channel_poll {kernel : Contract} {sourceProgram : Program UInt32} {runtime : ActorRuntime kernel sourceProgram}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle)
    (descriptors : List (UInt64 × Nat)) (milliseconds : Nat) :
    ChannelWritePost runtime actor held handle (fun _ => True) (Runtime.poll descriptors milliseconds) := by
  unfold Runtime.poll
  split
  · exact .pure True.intro
  · apply channel_bind (channel_perform laws actor held handle _ (by simp [RetainsDescriptors]) (by intro wrong; cases wrong) rfl)
    intro reply _
    repeat' first | exact .pure True.intro | split

theorem channel_read {kernel : Contract} {sourceProgram : Program UInt32} {runtime : ActorRuntime kernel sourceProgram}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle) (fd : UInt64) (amount : Nat) :
    ChannelWritePost runtime actor held handle (fun _ => True) (Runtime.read fd amount) := by
  unfold Runtime.read
  split
  · exact .pure True.intro
  · apply channel_bind (channel_perform laws actor held handle _ (by simp [RetainsDescriptors]) (by intro wrong; cases wrong) rfl)
    intro reply _
    repeat' first | exact .pure True.intro | split

end LeanCage.Host.Kernel

namespace LeanCage.Host.VirtualMachine
open Filesystem
open Kernel

private theorem fail_fresh {held : UInt64} {state : State} (fresh : ConnectionFresh held state) (message : String) :
    ConnectionFresh held (state.fail message) := fresh

theorem channel_connect {kernel : Contract} {sourceProgram : Program UInt32} {runtime : ActorRuntime kernel sourceProgram}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle) (path : ByteArray) :
    ChannelWritePost runtime actor held handle (Successful (FreshConnection held)) (connect path) := by
  unfold connect
  split
  · exact .pure True.intro
  · apply channel_bind (channel_allocate laws actor held handle _ (.inr (.inl rfl)) rfl)
    intro created fresh
    split
    · rename_i fd recognized
      apply channel_bind (channel_perform laws actor held handle _ (by simp [RetainsDescriptors]) (by intro wrong; cases wrong) rfl)
      intro connected _
      split
      · apply ChannelWritePost.pure
        intro query same
        have sameFd := Option.some.inj same
        subst query
        exact fresh fd recognized
      · apply channel_bind (channel_close laws actor held handle fd (fresh fd recognized))
        intro ignored _
        split
        · exact .pure (by intro query same; cases same)
        · exact .pure True.intro
    · exact .pure True.intro

theorem channel_consume {kernel : Contract} {sourceProgram : Program UInt32} {runtime : ActorRuntime kernel sourceProgram}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle)
    (fd boot diagnostic : UInt64) (now : Nat) (state : State) (fresh : ConnectionFresh held state) :
    ChannelWritePost runtime actor held handle (ConnectionFresh held) (consume fd boot diagnostic now state) := by
  unfold consume
  apply channel_bind (channel_read laws actor held handle _ _)
  intro read _
  cases read with
  | error error => exact .pure (fail_fresh fresh _)
  | ok result =>
    cases result with
    | pending => exact .pure fresh
    | eof => repeat' first | exact .pure fresh | (dsimp only; split) | split
    | data part =>
      repeat' first | exact .pure fresh | exact .pure (fail_fresh fresh _) | (dsimp only; split) | split

theorem channel_consume_ready {kernel : Contract} {sourceProgram : Program UInt32} {runtime : ActorRuntime kernel sourceProgram}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle)
    (descriptors : List (UInt64 × Nat)) (ready : List Nat) (boot diagnostic : UInt64) (now : Nat)
    (state : State) (fresh : ConnectionFresh held state) :
    ChannelWritePost runtime actor held handle (ConnectionFresh held)
      (consumeReady descriptors ready boot diagnostic now state) := by
  induction descriptors generalizing ready state with
  | nil => cases ready <;> exact .pure fresh
  | cons descriptor rest ih =>
    cases ready with
    | nil => exact .pure fresh
    | cons outcome ready =>
      unfold consumeReady
      split
      · apply channel_bind (first := ConnectionFresh held) (.pure fresh)
        intro next nextFresh
        dsimp only
        split
        · exact .pure nextFresh
        · exact ih ready next nextFresh
      · apply channel_bind (channel_consume laws actor held handle _ _ _ _ _ fresh)
        intro next nextFresh
        dsimp only
        split
        · exact .pure nextFresh
        · exact ih ready next nextFresh


end LeanCage.Host.VirtualMachine
