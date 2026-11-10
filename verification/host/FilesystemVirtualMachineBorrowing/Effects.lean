import FilesystemVirtualMachineBorrowing.Source

namespace LeanCage.Host.Kernel
open Filesystem

theorem actor_borrow_weaken {kernel : Contract} {runtime : ActorRuntime kernel} {actor : ActorId}
    {fd : UInt64} {handle : Handle} {α : Type} {program : Program α} {first last : α → Prop}
    (source : ActorBorrowPost runtime actor fd handle first program)
    (weaken : ∀ value, first value → last value) : ActorBorrowPost runtime actor fd handle last program := by
  induction source with
  | pure property => exact .pure (weaken _ property)
  | call preserve following ih => exact .call preserve ih

theorem perform_passive_borrow {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle) (request : Request)
    (passive : RetainsDescriptors request.op) :
    ActorBorrowPost runtime actor held handle (fun _ => True) (Runtime.perform request) :=
  actor_borrow_lift actor (passive_borrow laws held handle request passive)

theorem perform_fresh_borrow {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle) (request : Request)
    (allocating : AllocatesDescriptor request.op) :
    ActorBorrowPost runtime actor held handle (fun reply => ∀ fd, descriptor reply = some fd → fd ≠ held)
      (Runtime.perform request) := actor_borrow_lift actor (open_fresh_borrow laws held handle request allocating)

theorem vm_close_borrow {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle)
    (fd : UInt64) (different : fd ≠ held) :
    ActorBorrowPost runtime actor held handle (fun _ => True) (VirtualMachine.close fd) := by
  apply ActorBorrowPost.call
  · intro before after observed actual live
    change kernel.step before {op := .close, first := fd} observed after at actual
    rw [laws.close_other _ _ _ _ _ actual rfl (Ne.symm different)]
    exact live
  · intro before after reply actual live
    exact .pure True.intro

theorem clock_borrow {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle) :
    ActorBorrowPost runtime actor held handle (fun _ => True) Runtime.clock := by
  unfold Runtime.clock
  apply actor_borrow_bind (perform_passive_borrow laws actor held handle _ (by simp [RetainsDescriptors]))
  intro reply _
  split
  · exact .pure True.intro
  · dsimp only; split <;> exact .pure True.intro

theorem poll_borrow {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle)
    (descriptors : List (UInt64 × Nat)) (milliseconds : Nat) :
    ActorBorrowPost runtime actor held handle (fun _ => True) (Runtime.poll descriptors milliseconds) := by
  unfold Runtime.poll
  split
  · exact .pure True.intro
  · apply actor_borrow_bind (perform_passive_borrow laws actor held handle _ (by simp [RetainsDescriptors]))
    intro reply _
    repeat' first | exact .pure True.intro | split

theorem runtime_read_borrow {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle) (fd : UInt64) (amount : Nat) :
    ActorBorrowPost runtime actor held handle (fun _ => True) (Runtime.read fd amount) := by
  unfold Runtime.read
  split
  · exact .pure True.intro
  · apply actor_borrow_bind (perform_passive_borrow laws actor held handle _ (by simp [RetainsDescriptors]))
    intro reply _
    repeat' first | exact .pure True.intro | split

end LeanCage.Host.Kernel

namespace LeanCage.Host.VirtualMachine
open Filesystem
open Kernel

def FreshConnection (held : UInt64) (connection : Option UInt64) : Prop :=
  ∀ fd, connection = some fd → fd ≠ held

private theorem fail_fresh {held : UInt64} {state : State} (fresh : ConnectionFresh held state) (message : String) :
    ConnectionFresh held (state.fail message) := fresh

theorem connect_borrow {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle) (path : ByteArray) :
    ActorBorrowPost runtime actor held handle (Successful (FreshConnection held)) (connect path) := by
  unfold connect
  split
  · exact .pure True.intro
  · apply actor_borrow_bind (perform_fresh_borrow laws actor held handle _ (.inr (.inl rfl)))
    intro created fresh
    split
    · rename_i fd recognized
      apply actor_borrow_bind (perform_passive_borrow laws actor held handle _ (by simp [RetainsDescriptors]))
      intro connected _
      split
      · apply ActorBorrowPost.pure
        intro query same
        have sameFd := Option.some.inj same
        subst query
        exact fresh fd recognized
      · apply actor_borrow_bind (vm_close_borrow laws actor held handle fd (fresh fd recognized))
        intro ignored _
        split
        · exact .pure (by intro query same; cases same)
        · exact .pure True.intro
    · exact .pure True.intro

theorem consume_borrow {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle)
    (fd boot diagnostic : UInt64) (now : Nat) (state : State) (fresh : ConnectionFresh held state) :
    ActorBorrowPost runtime actor held handle (ConnectionFresh held) (consume fd boot diagnostic now state) := by
  unfold consume
  apply actor_borrow_bind (runtime_read_borrow laws actor held handle _ _)
  intro read _
  cases read with
  | error error => exact .pure (fail_fresh fresh _)
  | ok result =>
    cases result with
    | pending => exact .pure fresh
    | eof => repeat' first | exact .pure fresh | (dsimp only; split) | split
    | data part =>
      repeat' first | exact .pure fresh | exact .pure (fail_fresh fresh _) | (dsimp only; split) | split

theorem consume_ready_borrow {kernel : Contract} {runtime : ActorRuntime kernel}
    (laws : DescriptorContract kernel) (actor : ActorId) (held : UInt64) (handle : Handle)
    (descriptors : List (UInt64 × Nat)) (ready : List Nat) (boot diagnostic : UInt64) (now : Nat)
    (state : State) (fresh : ConnectionFresh held state) :
    ActorBorrowPost runtime actor held handle (ConnectionFresh held)
      (consumeReady descriptors ready boot diagnostic now state) := by
  induction descriptors generalizing ready state with
  | nil => cases ready <;> exact .pure fresh
  | cons descriptor rest ih =>
    cases ready with
    | nil => exact .pure fresh
    | cons outcome ready =>
      unfold consumeReady
      split
      · apply actor_borrow_bind (first := ConnectionFresh held) (.pure fresh)
        intro next nextFresh
        dsimp only
        split
        · exact .pure nextFresh
        · exact ih ready next nextFresh
      · apply actor_borrow_bind (consume_borrow laws actor held handle _ _ _ _ _ fresh)
        intro next nextFresh
        dsimp only
        split
        · exact .pure nextFresh
        · exact ih ready next nextFresh


end LeanCage.Host.VirtualMachine
