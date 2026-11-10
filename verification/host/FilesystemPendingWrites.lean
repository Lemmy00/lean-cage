import FilesystemPendingPrefixPhases
import FilesystemLoweredWrites
import FilesystemWriteSources.ReadOnly

namespace LeanCage.Host.Kernel
open Filesystem

private theorem raw_history_forget {kernel : Contract} {origin : RawOrigin} {ordinal : Nat}
    {before after : World} {events : List (Request × Reply)}
    (source : RawHistory kernel.step kernel.interference origin ordinal before events after) :
    History kernel before events after := by
  induction source with
  | nil => exact .nil _
  | environment actual tail ih => exact .environment actual ih
  | call actual sampled tail ih => exact .cons actual ih

private theorem raw_before_pending {kernel : Contract} {origin : RawOrigin} {ordinal : Nat}
    {α : Type} {program : Filesystem.Program α} {before after : World} {events : List (Request × Option Reply)}
    {request : Request} (source : Prefix program (events ++ [(request, none)]))
    (history : RawPrefixHistory kernel.step kernel.interference origin ordinal before events after) :
    PhysicalPrefix kernel program before events after := by
  induction history generalizing program with
  | stop => exact .stop _ _
  | environment actual tail ih => exact .environment actual (ih source)
  | lost actual sampled => cases source
  | returned actual sampled tail ih =>
    cases source with
    | returned request next reply rest continued => exact .returned actual (ih continued)

private theorem pure_no_last {α : Type} (value : α) {before : List (Request × Option Reply)}
    {event : Request × Option Reply} (source : Prefix (.pure value) (before ++ [event])) : False := by
  have empty := Snapshot.prefix_pure_empty source
  have lengths := congrArg List.length empty
  simp only [List.length_append, List.length_singleton, List.length_nil] at lengths
  omega

private theorem adapter_no_write {request candidate : Request} (opening : request.op = .openAt)
    (role : AdapterRequest request candidate) : candidate.op ≠ .write := by
  rcases role with same | magic | flags | close
  · rw [same, opening]; decide
  · rw [magic]; decide
  · rw [flags]; decide
  · rw [close]; decide

private theorem close_no_write {α : Type} (fd : UInt64) (value : Result α) :
    RequestProgram (fun request => request.op ≠ .write) (closeResult fd value) := by
  apply RequestProgram.call (by intro wrong; cases wrong)
  intro reply
  cases value with
  | error => exact .pure _
  | ok => dsimp only; split <;> exact .pure _

-- §AR-host-boundary.interfaces: This verification alias is the exact actual exclusive-open
-- expression shared by ordinary publication writers and the archive's streamed content.
def exclusiveWriter (parent : UInt64) (name : ByteArray) (mode : UInt64)
    (writer : UInt64 → Filesystem.Program (Result Unit)) (message : String) : Filesystem.Program (Result Unit) :=
  .call {op := .openAt, first := parent, second := newFileFlags, third := mode, left := name} fun reply =>
    match descriptor reply with
    | none => .pure (.error (failure message reply))
    | some fd => (writer fd).bind (closeResult fd)

private theorem scoped_writer_identity {α : Type} {fd : UInt64} {program : Filesystem.Program α}
    (scope : Image.WriteProgram fd program) : program.lower = program := by
  apply Lowered.lowering_identity
  induction scope with
  | pure => exact .pure _
  | @call request next allowed tail ih =>
    apply RequestProfile.call _ _ ?_ ih
    rcases request with ⟨operation, first, second, third, left, right⟩
    have writing := allowed.1
    cases writing
    rfl

private theorem scoped_writer_borrow {kernel : Contract} (descriptors : DescriptorContract kernel)
    (held : UInt64) (handle : Handle) {α : Type} {fd : UInt64} {program : Filesystem.Program α}
    (scope : Image.WriteProgram fd program) : BorrowPost kernel held handle (fun _ => True) program := by
  induction scope with
  | pure => exact .pure True.intro
  | @call request next allowed tail ih =>
    apply BorrowPost.call
    · intro before after observed actual live
      rw [descriptors.retained _ _ _ _ actual (by simp only [RetainsDescriptors, allowed.1]; decide)]
      exact live
    · intro before after reply actual live
      exact ih reply

private theorem scoped_close_identity {fd : UInt64} {program : Filesystem.Program (Result Unit)}
    (scope : Image.WriteProgram fd program) :
    (program.bind (closeResult fd)).lower = program.bind (closeResult fd) := by
  rw [Filesystem.Program.lower_bind, scoped_writer_identity scope]
  exact congrArg (Filesystem.Program.bind program) (funext (Lowered.close_result_identity fd))

-- §FS-host-boundary.ownership: A pending writer's current FD names the actual O_EXCL-born
-- file. No current write effect, successful future ACK or alternative kernel run is needed.
theorem pending_exclusive_writer_reference {kernel : Contract} (descriptors : DescriptorContract kernel)
    {origin : RawOrigin} {ordinal : Nat} (parent : UInt64) (name : ByteArray) (mode : UInt64)
    (writer : UInt64 → Filesystem.Program (Result Unit)) (scope : ∀ fd, Image.WriteProgram fd (writer fd))
    (message : String)
    {before current : World} {events : List (Request × Option Reply)} {request : Request}
    (source : Prefix (exclusiveWriter parent name mode writer message).lower (events ++ [(request, none)]))
    (history : RawPrefixHistory kernel.step kernel.interference origin ordinal before events current)
    (writing : request.op = .write) :
    ∃ handle, current.handles request.first = some handle ∧ before.allocated handle.object = false := by
  let opening : Request := {op := .openAt, first := parent, second := newFileFlags, third := mode, left := name}
  let next (reply : Reply) : Filesystem.Program (Result Unit) := match descriptor reply with
    | none => .pure (.error (failure message reply))
    | some fd => (writer fd).bind (closeResult fd)
  have source : Prefix ((guardedCall opening).bind (fun reply => (next reply).lower))
      (events ++ [(request, none)]) := source
  rcases filesystem_last_bind_split _ _ source with checking |
      ⟨opened, reply, remaining, openedSource, afterOpen, trace⟩
  · have role := profile_prefix (guarded_call_profile opening) checking (request, none) (by simp)
    exact False.elim (adapter_no_write rfl role writing)
  · have history := history
    rw [trace] at history
    obtain ⟨openedWorld, openingHistory, remainingHistory⟩ := raw_prefix_split opened remaining history
    unfold next at afterOpen
    cases recognized : descriptor reply with
    | none =>
      rw [recognized] at afterOpen
      exact False.elim (pure_no_last _ afterOpen)
    | some fd =>
      rw [recognized] at afterOpen
      have actualOpen : ConcurrentRun kernel (guardedCall opening) before opened openedWorld reply :=
        ⟨openedSource, raw_history_forget openingHistory⟩
      obtain ⟨handle, live, fresh⟩ := Lowered.guarded_exclusive_fresh kernel parent name mode actualOpen recognized
      have afterOpen : Prefix ((writer fd).bind (closeResult fd))
          (remaining ++ [(request, none)]) := scoped_close_identity (scope fd) ▸ afterOpen
      have active : Prefix (writer fd) (remaining ++ [(request, none)]) := by
        rcases filesystem_last_bind_split _ _ afterOpen with active |
            ⟨written, value, inside, completed, closing, trace⟩
        · exact active
        · exact False.elim (request_prefix (close_no_write fd value) closing (request, none) (by simp) writing)
      have currentLive := borrow_prefix (scoped_writer_borrow descriptors fd handle (scope fd))
        (raw_before_pending active remainingHistory) live
      have first := (Image.write_prefix (scope fd) active (request, none) (by simp)).2.1
      exact ⟨handle, first.symm ▸ currentLive, fresh⟩

theorem pending_new_file_reference {kernel : Contract} (descriptors : DescriptorContract kernel)
    {origin : RawOrigin} {ordinal : Nat} (parent : UInt64) (name bytes : ByteArray) (mode : UInt64)
    {before current : World} {events : List (Request × Option Reply)} {request : Request}
    (source : Prefix (writeNew parent name bytes mode).lower (events ++ [(request, none)]))
    (history : RawPrefixHistory kernel.step kernel.interference origin ordinal before events current)
    (writing : request.op = .write) :
    ∃ handle, current.handles request.first = some handle ∧ before.allocated handle.object = false := by
  unfold writeNew at source
  split at source
  · exact False.elim (pure_no_last _ source)
  · exact pending_exclusive_writer_reference descriptors parent name mode
      (fun fd => writeLoop (bytes.size + 1) fd bytes 0) (fun fd => Image.writeLoop_scoped _ fd _ _)
      "exclusive openat" source history writing

private theorem guarded_no_write (request : Request) (notWrite : request.op ≠ .write) :
    RequestProgram NoWrite (guardedCall request) := by
  have profile := guarded_call_profile request
  generalize actual : guardedCall request = program at profile ⊢
  clear actual
  induction profile with
  | pure => exact .pure _
  | @call candidate next allowed tail ih =>
    apply RequestProgram.call _ ih
    rcases allowed with same | magic | flags | close
    · rw [same]; exact notWrite
    · intro writing; rw [magic] at writing; cases writing
    · intro writing; rw [flags] at writing; cases writing
    · intro writing; rw [close] at writing; cases writing

private theorem lower_no_write {α : Type} {program : Filesystem.Program α}
    (source : RequestProgram NoWrite program) : RequestProgram NoWrite program.lower := by
  induction source with
  | pure => exact .pure _
  | @call request next allowed tail ih => exact request_bind (guarded_no_write request allowed) ih

private theorem raw_history_allocated {kernel : Contract} {origin : RawOrigin} {ordinal : Nat}
    {before after : World} {events : List (Request × Reply)}
    (history : RawHistory kernel.step kernel.interference origin ordinal before events after)
    {object : ObjectId} (allocated : before.allocated object = true) : after.allocated object = true := by
  induction history with
  | nil => exact allocated
  | call actual sampled tail ih => exact ih (kernel.allocation_monotone _ _ _ _ _ actual allocated)
  | environment actual tail ih => exact ih (kernel.interference_allocation _ _ _ actual allocated)

-- §FS-host-boundary.snapshot: The pending archive write uses the source's actual exclusive
-- request.cpio open after its bounded identified-base copy, and its retained current file FD.
theorem pending_image_reference {kernel : Contract} (descriptors : DescriptorContract kernel)
    {origin : RawOrigin} {ordinal : Nat} (runFd : UInt64) (bundle : Validation.Bundle) (overlay : List Image.Entry)
    {before current : World} {events : List (Request × Option Reply)} {request : Request}
    (source : Prefix (Image.create runFd bundle overlay).lower (events ++ [(request, none)]))
    (history : RawPrefixHistory kernel.step kernel.interference origin ordinal before events current)
    (writing : request.op = .write) :
    ∃ handle, current.handles request.first = some handle ∧ before.allocated handle.object = false := by
  unfold Image.create at source
  split at source
  · exact False.elim (pure_no_last _ source)
  · change Prefix ((Validation.copyIdentified bundle "profile/runtime.cpio.gz" workspaceMax).bind _).lower
        (events ++ [(request, none)]) at source
    rw [Filesystem.Program.lower_bind] at source
    rcases filesystem_last_bind_split _ _ source with copying |
        ⟨copied, result, remaining, copiedSource, afterCopy, trace⟩
    · have profile := lower_no_write (read_only_no_write
        (Image.copyIdentified_readOnly bundle "profile/runtime.cpio.gz" workspaceMax))
      exact False.elim (request_prefix profile copying (request, none) (by simp) writing)
    · have history := history
      rw [trace] at history
      obtain ⟨copiedWorld, copyingHistory, remainingHistory⟩ := raw_prefix_split copied remaining history
      cases result with
      | error error => exact False.elim (pure_no_last _ afterCopy)
      | ok base =>
        have source : Prefix (exclusiveWriter runFd "request.cpio".toUTF8 384
            (fun fd => Image.content fd base overlay) "request archive openat").lower
            (remaining ++ [(request, none)]) := afterCopy
        obtain ⟨handle, live, fresh⟩ := pending_exclusive_writer_reference descriptors runFd "request.cpio".toUTF8 384
          (fun fd => Image.content fd base overlay) (fun fd => Image.content_scoped fd base overlay)
          "request archive openat" source remainingHistory writing
        refine ⟨handle, live, ?_⟩
        cases old : before.allocated handle.object with
        | false => rfl
        | true =>
          have current := raw_history_allocated copyingHistory old
          rw [current] at fresh
          cases fresh

theorem actor_history_allocated {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (lifetimes : LifetimeContract runtime)
    {actor : ActorId} {origin : OperationOrigin} {ordinal : Nat} {before after : World}
    {events : List Program.Event} (history : ActorHistoryWith runtime actor origin ordinal before events after)
    {object : ObjectId} (allocated : before.allocated object = true) : after.allocated object = true := by
  induction history with
  | nil => exact allocated
  | environment actual tail ih => exact ih (kernel.interference_allocation _ _ _ actual allocated)
  | returned actual sampled tail ih => exact ih (operation_allocated lifetimes actual _ allocated)

-- §FS-host-boundary.caller: The same earlier live IPC lifetime cannot equal this fresh file.
theorem pending_file_excludes_inherited {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request}
    (parent : UInt64) (name bytes : ByteArray) (mode : UInt64)
    (phase : PendingPrefixPhase runtime initial all tick actor engine request (writeNew parent name bytes mode))
    (writing : request.op = .write) {object : ObjectId}
    (inherited : (phase.source.launch.tick.after.project (.initialFrom (PrimitiveFilesystem.lower Entrypoint.run)
      phase.source.launch.references phase.source.launch.closeExec phase.source.launch.workingDirectory)).allocated object = true) :
    ∃ handle, engine.references request.first = some handle ∧ handle.object ≠ object := by
  have raw : RawPrefixHistory kernel.step kernel.interference (SourceRawAt runtime all actor) phase.rawBefore.length
      phase.before (Publication.completed phase.earlier) (tick.before.project engine) := by
    have history := raw_history_then_prefix phase.sampled
      (RawPrefixHistory.stop (step := kernel.step) (interference := kernel.interference)
        (origin := SourceRawAt runtime all actor) _ (tick.before.project engine))
    simpa only [Publication.completed, List.append_nil] using history
  obtain ⟨handle, live, fresh⟩ := pending_new_file_reference descriptors parent name bytes mode phase.active raw writing
  have old := actor_history_allocated lifetimes phase.leading inherited
  refine ⟨handle, live, ?_⟩
  intro same
  rw [same, old] at fresh
  cases fresh

end LeanCage.Host.Kernel
