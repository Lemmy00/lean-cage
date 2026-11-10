import FilesystemPendingPrefixPhases

namespace LeanCage.Host.Kernel
open Filesystem

def AvoidsWrite (held : UInt64) : {β : Type} → Effect β → Prop
  | _, .filesystem request => request.op = .write → request.first ≠ held
  | _, _ => True

-- §FS-host-boundary.caller: Each actual operation preserves this raw channel and cannot
-- write to it. Returned values and SDK effects keep their individual primitive laws.
inductive ChannelWritePost {kernel : Contract} {sourceProgram : Program UInt32}
    (runtime : ActorRuntime kernel sourceProgram) (actor : ActorId) (held : UInt64) (handle : Handle)
    {α : Type} (post : α → Prop) : Program α → Prop where
  | pure {value : α} (property : post value) : ChannelWritePost runtime actor held handle post (.pure value)
  | call {β : Type} {effect : Effect β} {next : β → Program α}
      (avoid : AvoidsWrite held effect)
      (raw : PrimitiveFilesystem.lowerEffect effect = Program.effect effect)
      (preserve : ∀ before after observed, ActorOperation runtime actor effect observed before after →
        before.handles held = some handle → after.handles held = some handle)
      (following : ∀ before after reply, ActorOperation runtime actor effect (some reply) before after →
        before.handles held = some handle → ChannelWritePost runtime actor held handle post (next reply)) :
      ChannelWritePost runtime actor held handle post (.call effect next)

theorem channel_bind {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId} {held : UInt64} {handle : Handle}
    {α β : Type} {program : Program α} {next : α → Program β} {first : α → Prop} {post : β → Prop}
    (source : ChannelWritePost runtime actor held handle first program)
    (tail : ∀ value, first value → ChannelWritePost runtime actor held handle post (next value)) :
    ChannelWritePost runtime actor held handle post (program.bind next) := by
  induction source with
  | pure property => exact tail _ property
  | call avoid raw preserve following ih => exact .call avoid raw preserve ih

theorem channel_weaken {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId} {held : UInt64} {handle : Handle}
    {α : Type} {program : Program α} {first post : α → Prop}
    (source : ChannelWritePost runtime actor held handle first program) (weaken : ∀ value, first value → post value) :
    ChannelWritePost runtime actor held handle post program := by
  induction source with
  | pure property => exact .pure (weaken _ property)
  | call avoid raw preserve following ih => exact .call avoid raw preserve ih

-- §AR-host-boundary.primitives: Lowering remains tied to each actual request. Only the
-- checked source's raw-identity operations are used; no whole blocked-call interval is framed.
theorem channel_lower {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId} {held : UInt64} {handle : Handle}
    {α : Type} {program : Program α} {post : α → Prop}
    (source : ChannelWritePost runtime actor held handle post program) :
    ChannelWritePost runtime actor held handle post (PrimitiveFilesystem.lower program) := by
  induction source with
  | pure property => exact .pure property
  | @call β effect next avoid raw preserve following ih =>
    change ChannelWritePost runtime actor held handle post
      ((PrimitiveFilesystem.lowerEffect effect).bind (fun reply => PrimitiveFilesystem.lower (next reply)))
    rw [raw]
    exact .call avoid raw preserve ih

-- §FS-host-boundary.acceptance: Pending writes are excluded before any current operation
-- reply/effect. Earlier actual returned calls and arbitrary peer interference remain present.
theorem channel_pending_avoids {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId} {held : UInt64} {handle : Handle}
    {α : Type} {program : Program α} {post : α → Prop}
    (source : ChannelWritePost runtime actor held handle post program)
    {origin : OperationOrigin} {ordinal : Nat} {before current : World} {events : List Program.Event}
    (history : ActorHistoryWith runtime actor origin ordinal before events current)
    {request : Request} (pending : Program.Prefix program (events ++ [.lost (.filesystem request)]))
    (live : before.handles held = some handle) (writing : request.op = .write) : request.first ≠ held := by
  induction history generalizing program with
  | nil =>
    cases pending with
    | lost => cases source with | call avoid raw preserve following => exact avoid writing
  | environment actual tail ih =>
    exact ih source pending (by rw [kernel.interference_handles _ _ actual]; exact live)
  | returned actual sampled tail ih =>
    cases pending with
    | returned effect next reply rest continued =>
      cases source with
      | call avoid raw preserve following => exact ih (following _ _ _ actual live) continued (preserve _ _ _ actual live)

theorem channel_runtime {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (sdk : RuntimeDescriptorContract runtime)
    (actor : ActorId) (held : UInt64) (handle : Handle) {β : Type} (effect : Effect β)
    (kind : RuntimeEffect effect) (raw : handle.rawOwned = true) :
    ChannelWritePost runtime actor held handle (fun _ => True) (Program.effect effect) := by
  apply ChannelWritePost.call
  · cases effect <;> first | exact False.elim kind | exact True.intro
  · cases effect <;> first | exact False.elim kind | rfl
  · intro before after observed actual live
    exact runtime_keeps_raw sdk actor effect actual kind live raw
  · intro before after reply actual live
    exact .pure True.intro

end LeanCage.Host.Kernel
