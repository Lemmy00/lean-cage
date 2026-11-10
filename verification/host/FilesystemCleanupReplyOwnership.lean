import FilesystemCleanupCaptured

namespace LeanCage.Host.Kernel
open Filesystem

def PrivateUnlinkReplies {kernel : Contract} (origin : OperationOrigin) (family : Family)
    (scope ordinal : Nat) (events : List (Request × Reply)) : Prop :=
  ∀ offset request reply, events[offset]? = some (request, reply) → request.op = .unlinkAt →
    Nonempty (CapturedPrivateUnlink (kernel := kernel) (origin := origin) family scope (ordinal + offset) request reply)

theorem private_unlink_replies_append {kernel : Contract} {origin : OperationOrigin} {family : Family}
    {scope ordinal : Nat} {first last : List (Request × Reply)}
    (leading : PrivateUnlinkReplies (kernel := kernel) origin family scope ordinal first)
    (trailing : PrivateUnlinkReplies (kernel := kernel) origin family scope (ordinal + first.length) last) :
    PrivateUnlinkReplies (kernel := kernel) origin family scope ordinal (first ++ last) := by
  intro offset request reply selected unlink
  by_cases inside : offset < first.length
  · exact leading offset request reply (by simpa only [List.getElem?_append_left inside] using selected) unlink
  · have afterFirst : first.length ≤ offset := by omega
    have actual := trailing (offset - first.length) request reply
      (by simpa only [List.getElem?_append_right afterFirst] using selected) unlink
    have count : ordinal + first.length + (offset - first.length) = ordinal + offset := by omega
    exact count ▸ actual

theorem no_unlink_replies {kernel : Contract} {origin : OperationOrigin} {family : Family}
    {scope ordinal : Nat} {events : List (Request × Reply)}
    (source : ∀ pair ∈ events, pair.1.op ≠ .unlinkAt) :
    PrivateUnlinkReplies (kernel := kernel) origin family scope ordinal events := by
  intro offset request reply selected unlink
  exact False.elim (source (request, reply) (List.mem_of_getElem? selected) unlink)

private theorem post_as_uses {kernel : Contract} {held : UInt64} {handle : Handle} {α : Type}
    {program : Filesystem.Program α} {post : α → Prop}
    (source : BorrowPost kernel held handle post program) :
    BorrowUses kernel held handle (fun _ => True) program := by
  induction source with
  | pure => exact .unused (.pure _)
  | call preserve following ih => exact .call preserve ih

private theorem returns_prefix {α : Type} {program : Filesystem.Program α}
    {events : List (Request × Reply)} {value : α} (source : Returns program events value) :
    Prefix program (Publication.completed events) := by
  induction source with
  | pure => exact .empty _
  | call request next reply tail value rest ih => exact .returned request next reply _ ih

-- §FS-host-boundary.ownership: The concrete held-FD source profile produces
-- each completed removal's SAME sampled input, including ignored errors.
theorem held_unlink_replies {kernel : Contract} {origin : OperationOrigin} {family : Family}
    {held : UInt64} {handle : Handle} {scope ordinal : Nat} {α : Type}
    {program : Filesystem.Program α} {post : α → Prop} {events : List (Request × Reply)}
    {before after : World} {value : α}
    (borrowed : BorrowPost kernel held handle post program)
    (profile : RequestProgram (fun query => query.op = .unlinkAt →
      query.first = held ∧ Directories.component query.left = true) program)
    (run : RecordedRun kernel (fun index request reply => origin index Reply (.filesystem request) reply)
      ordinal program before events after value)
    (live : before.handles held = some handle) (privateHandle : family handle.object = some scope) :
    PrivateUnlinkReplies (kernel := kernel) origin family scope ordinal events := by
  intro offset request reply selected unlink
  obtain ⟨atCall, afterCall, actual, sampled, reference⟩ := borrowed_recorded_use_at (post_as_uses borrowed)
    (returns_prefix run.1) run.2 live selected
  have operand := requests_returned profile run.1 (request, reply) (List.mem_of_getElem? selected) unlink
  exact ⟨⟨atCall, afterCall, actual, sampled, handle, operand.1 ▸ reference True.intro,
    privateHandle, operand.2⟩⟩

private theorem adapter_unlink_profile {allowed : Request → Prop} {primary : Request}
    (accepted : primary.op = .unlinkAt → allowed primary) {α : Type} {program : Filesystem.Program α}
    (source : RequestProfile (AdapterRequest primary) program) :
    RequestProgram (fun query => query.op = .unlinkAt → allowed query) program := by
  induction source with
  | pure => exact .pure _
  | call request next role following ih =>
    apply RequestProgram.call ?_ ih
    intro unlink
    rcases role with same | magic | flags | close
    · rw [same] at unlink ⊢; exact accepted unlink
    · rw [magic] at unlink; cases unlink
    · rw [flags] at unlink; cases unlink
    · rw [close] at unlink; cases unlink

theorem lower_unlink_profile {allowed : Request → Prop} {α : Type} {program : Filesystem.Program α}
    (source : RequestProgram (fun query => query.op = .unlinkAt → allowed query) program) :
    RequestProgram (fun query => query.op = .unlinkAt → allowed query) program.lower := by
  induction source with
  | pure => exact .pure _
  | call accepted following ih => exact request_bind (adapter_unlink_profile accepted (guarded_call_profile _)) ih

theorem export_cleanup_replies {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (descriptors : DescriptorContract kernel)
    (actor : ActorId) (origin : OperationOrigin) (limit : Nat) {family : Family}
    (opens : PrivateDirectoryOpens kernel (fun index request reply before after =>
      origin index Reply (.filesystem request) reply before after ∧ index < limit) family)
    {uid : Nat} {root : Directories.Opened} {input : Publication.Input}
    {ordinal : Nat} {before after : World} {events : List (Request × Reply)}
    (run : RecordedRun kernel (fun index request reply => origin index Reply (.filesystem request) reply)
      ordinal (Publication.cleanupExport uid root input).lower before events after ())
    (bounded : ordinal + events.length ≤ limit) {rootHandle : Handle} {scope : ObjectId}
    (live : before.handles root.fd = some rootHandle) (privateRoot : family rootHandle.object = some scope) :
    PrivateUnlinkReplies (kernel := kernel) origin family scope ordinal events := by
  intro offset request reply selected unlink
  exact actual_export_cleanup_capture (runtime := runtime) descriptors actor origin limit opens run bounded live privateRoot selected unlink

end LeanCage.Host.Kernel
