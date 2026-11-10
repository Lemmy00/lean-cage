import FilesystemAccessProofs

namespace LeanCage.Host.Filesystem

-- §AR-host-boundary.primitives: The adapter's extra operations are source-derived probes/closes.
inductive RequestProfile (allowed : Request → Prop) {α : Type} : Program α → Prop where
  | pure (value : α) : RequestProfile allowed (.pure value)
  | call (request : Request) (next : Reply → Program α) (permitted : allowed request)
      (rest : ∀ reply, RequestProfile allowed (next reply)) : RequestProfile allowed (.call request next)

theorem profile_bind {α β : Type} {allowed : Request → Prop} {program : Program α}
    {next : α → Program β} (initial : RequestProfile allowed program)
    (rest : ∀ value, RequestProfile allowed (next value)) : RequestProfile allowed (program.bind next) := by
  induction initial with
  | pure value => exact rest value
  | call request next permitted continued ih => exact .call _ _ permitted (fun reply => ih reply)

theorem profile_prefix {α : Type} {allowed : Request → Prop} {program : Program α}
    (profile : RequestProfile allowed program) {events : List (Request × Option Reply)}
    (source : Prefix program events) : ∀ event ∈ events, allowed event.1 := by
  induction source with
  | empty => simp
  | lost request next =>
    cases profile with
    | call _ _ permitted rest => intro event member; simpa only [List.mem_singleton.mp member] using permitted
  | returned request next reply tail rest ih =>
    cases profile with
    | call _ _ permitted continued =>
      intro event member
      rcases List.mem_cons.mp member with rfl | later
      · exact permitted
      · exact ih (continued reply) event later

theorem profile_returns {α : Type} {allowed : Request → Prop} {program : Program α}
    (profile : RequestProfile allowed program) {events : List (Request × Reply)} {result : α}
    (source : Returns program events result) : ∀ event ∈ events, allowed event.1 := by
  induction source with
  | pure => simp
  | call request next reply tail value rest ih =>
    cases profile with
    | call _ _ permitted continued =>
      intro event member
      rcases List.mem_cons.mp member with rfl | later
      · exact permitted
      · exact ih (continued reply) event later

theorem lookup_check_profile (fd : UInt64) (allowed : Request → Prop)
    (magic : allowed { op := .filesystemType, first := fd })
    (flags : allowed { op := .inodeFlags, first := fd }) : RequestProfile allowed (Lookup.check fd) := by
  unfold Lookup.check
  apply RequestProfile.call _ _ magic
  intro observed
  split
  · exact .pure _
  · split
    · exact .pure _
    · split
      · exact .call _ _ flags (fun _ => .pure _)
      · exact .pure _

def AdapterRequest (primary candidate : Request) : Prop :=
  candidate = primary ∨ candidate.op = .filesystemType ∨ candidate.op = .inodeFlags ∨ candidate.op = .close

theorem lookup_all_profile (primary : Request) (fds : List UInt64) :
    RequestProfile (AdapterRequest primary) (Lookup.checkAll fds) := by
  induction fds with
  | nil => exact .pure _
  | cons fd rest ih =>
    unfold Lookup.checkAll
    apply profile_bind (lookup_check_profile _ _ (.inr (.inl rfl)) (.inr (.inr (.inl rfl))))
    intro accepted
    split
    · exact ih
    · exact .pure _

theorem lookup_opened_profile (primary : Request) (reply : Reply) :
    RequestProfile (AdapterRequest primary) (Lookup.opened primary reply) := by
  unfold Lookup.opened
  split
  · split
    · exact .pure _
    · apply profile_bind (lookup_check_profile _ _ (.inr (.inl rfl)) (.inr (.inr (.inl rfl))))
      intro accepted
      split
      · exact .pure _
      · exact .call _ _ (.inr (.inr (.inr rfl))) (fun _ => .pure _)
  · exact .pure _

theorem guarded_call_profile (primary : Request) :
    RequestProfile (AdapterRequest primary) (guardedCall primary) := by
  unfold guardedCall
  apply profile_bind (lookup_all_profile primary _)
  intro accepted
  split
  · exact .pure _
  · exact .call _ _ (.inl rfl) (lookup_opened_profile primary)

-- §FS-host-boundary.lookup: A selected namespace operation retains the original source arguments.
theorem guarded_namespace_origin {primary : Request} {events : List (Request × Option Reply)}
    (source : Prefix (guardedCall primary) events) {event : Request × Option Reply}
    (selected : event ∈ events) (namespaceOperation : event.1.op = .openAt ∨ event.1.op = .mkdirAt ∨
      event.1.op = .unlinkAt ∨ event.1.op = .renameNew ∨ event.1.op = .dirOpen) : event.1 = primary := by
  rcases profile_prefix (guarded_call_profile primary) source event selected with actual | probe | flags | close
  · exact actual
  all_goals rcases namespaceOperation with actual | actual | actual | actual | actual <;> simp_all

end LeanCage.Host.Filesystem
