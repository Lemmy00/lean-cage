import FilesystemPrimitiveSources

namespace LeanCage.Host.PrimitiveFilesystem

-- §AR-host-boundary.primitives: Logical phase splitting keeps the exact completed raw chunks.
inductive Chunks : List Program.Event → List Program.Event → Prop where
  | nil : Chunks [] []
  | cons {β : Type} (effect : Effect β) (reply : β) (inside logical raw : List Program.Event)
      (adapter : Program.Returns (lowerEffect effect) inside reply) (rest : Chunks logical raw) :
      Chunks (.returned effect reply :: logical) (inside ++ raw)

theorem reached_chunks {α : Type} {program after : Program α} {logical raw : List Program.Event}
    (source : Reached program logical raw after) : Chunks logical raw := by
  induction source with
  | refl => exact .nil
  | call effect next reply inside logical raw after adapter rest ih => exact .cons effect reply inside logical raw adapter ih

theorem chunks_split {raw : List Program.Event} (first last : List Program.Event)
    (source : Chunks (first ++ last) raw) :
    ∃ initial final, Chunks first initial ∧ Chunks last final ∧ raw = initial ++ final := by
  induction first generalizing raw with
  | nil => exact ⟨[], raw, .nil, source, rfl⟩
  | cons event rest ih =>
    cases source with
    | cons effect reply inside logical raw adapter tail =>
      obtain ⟨initial, final, first, last, shape⟩ := ih tail
      exact ⟨inside ++ initial, final, .cons effect reply inside rest initial adapter first,
        last, by rw [shape, List.append_assoc]⟩

theorem chunks_returns {α : Type} {program : Program α} {logical raw : List Program.Event} {value : α}
    (run : Program.Returns program logical value) (source : Chunks logical raw) :
    Program.Returns (lower program) raw value := by
  induction run generalizing raw with
  | pure value => cases source; exact .pure value
  | call effect next reply tail value following ih =>
    cases source with
    | cons effect reply inside logical raw adapter rest =>
      exact Program.returns_bind adapter (ih rest)

-- §AR-host-boundary.primitives: A completed actual lowered helper retains the original
-- source returns AND every real raw guard chunk; no probes or rejection branches disappear.
theorem lowered_returns_chunks {α : Type} (program : Program α) {raw : List Program.Event} {value : α}
    (run : Program.Returns (lower program) raw value) :
    ∃ logical, Program.Returns program logical value ∧ Chunks logical raw := by
  induction program generalizing raw with
  | pure result =>
    obtain ⟨rfl, rfl⟩ := Program.returns_pure _ run
    exact ⟨[], .pure _, .nil⟩
  | @call β effect next ih =>
    change Program.Returns ((lowerEffect effect).bind (fun reply => lower (next reply))) raw value at run
    obtain ⟨inside, reply, remaining, first, tail, shape⟩ := Program.returns_bind_split _ _ run
    obtain ⟨logical, source, chunks⟩ := ih reply tail
    exact ⟨.returned effect reply :: logical, .call effect next reply logical value source,
      shape ▸ Chunks.cons effect reply inside logical remaining first chunks⟩

theorem filesystem_events_injective {first last : List (Filesystem.Request × Filesystem.Reply)}
    (same : first.map Program.filesystemEvent = last.map Program.filesystemEvent) : first = last := by
  induction first generalizing last with
  | nil => cases last <;> cases same; rfl
  | cons head rest ih =>
    cases last with
    | nil => cases same
    | cons following tail =>
      have parts := List.cons.inj same
      have observed := congrArg filesystemEvent? parts.1
      have fields : (head.1, some head.2) = (following.1, some following.2) := Option.some.inj observed
      have header : head = following := by
        apply Prod.ext
        · exact congrArg (fun pair : Filesystem.Request × Option Filesystem.Reply => pair.1) fields
        · exact Option.some.inj (congrArg (fun pair : Filesystem.Request × Option Filesystem.Reply => pair.2) fields)
      rw [header, ih parts.2]

theorem chunks_filesystem_raw (logical : List (Filesystem.Request × Filesystem.Reply)) {raw : List Program.Event}
    (chunks : Chunks (logical.map Program.filesystemEvent) raw) :
    ∃ events : List (Filesystem.Request × Filesystem.Reply), raw = events.map Program.filesystemEvent := by
  induction logical generalizing raw with
  | nil => cases chunks; exact ⟨[], rfl⟩
  | cons first rest ih =>
    rcases first with ⟨request, reply⟩
    change Chunks (.returned (.filesystem request) reply :: rest.map Program.filesystemEvent) raw at chunks
    cases chunks with
    | cons effect reply inside logical raw adapter tail =>
      obtain ⟨events, source, insideTrace⟩ := Program.lift_filesystem_source (Filesystem.guardedCall request) adapter
      obtain ⟨remaining, restTrace⟩ := ih tail
      exact ⟨events ++ remaining, by rw [insideTrace, restTrace, List.map_append]⟩

theorem effect_returns_singleton {β : Type} (effect : Effect β) {events : List Program.Event} {value : β}
    (source : Program.Returns (Program.effect effect) events value) : events = [.returned effect value] := by
  cases source with
  | call _ _ reply tail value rest => cases rest; rfl

-- §FS-host-boundary.ownership: An unguarded UID/stat observation remains the exact same raw
-- event, at the raw position obtained by splitting the real preceding chunks.
theorem chunks_selected_identity {logical raw : List Program.Event} (source : Chunks logical raw)
    {β : Type} {effect : Effect β} {reply : β} {before after : List Program.Event}
    (trace : logical = before ++ .returned effect reply :: after)
    (identity : lowerEffect effect = Program.effect effect) :
    ∃ first last, Chunks before first ∧ Chunks after last ∧
      raw = first ++ .returned effect reply :: last := by
  have indexed : Chunks (before ++ .returned effect reply :: after) raw := trace ▸ source
  obtain ⟨first, tail, leading, remaining, whole⟩ := chunks_split before _ indexed
  cases remaining with
  | cons _ _ inside logical raw adapter rest =>
    have singleton : inside = [.returned effect reply] :=
      effect_returns_singleton effect (identity ▸ adapter)
    exact ⟨first, raw, leading, rest, by simpa only [singleton, List.singleton_append] using whole⟩

theorem stat_identity (fd : UInt64) :
    lowerEffect (.filesystem { op := .stat, first := fd }) =
      Program.effect (.filesystem { op := .stat, first := fd }) := rfl

theorem euid_identity : lowerEffect (.filesystem { op := .euid }) =
    Program.effect (.filesystem { op := .euid }) := rfl

def IdentityEvent : Program.Event → Prop
  | .returned effect _ => lowerEffect effect = Program.effect effect
  | .lost _ => False

theorem chunks_identity {logical raw : List Program.Event} (source : Chunks logical raw)
    (identity : ∀ event ∈ logical, IdentityEvent event) : raw = logical := by
  induction source with
  | nil => rfl
  | cons effect reply inside logical raw adapter rest ih =>
    have unchanged := identity (.returned effect reply) (by simp)
    change lowerEffect effect = Program.effect effect at unchanged
    have single := effect_returns_singleton effect (unchanged ▸ adapter)
    rw [single, ih (by intro event member; exact identity event (by simp [member]))]
    rfl

theorem random_identity (request : Filesystem.Request) (kind : request.op = .random) :
    lowerEffect (.filesystem request) = Program.effect (.filesystem request) := by
  cases request with
  | mk operation first second third left right => cases kind; rfl

end LeanCage.Host.PrimitiveFilesystem
