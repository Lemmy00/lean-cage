import MetadataOrigins
import CallerRecording

set_option autoImplicit false

namespace LeanCage.Entry.CallerPhysical

-- §AR-metadata.primitives: These labels identify the maintained three-function metadata ABI.
def metadataCode : LeanCageM3.Metadata.Op → Nat
  | .open => 0
  | .read => 1
  | .close => 2

-- §AR-entry.caller.origin: A metadata return samples its own occurrence in one fixed journal.
-- This is a one-operation runtime law; source ordering and safe control are proved consumers.
structure MetadataRecording {platform : MetadataFrame.PrimitiveContract}
    (runtime : MetadataOriginContract platform) (owner child : ProcessIdentity)
    (returned : Nat → Context → ReturnOrigin → State → LeanCageM3.Metadata.Request →
      LeanCageM3.Metadata.Reply → Context → State → Prop) (start : Nat) (ticks : List Tick) where
  occurrence : ∀ position before origin state request reply after result,
    returned position before origin state request reply after result →
    ∃ offset tick, position = start + offset ∧ TickAt ticks offset tick ∧
      tick.before = before ∧ tick.after = after ∧
      (origin = .kernel → (control owner child before).nonSubstituting → tick.action = .native) ∧
      NativeTable child state tick ∧
      runtime.returns (control owner child before) origin state request reply result ∧
      (origin = .kernel → (control owner child before).nonSubstituting →
        ∀ actor fd bytes lost, tick.socket ≠ .wrote actor fd bytes lost)
  label : ∀ position before origin state request reply after result,
    returned position before origin state request reply after result →
    ∀ offset tick, position = start + offset → TickAt ticks offset tick →
      tick.primitive = some ⟨.metadata, metadataCode request.op, decide (origin = .kernel)⟩

-- §FS-entry.provenance: The operation's supplied ordinal determines its physical caller control.
theorem metadata_recorded_snapshot {platform : MetadataFrame.PrimitiveContract}
    {runtime : MetadataOriginContract platform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {history : List Nat} {start namespaceId : Nat}
    {cgroup : Option Nat} {ticks : List Tick} {final before after : Context}
    {position : Nat} {origin : ReturnOrigin} {state result : State}
    {request : LeanCageM3.Metadata.Request} {reply : LeanCageM3.Metadata.Reply}
    {returned : Nat → Context → ReturnOrigin → State → LeanCageM3.Metadata.Request →
      LeanCageM3.Metadata.Reply → Context → State → Prop}
    (journal : Journal mayTrace owner child history (born namespaceId cgroup) ticks final)
    (recording : MetadataRecording runtime owner child returned start ticks)
    (operation : returned position before origin state request reply after result) :
    At start ticks position before ∧ CallerMetadata runtime owner child history state request reply result := by
  obtain ⟨offset, tick, ordinal, selected, initial, _, _, _, actual, _⟩ :=
    recording.occurrence _ _ _ _ _ _ _ _ operation
  have sampled : At start ticks position before :=
    ⟨offset, tick, ordinal, selected, initial.symm⟩
  exact ⟨sampled, control owner child before, origin, actual, journal_snapshot journal sampled⟩

end LeanCage.Entry.CallerPhysical
