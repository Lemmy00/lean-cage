import CallerPhysical

namespace LeanCage.Entry.CallerPhysical

-- §FS-entry.release: One read's bytes and descriptor belong to its actual kernel occurrence.
structure NativeSocket (actualControl : TracerControl) (child : ProcessIdentity) (origin : ReturnOrigin)
    (request : Request) (reply : Reply) (socket : SocketObservation) : Prop where
  read : actualControl.nonSubstituting → request.op = .readByte → origin = .kernel → reply.1 = 1 →
    request.a.toNat ≤ 2147483647 →
      socket = .read child request.a.toNat 1 (reply.2.data.toList.map UInt8.toNat)
  wrote : actualControl.nonSubstituting → origin = .kernel →
    ∀ actor descriptor bytes lost, socket = .wrote actor descriptor bytes lost →
    request.op = .write ∧ origin = .kernel ∧ actor = child ∧
      descriptor = request.a.toUInt32.toNat ∧ bytes.length ≤ request.data.size ∧
      bytes = (request.data.data.toList.map UInt8.toNat).take bytes.length ∧
      (lost = false → reply.1.toNat = bytes.length)

-- §AR-entry.caller.origin: These are the live task's descriptor observations at one position.
def NativeTable (child : ProcessIdentity) (state : State) (tick : Tick) : Prop :=
  ∀ fd : UInt32, fd.toNat ≤ 2147483647 →
    tick.objects (taskKey child) fd.toNat = (state.handles fd).map Handle.object ∧
      tick.cloexec (taskKey child) fd.toNat =
        ((state.handles fd).map Handle.cloexec).getD false

-- §AR-entry.effects: This law maps one returned primitive to one fixed global kernel journal.
-- It supplies no source whitelist, safe control, entry ordering or successful setup claim.
structure NativeRecording {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} (native : NativeContract runtime mayTrace owner child)
    (start : Nat) (ticks : List Tick) where
  occurrence : ∀ position before origin state request reply after result,
    native.returned position before origin state request reply after result →
    ∃ offset tick, position = start + offset ∧ TickAt ticks offset tick ∧
      tick.before = before ∧ tick.after = after ∧
      (tick.action = .native ∨
        (tick.action = .traceMe ∧ request.op = .traceMe ∧ origin = .kernel ∧ reply.1 = 0) ∨
        (∃ group, tick.action = .placement group ∧
          (request.op = .write ∨ origin = .intercepted ∨
            ¬(control owner child before).nonSubstituting))) ∧
      NativeTable child state tick ∧ NativeSocket (control owner child before) child origin request reply tick.socket
  label : ∀ position before origin state request reply after result,
    native.returned position before origin state request reply after result →
    ∀ offset tick, position = start + offset → TickAt ticks offset tick →
      tick.primitive = some ⟨.native, request.op.code.toNat, decide (origin = .kernel)⟩

-- §FS-entry.provenance: Erase an ordinal only after deriving its control from that same journal.
theorem native_recorded_snapshot {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {native : NativeContract runtime mayTrace owner child}
    {history : List Nat} {start namespaceId : Nat} {cgroup : Option Nat}
    {ticks : List Tick} {final before after : Context} {position : Nat}
    {origin : ReturnOrigin} {state result : State} {request : Request} {reply : Reply}
    (journal : Journal mayTrace owner child history (born namespaceId cgroup) ticks final)
    (recording : NativeRecording native start ticks)
    (operation : native.returned position before origin state request reply after result) :
    At start ticks position before ∧ CallerControlUse owner child history (control owner child before) := by
  obtain ⟨offset, tick, ordinal, selected, initial, _, _, _, _⟩ :=
    recording.occurrence _ _ _ _ _ _ _ _ operation
  have sampled : At start ticks position before :=
    ⟨offset, tick, ordinal, selected, initial.symm⟩
  exact ⟨sampled, journal_snapshot journal sampled⟩

-- §FS-entry.release: The queue proof receives the same ordinal, table and actual returned bytes.
theorem native_recorded_read {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {native : NativeContract runtime mayTrace owner child}
    {start : Nat} {ticks : List Tick} {before after : Context} {position : Nat}
    {state result : State} {request : Request} {reply : Reply}
    (recording : NativeRecording native start ticks)
    (operation : native.returned position before .kernel state request reply after result)
    (safe : (control owner child before).nonSubstituting)
    (reading : request.op = .readByte) (successful : reply.1 = 1)
    (descriptor : request.a.toNat ≤ 2147483647) :
    ∃ offset tick, position = start + offset ∧ TickAt ticks offset tick ∧
      tick.before = before ∧ tick.after = after ∧ NativeTable child state tick ∧
      tick.socket = .read child request.a.toNat 1 (reply.2.data.toList.map UInt8.toNat) := by
  obtain ⟨offset, tick, ordinal, selected, initial, final, _, table, socket⟩ :=
    recording.occurrence _ _ _ _ _ _ _ _ operation
  exact ⟨offset, tick, ordinal, selected, initial, final, table,
    socket.read safe reading rfl successful descriptor⟩

-- §FS-entry.provenance: The source labels and runtime effects describe the same ancestry path.
inductive LineageEffects (runtime : CallerLineageContract) :
    ProcessIdentity → List ByteArray → List LineageLabel → ProcessIdentity → List ByteArray → Prop
  | done (task : ProcessIdentity) (installed : List ByteArray) :
      LineageEffects runtime task installed [] task installed
  | next {before middle after : ProcessIdentity} {initial changed final : List ByteArray}
      {rest : List LineageLabel} (label : LineageLabel)
      (operation : runtime.step label.kind label.request before middle initial changed)
      (remaining : LineageEffects runtime middle changed rest after final) :
      LineageEffects runtime before initial (label :: rest) after final

theorem source_effects_lineage {runtime : CallerLineageContract} {before after : ProcessIdentity}
    {initial final : List ByteArray} {labels : List LineageLabel}
    (ancestor : CallerLineage runtime before initial)
    (effects : LineageEffects runtime before initial labels after final)
    (source : CallerLabelsAllowed labels) : CallerLineage runtime after final := by
  induction effects with
  | done => exact ancestor
  | next label operation remaining ih =>
    exact ih (.step label.kind label.request ancestor operation source.1) source.2

-- §FS-entry.provenance: Actual inherited programs are established before inspecting metadata.
theorem source_observed_startup_lineage {runtime : CallerLineageContract}
    {owner child : ProcessIdentity} {before installed : List ByteArray}
    {labels : List LineageLabel} {startup : State}
    (ancestor : CallerLineage runtime owner before)
    (effects : LineageEffects runtime owner before labels child installed)
    (source : CallerLabelsAllowed labels) (observed : StackObservation installed startup) :
    CallerLineage runtime child startup.filters := by
  have lineage := source_effects_lineage ancestor effects source
  have clean := caller_lineage_clean lineage
  have active := observed clean
  simpa only [active, clean] using lineage

end LeanCage.Entry.CallerPhysical
