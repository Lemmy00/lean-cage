import MetadataRecording
import ChannelExecution

set_option autoImplicit false

namespace LeanCage.Entry.CallerPhysical

-- §AR-entry.caller.origin: Keep physical time and task context with each interpreter state.
structure Point where
  position : Nat
  context : Context
  state : State

def Point.advance (before : Point) (context : Context) (state : State) : Point :=
  ⟨before.position + 1, context, state⟩

-- §AR-entry.effects: This describes one metadata primitive, including intercepted replies.
structure MetadataContract {platform : MetadataFrame.PrimitiveContract}
    (runtime : MetadataOriginContract platform) (mayTrace : ProcessIdentity → Prop)
    (owner child : ProcessIdentity) where
  returned : Nat → Context → ReturnOrigin → State → LeanCageM3.Metadata.Request →
    LeanCageM3.Metadata.Reply → Context → State → Prop
  live : ∀ position before origin state request reply after result,
    returned position before origin state request reply after result → before.childAlive = true
  projection : ∀ position before origin state request reply after result,
    returned position before origin state request reply after result →
    (control owner child before).nonSubstituting → origin = .kernel →
    Step mayTrace owner child before .native after
-- §AR-entry.caller.origin: A supervisor operation is located in the same immutable journal.
structure SupervisorRecording {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} (supervisor : SupervisorContract mayTrace owner child)
    (start : Nat) (ticks : List Tick) where
  occurrence : ∀ position before state action after result,
    supervisor.returned position before state action after result →
    ∃ offset tick, position = start + offset ∧ TickAt ticks offset tick ∧
      tick.before = before ∧ tick.after = after ∧ tick.action = action
  writeOrigin : ∀ position before state action after result,
    supervisor.returned position before state action after result →
    ∀ offset tick, position = start + offset → TickAt ticks offset tick →
      ∀ actor fd bytes lost, tick.socket = .wrote actor fd bytes lost →
        (∃ reference, tick.source = some reference) ∨ (actor ≠ owner ∧ actor ≠ child)

-- §FS-entry.image: One successful exec retains the physical task and its resource scope.
structure ImageContract (execution : ExecContract) (owner child : ProcessIdentity)
    (start : Nat) (ticks : List Tick) where
  replaced : Nat → Context → State → Request → ProcessIdentity → Context → Image → Prop
  effect : ∀ position before state request task after image,
    replaced position before state request task after image →
    execution.replaced (control owner child before) state request image
  occurrence : ∀ position before state request task after image,
    replaced position before state request task after image → At start ticks position before
  identity : ∀ position before state request task after image,
    replaced position before state request task after image → task = child
  live : ∀ position before state request task after image,
    replaced position before state request task after image → before.childAlive = true
  scope : ∀ position before state request task after image,
    replaced position before state request task after image →
    after.namespaceId = before.namespaceId ∧ after.cgroup = before.cgroup
  noSocketWrite : ∀ position before state request task after image,
    replaced position before state request task after image →
    (control owner child before).nonSubstituting →
    ∀ offset tick, position = start + offset → TickAt ticks offset tick →
      ∀ actor fd bytes lost, tick.socket ≠ .wrote actor fd bytes lost

theorem journal_tick_source {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity}
    {history : List Nat} {before after : Context} {ticks : List Tick}
    (journal : Journal mayTrace owner child history before ticks after)
    {offset : Nat} {tick : Tick} (selected : TickAt ticks offset tick) :
    SourceUse mayTrace history tick.before tick.action := by
  induction journal generalizing offset with
  | done => cases offset <;> contradiction
  | next current source operation rest ih =>
    cases offset with
    | zero => cases selected; exact source
    | succ offset => exact ih selected

theorem supervisor_recorded_source {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {history : List Nat} {start : Nat} {ticks : List Tick} {initial final before after : Context}
    {position : Nat} {state result : State} {action : Action}
    (journal : Journal mayTrace owner child history initial ticks final)
    (recording : SupervisorRecording supervisor start ticks)
    (operation : supervisor.returned position before state action after result) :
    SourceUse mayTrace history before action := by
  obtain ⟨offset, tick, _, selected, first, _, actual⟩ :=
    recording.occurrence _ _ _ _ _ _ operation
  have source := journal_tick_source journal selected
  simpa only [first, actual] using source

-- §AR-entry.caller.origin: Parent actions may occur between any two metadata operations.
inductive MetadataExecution {platform : MetadataFrame.PrimitiveContract}
    {runtime : MetadataOriginContract platform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} (supervisor : SupervisorContract mayTrace owner child)
    (metadata : MetadataContract runtime mayTrace owner child) :
    {α : Type} → LeanCageM3.Metadata.Program α → Point →
      List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply) → α → Point → Prop
  | pure {α : Type} (value : α) (point : Point) :
      MetadataExecution supervisor metadata (.pure value) point [] value point
  | supervised {α : Type} {program : LeanCageM3.Metadata.Program α}
      {before final : Point} {middle : Context} {changed : State} {action : Action}
      {trace : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)} {value : α}
      (operation : supervisor.returned before.position before.context before.state action middle changed)
      (rest : MetadataExecution supervisor metadata program (before.advance middle changed) trace value final) :
      MetadataExecution supervisor metadata program before trace value final
  | returned {α : Type} (request : LeanCageM3.Metadata.Request)
      (next : LeanCageM3.Metadata.Reply → LeanCageM3.Metadata.Program α)
      (reply : LeanCageM3.Metadata.Reply) (origin : ReturnOrigin)
      {before final : Point} {middle : Context} {changed : State}
      {trace : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)} {value : α}
      (operation : metadata.returned before.position before.context origin before.state request reply middle changed)
      (rest : MetadataExecution supervisor metadata (next reply) (before.advance middle changed) trace value final) :
      MetadataExecution supervisor metadata (.call request next) before ((request, reply) :: trace) value final

-- §AR-entry.acceptance: These are the shared worker program's actual ordered primitive calls.
inductive StartupExecution {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {metadataPlatform : MetadataFrame.PrimitiveContract}
    {metadataRuntime : MetadataOriginContract metadataPlatform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} (supervisor : SupervisorContract mayTrace owner child)
    (native : NativeContract runtime mayTrace owner child)
    (metadata : MetadataContract metadataRuntime mayTrace owner child) :
    {α : Type} → Startup α → Point → List (Request × Reply) → Request → Point → Prop
  | ready {α : Type} (request : Request) (next : Reply → Startup α) (point : Point)
      (exec : request.op = .exec) :
      StartupExecution supervisor native metadata (.call request next) point [] request point
  | supervised {α : Type} {program : Startup α} {before final : Point}
      {middle : Context} {changed : State} {action : Action}
      {trace : List (Request × Reply)} {target : Request}
      (operation : supervisor.returned before.position before.context before.state action middle changed)
      (rest : StartupExecution supervisor native metadata program (before.advance middle changed) trace target final) :
      StartupExecution supervisor native metadata program before trace target final
  | returned {α : Type} (request : Request) (next : Reply → Startup α) (reply : Reply)
      (origin : ReturnOrigin) {before final : Point} {middle : Context} {changed : State}
      {trace : List (Request × Reply)} {target : Request}
      (operation : native.returned before.position before.context origin before.state request reply middle changed)
      (rest : StartupExecution supervisor native metadata (next reply) (before.advance middle changed) trace target final) :
      StartupExecution supervisor native metadata (.call request next) before ((request, reply) :: trace) target final
  | inspected {α : Type} (path : String) (limit : Nat) (next : Except IO.Error ByteArray → Startup α)
      (result : LeanCageM3.Metadata.Result) {before middle final : Point}
      {reads : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)}
      {trace : List (Request × Reply)} {target : Request}
      (operation : MetadataExecution supervisor metadata (LeanCageM3.Metadata.bounded path limit)
        before reads result middle)
      (rest : StartupExecution supervisor native metadata (next (LeanCageM3.Metadata.inspection result))
        middle trace target final) :
      StartupExecution supervisor native metadata (.inspect path limit next) before trace target final

theorem metadata_execution_erase {metadataPlatform : MetadataFrame.PrimitiveContract}
    {metadataRuntime : MetadataOriginContract metadataPlatform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {metadata : MetadataContract metadataRuntime mayTrace owner child}
    {history : List Nat} {start namespaceId : Nat} {cgroup : Option Nat}
    {ticks : List Tick} {context : Context} {α : Type} {program : LeanCageM3.Metadata.Program α}
    {before final : Point} {trace : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)} {value : α}
    (journal : Journal mayTrace owner child history (born namespaceId cgroup) ticks context)
    (supervisorRecording : SupervisorRecording supervisor start ticks)
    (metadataRecording : MetadataRecording metadataRuntime owner child metadata.returned start ticks)
    (run : MetadataExecution supervisor metadata program before trace value final) :
    LeanCageM3.Metadata.Runs (CallerMetadata metadataRuntime owner child history)
      program before.state trace value final.state := by
  induction run with
  | pure value point => exact .pure value point.state
  | supervised operation rest ih =>
    have source := supervisor_recorded_source journal supervisorRecording operation
    have frame := supervisor.frame _ _ _ _ _ _ operation (source_frame_allowed source)
    simpa only [Point.advance, frame] using ih
  | returned request next reply origin operation rest ih =>
    have recorded := (metadata_recorded_snapshot journal metadataRecording operation).2
    exact .call request next reply recorded ih

theorem startup_execution_erase {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {metadataPlatform : MetadataFrame.PrimitiveContract}
    {metadataRuntime : MetadataOriginContract metadataPlatform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {native : NativeContract runtime mayTrace owner child}
    {metadata : MetadataContract metadataRuntime mayTrace owner child}
    {history : List Nat} {start namespaceId : Nat} {cgroup : Option Nat}
    {ticks : List Tick} {context : Context} {α : Type} {program : Startup α}
    {before final : Point} {trace : List (Request × Reply)} {target : Request}
    (journal : Journal mayTrace owner child history (born namespaceId cgroup) ticks context)
    (supervisorRecording : SupervisorRecording supervisor start ticks)
    (nativeRecording : NativeRecording native start ticks)
    (metadataRecording : MetadataRecording metadataRuntime owner child metadata.returned start ticks)
    (run : StartupExecution supervisor native metadata program before trace target final) :
    Startup.AtExecState (CallerMetadata metadataRuntime owner child history)
      (CallerNative runtime owner child history) program before.state trace target final.state := by
  induction run with
  | ready request next point exec => exact .ready request next point.state exec
  | supervised operation rest ih =>
    have source := supervisor_recorded_source journal supervisorRecording operation
    have frame := supervisor.frame _ _ _ _ _ _ operation (source_frame_allowed source)
    simpa only [Point.advance, frame] using ih
  | returned request next reply origin operation rest ih =>
    have snapshot := (native_recorded_snapshot journal nativeRecording operation).2
    exact .returned request next reply
      ⟨_, origin, native.effect _ _ _ _ _ _ _ _ operation, snapshot⟩ ih
  | inspected path limit next result operation rest ih =>
    exact .inspected path limit next result
      (metadata_execution_erase journal supervisorRecording metadataRecording operation) ih

theorem admission_execution {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {metadataPlatform : MetadataFrame.PrimitiveContract}
    {metadataRuntime : MetadataOriginContract metadataPlatform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {native : NativeContract runtime mayTrace owner child}
    {metadata : MetadataContract metadataRuntime mayTrace owner child}
    {history : List Nat} {start : Nat} {ticks : List Tick} {initial context : Context}
    {α : Type} {program : Startup α} {before final : Point}
    {trace : List (Request × Reply)} {target : Request}
    (journal : Journal mayTrace owner child history initial ticks context)
    (recording : SupervisorRecording supervisor start ticks)
    (run : StartupExecution supervisor native metadata program before trace target final)
    (script : Script α) (selected : program = Startup.admission script) :
    ∃ actions controls,
      Execution supervisor native history before.position before.context before.state
        actions trace controls final.context final.state ∧
      final.position = before.position + actions.length := by
  induction run generalizing script with
  | ready request next point exec =>
    cases script with
    | pure value => cases selected
    | call operation rest =>
      cases selected
      exact ⟨[], [], .done _ _ _, rfl⟩
  | supervised operation rest ih =>
    obtain ⟨actions, controls, remaining, position⟩ := ih script selected
    refine ⟨_ :: actions, controls,
      .supervisor (supervisor_recorded_source journal recording operation) operation remaining, ?_⟩
    simp only [Point.advance] at position
    simp only [List.length_cons]; omega
  | returned request next reply origin operation rest ih =>
    cases script with
    | pure value => cases selected
    | call selectedRequest selectedNext =>
      cases selected
      obtain ⟨actions, controls, remaining, position⟩ := ih (selectedNext reply) rfl
      refine ⟨.native :: actions, _ :: controls, .native origin request reply operation remaining, ?_⟩
      simp only [Point.advance] at position
      simp only [List.length_cons]; omega
  | inspected => cases script <;> cases selected

private theorem metadata_phase_view {α : Type} {program : Startup α}
    (phase : Startup.MetadataPhase program) :
    (∃ script, program = Startup.admission script) ∨
      (∃ path limit next, program = Startup.inspect path limit next ∧
        ∀ reply, Startup.MetadataPhase (next reply)) := by
  cases phase with
  | admission script => exact Or.inl ⟨script, rfl⟩
  | inspected path limit next rest => exact Or.inr ⟨path, limit, next, rfl, rest⟩

theorem metadata_execution_monotone {platform : MetadataFrame.PrimitiveContract}
    {runtime : MetadataOriginContract platform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {metadata : MetadataContract runtime mayTrace owner child} {α : Type}
    {program : LeanCageM3.Metadata.Program α} {before final : Point}
    {trace : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)} {value : α}
    (run : MetadataExecution supervisor metadata program before trace value final) :
    before.position ≤ final.position := by
  induction run with
  | pure => exact Nat.le_refl _
  | supervised _ _ ih => simp only [Point.advance] at ih; omega
  | returned _ _ _ _ _ _ ih => simp only [Point.advance] at ih; omega

-- §AR-entry.caller.origin: Metadata restores the initial state before the first body operation.
theorem startup_execution_body {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {metadataPlatform : MetadataFrame.PrimitiveContract}
    {metadataRuntime : MetadataOriginContract metadataPlatform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {native : NativeContract runtime mayTrace owner child}
    {metadata : MetadataContract metadataRuntime mayTrace owner child}
    {history : List Nat} {start namespaceId : Nat} {cgroup : Option Nat}
    {ticks : List Tick} {context : Context} {α : Type} {program : Startup α}
    {before final : Point} {trace : List (Request × Reply)} {target : Request}
    (journal : Journal mayTrace owner child history (born namespaceId cgroup) ticks context)
    (supervisorRecording : SupervisorRecording supervisor start ticks)
    (metadataRecording : MetadataRecording metadataRuntime owner child metadata.returned start ticks)
    (source : CallerRequestsAllowed history)
    (run : StartupExecution supervisor native metadata program before trace target final)
    (phase : Startup.MetadataPhase program) (clean : before.state.filters = []) :
    ∃ body : Point, ∃ actions controls, body.state = before.state ∧
      Execution supervisor native history body.position body.context body.state
        actions trace controls final.context final.state ∧
      final.position = body.position + actions.length ∧ before.position ≤ body.position := by
  induction run with
  | ready request next point exec =>
    rcases metadata_phase_view phase with ⟨script, selected⟩ | ⟨_, _, _, impossible, _⟩
    ·
      obtain ⟨actions, controls, actual, position⟩ := admission_execution (metadata := metadata) journal supervisorRecording
        (.ready request next point exec) script selected
      exact ⟨point, actions, controls, rfl, actual, position, Nat.le_refl _⟩
    · cases impossible
  | supervised operation rest ih =>
    have allowed := supervisor_recorded_source journal supervisorRecording operation
    have frame := supervisor.frame _ _ _ _ _ _ operation (source_frame_allowed allowed)
    obtain ⟨body, actions, controls, same, actual, position, bound⟩ := ih phase (by simpa [Point.advance, frame] using clean)
    exact ⟨body, actions, controls, same.trans frame, actual, position, by simp only [Point.advance] at bound; omega⟩
  | returned request next reply origin operation rest ih =>
    rcases metadata_phase_view phase with ⟨script, selected⟩ | ⟨_, _, _, impossible, _⟩
    ·
      obtain ⟨actions, controls, actual, position⟩ := admission_execution (metadata := metadata) journal supervisorRecording
        (.returned request next reply origin operation rest) script selected
      exact ⟨_, actions, controls, rfl, actual, position, Nat.le_refl _⟩
    · cases impossible
  | inspected path limit next result operation rest ih =>
    rcases metadata_phase_view phase with ⟨script, impossible⟩ | ⟨_, _, _, selected, later⟩
    · cases script <;> cases impossible
    · cases selected
      have erased := metadata_execution_erase journal supervisorRecording metadataRecording operation
      have frame := (bounded_metadata_from_caller path limit erased source clean).2
      obtain ⟨body, actions, controls, same, actual, position, bound⟩ :=
        ih (later (LeanCageM3.Metadata.inspection result)) (frame ▸ clean)
      exact ⟨body, actions, controls, same.trans frame, actual, position,
        Nat.le_trans (metadata_execution_monotone operation) bound⟩

theorem execution_initial_good {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {native : NativeContract runtime mayTrace owner child} {history : List Nat}
    {start namespaceId position : Nat} {cgroup : Option Nat} {ticks : List Tick}
    {context before after : Context} {initial final : State}
    {actions : List Action} {trace : List (Request × Reply)} {controls : List TracerControl}
    (journal : Journal mayTrace owner child history (born namespaceId cgroup) ticks context)
    (supervisorRecording : SupervisorRecording supervisor start ticks)
    (nativeRecording : NativeRecording native start ticks)
    (run : Execution supervisor native history position before initial actions trace controls after final)
    (nonempty : trace ≠ []) : Good owner history before := by
  cases run with
  | done => exact False.elim (nonempty rfl)
  | supervisor source operation rest =>
    obtain ⟨offset, tick, _, selected, first, _, _⟩ :=
      supervisorRecording.occurrence _ _ _ _ _ _ operation
    have good := journal_member_good (Or.inl rfl) journal (tickAt_getElem selected)
    simpa only [first] using good
  | native origin request reply operation rest =>
    obtain ⟨offset, tick, _, selected, first, _, _, _, _⟩ :=
      nativeRecording.occurrence _ _ _ _ _ _ _ _ operation
    have good := journal_member_good (Or.inl rfl) journal (tickAt_getElem selected)
    simpa only [first] using good

private theorem accepted_trace_no_write {commands : List Command} {trace : List (Request × Reply)}
    (accepted : Accepted commands trace) (guards : ∀ command ∈ commands, GuardSound command) :
    ∀ pair ∈ trace, pair.1.op ≠ .write := by
  induction accepted with
  | nil => simp
  | cons command reply checked rest ih =>
    intro pair present
    rcases List.mem_cons.mp present with first | later
    · cases first
      have success := (guards command (by simp)).2 reply checked
      intro writing
      change command.request.op = .write at writing
      simp only [successfulReturn, writing] at success
      contradiction
    · exact ih (by intro selected member; exact guards selected (by simp [member])) pair later

-- §FS-entry.release: Produce the exact release read from the maintained worker's whole startup.
theorem startup_execution_release {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {metadataPlatform : MetadataFrame.PrimitiveContract}
    {metadataRuntime : MetadataOriginContract metadataPlatform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {native : NativeContract runtime mayTrace owner child}
    {metadata : MetadataContract metadataRuntime mayTrace owner child}
    {history : List Nat} {start namespaceId : Nat} {cgroup : Option Nat}
    {ticks : List Tick} {context : Context} {before final : Point}
    {trace : List (Request × Reply)} {target : Request} (args : List String)
    (journal : Journal mayTrace owner child history (born namespaceId cgroup) ticks context)
    (supervisorRecording : SupervisorRecording supervisor start ticks)
    (nativeRecording : NativeRecording native start ticks)
    (metadataRecording : MetadataRecording metadataRuntime owner child metadata.returned start ticks)
    (source : CallerRequestsAllowed history) (clean : before.state.filters = [])
    (run : StartupExecution supervisor native metadata (Worker.startup false args) before trace target final) :
    ∃ p, Worker.parse args = some p ∧ p.fault = "normal" ∧
      ∃ ordinal selected state next changed leading trailing actions controls,
        trace = leading ++ ((releaseCommand p).request, (1, (⟨#[165]⟩ : ByteArray))) :: trailing ∧
        native.returned ordinal selected .kernel state (releaseCommand p).request
          (1, (⟨#[165]⟩ : ByteArray)) next changed ∧
        Execution supervisor native history (ordinal + 1) next changed actions trailing controls
          final.context final.state ∧ state.handles = before.state.handles ∧
        ordinal < final.position ∧ (∀ pair ∈ trailing, pair.1.op ≠ .write) := by
  have erased := startup_execution_erase journal supervisorRecording nativeRecording metadataRecording run
  obtain ⟨p, parsed, production, atExec⟩ := startup_at_exec false args (startup_state_control erased)
  have normal := Worker.production_mode p production
  obtain ⟨body, actions, controls, same, actual, position, _⟩ := startup_execution_body journal supervisorRecording
    metadataRecording source run (worker_metadata_phase false args) clean
  obtain ⟨_, accepted, _, _⟩ := admission_at_exec p atExec
  have releaseMember : releaseCommand p ∈ setup p := by
    rw [setup_release_cut p normal]
    simp
  obtain ⟨reply, present, checked⟩ := accepted_command_reply accepted (releaseCommand p) releaseMember
  have nonempty : trace ≠ [] := by intro empty; simp [empty] at present
  have good := execution_initial_good journal supervisorRecording nativeRecording actual nonempty
  obtain ⟨leading, trailing, reply, first, remaining, firstControls, restControls, ordinal,
    selected, state, next, changed, traceCut, actionCut, _, ordinalEq, _, operation, suffix, handles,
    returned, bytes, _⟩ := actual_release_read p normal atExec source good (by simpa [same] using clean) actual
  have value : reply = (1, (⟨#[165]⟩ : ByteArray)) := Prod.ext returned bytes
  subst reply
  refine ⟨p, parsed, normal, ordinal, selected, state, next, changed, leading, trailing,
    remaining, restControls, traceCut, operation, suffix, ?_, ?_, ?_⟩
  · exact handles.trans (congrArg State.handles same)
  · rw [actionCut, List.length_append, List.length_cons] at position
    omega
  · intro pair member
    apply accepted_trace_no_write accepted (setup_guards_sound p normal) pair
    rw [traceCut]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ member)

-- §AR-entry.caller.origin: The same physical table receipt supplies an actual entry handle.
theorem native_table_binding {child : ProcessIdentity} {state : State} {tick : Tick}
    {fd : UInt32} {object : Nat} {flag : Bool}
    (table : NativeTable child state tick) (fits : fd.toNat ≤ 2147483647)
    (bound : TickBinding tick (taskKey child) fd.toNat object flag) :
    ∃ handle, state.handles fd = some handle ∧ handle.object = object ∧ handle.cloexec = flag := by
  have objectTable := (table fd fits).1
  have flags := (table fd fits).2
  cases present : state.handles fd with
  | none => simp only [present, Option.map_none] at objectTable; rw [bound.1] at objectTable; cases objectTable
  | some handle =>
    rw [present] at objectTable flags
    simp only [Option.map_some, Option.getD_some] at objectTable flags
    exact ⟨handle, rfl, Option.some.inj (objectTable.symm.trans bound.1), flags.symm.trans bound.2⟩

-- §FS-entry.image: Every cgroup change is an explicit placement, including native writes.
theorem step_observed_scope {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity}
    {history : List Nat} {before after : Context} {action : Action}
    (good : Good owner history before)
    (operation : Step mayTrace owner child before action after)
    (source : SourceUse mayTrace history before action)
    (notPlacement : ∀ group, action ≠ .placement group) :
    after.namespaceId = before.namespaceId ∧ after.cgroup = before.cgroup := by
  cases operation with
  | nativeFrame after tracer options issued parent alive space group => exact ⟨space, group⟩
  | nativeUnsafe after unprotected => exact False.elim (unprotected (good_context_safe good))
  | placement group => exact False.elim (notPlacement group rfl)
  | other after actor request value permission opcode =>
    exact False.elim (opcode (source permission).2.1)
  | _ => exact ⟨rfl, rfl⟩

private theorem step_placement_scope {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {before after : Context} {group : Nat}
    (operation : Step mayTrace owner child before (.placement group) after) :
    after.cgroup = some group ∧ after.namespaceId = before.namespaceId := by
  cases operation
  exact ⟨rfl, rfl⟩

private theorem step_namespace {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity}
    {history : List Nat} {before after : Context} {action : Action}
    (good : Good owner history before)
    (operation : Step mayTrace owner child before action after)
    (source : SourceUse mayTrace history before action) : after.namespaceId = before.namespaceId := by
  cases operation with
  | nativeFrame after tracer options issued parent alive space group => exact space
  | nativeUnsafe after unprotected => exact False.elim (unprotected (good_context_safe good))
  | other after actor request value permission opcode =>
    exact False.elim (opcode (source permission).2.1)
  | _ => rfl

private theorem no_placement_tail {start cutoff limit : Nat} {current : Tick} {ticks : List Tick}
    (stable : NoPlacementBefore start (current :: ticks) cutoff limit) :
    NoPlacementBefore (start + 1) ticks cutoff limit := by
  intro offset tick reached below selected group
  exact stable (offset + 1) tick (by omega) (by omega) selected group

theorem journal_prefix_scope {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity}
    {history : List Nat} {start cutoff limit : Nat} {before after : Context} {ticks : List Tick}
    (journal : Journal mayTrace owner child history before ticks after)
    (good : Good owner history before)
    (stable : NoPlacementBefore start ticks cutoff limit) (reached : cutoff ≤ start)
    {offset : Nat} {tick : Tick} (selected : TickAt ticks offset tick) (bounded : start + offset ≤ limit) :
    tick.before.namespaceId = before.namespaceId ∧ tick.before.cgroup = before.cgroup := by
  induction journal generalizing start offset with
  | done => cases offset <;> contradiction
  | next current source operation rest ih =>
    cases offset with
    | zero => cases selected; exact ⟨rfl, rfl⟩
    | succ offset =>
      have later := ih (start := start + 1) (step_good good source operation)
        (no_placement_tail stable) (by omega) selected (by omega)
      have first := step_observed_scope good operation source (stable 0 current (by omega) (by omega) rfl)
      exact ⟨later.1.trans first.1, later.2.trans first.2⟩

-- §FS-entry.release: Placement and entry are positions in the same physical journal.
theorem journal_after_placement_scope {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {history : List Nat} {start : Nat}
    {before after : Context} {ticks : List Tick} {placed entered : Tick}
    {placementOffset entryOffset group : Nat}
    (journal : Journal mayTrace owner child history before ticks after)
    (good : Good owner history before)
    (placement : TickAt ticks placementOffset placed) (assigned : placed.action = .placement group)
    (entry : TickAt ticks entryOffset entered) (ordered : placementOffset < entryOffset)
    (stable : NoPlacementBefore start ticks (start + placementOffset + 1) (start + entryOffset)) :
    entered.before.cgroup = some group ∧ entered.before.namespaceId = placed.before.namespaceId := by
  induction journal generalizing start placementOffset entryOffset with
  | done => cases placementOffset <;> contradiction
  | next current source operation rest ih =>
    cases placementOffset with
    | zero =>
      cases placement
      cases entryOffset with
      | zero => omega
      | succ entryOffset =>
        have first : placed.after.cgroup = some group ∧
            placed.after.namespaceId = placed.before.namespaceId := by
          rw [assigned] at operation
          exact step_placement_scope operation
        have later := journal_prefix_scope (start := start + 1) rest
          (step_good good source operation) (no_placement_tail stable) (by omega) entry (by omega)
        exact ⟨later.2.trans first.1, later.1.trans first.2⟩
    | succ placementOffset =>
      cases entryOffset with
      | zero => omega
      | succ entryOffset =>
        apply ih (start := start + 1) (step_good good source operation) placement entry (by omega)
        intro offset tick reached below selected group
        exact stable (offset + 1) tick (by omega) (by omega) selected group

-- §FS-entry.image: Local admission cannot change the prepared namespace identity.
theorem journal_namespace {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity}
    {history : List Nat} {before after : Context} {ticks : List Tick}
    (journal : Journal mayTrace owner child history before ticks after)
    (good : Good owner history before)
    {offset : Nat} {tick : Tick} (selected : TickAt ticks offset tick) :
    tick.before.namespaceId = before.namespaceId := by
  induction journal generalizing offset with
  | done => cases offset <;> contradiction
  | next current source operation rest ih =>
    cases offset with
    | zero => cases selected; rfl
    | succ offset =>
      have first := step_namespace good operation source
      exact (ih (step_good good source operation) selected).trans first

-- §FS-entry.image: The actual physical checkpoint and successful image use one fixed history.
theorem journal_after_observed_scope {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {history : List Nat} {start : Nat}
    {before after : Context} {ticks : List Tick} {observed entered : Tick}
    {observedOffset entryOffset group : Nat}
    (journal : Journal mayTrace owner child history before ticks after)
    (good : Good owner history before)
    (checkpoint : TickAt ticks observedOffset observed) (assigned : observed.after.cgroup = some group)
    (entry : TickAt ticks entryOffset entered) (ordered : observedOffset < entryOffset)
    (stable : NoPlacementBefore start ticks (start + observedOffset + 1) (start + entryOffset)) :
    entered.before.cgroup = some group := by
  induction journal generalizing start observedOffset entryOffset with
  | done => cases observedOffset <;> contradiction
  | next current source operation rest ih =>
    cases observedOffset with
    | zero =>
      cases checkpoint
      cases entryOffset with
      | zero => omega
      | succ entryOffset =>
        have later := journal_prefix_scope (start := start + 1) rest
          (step_good good source operation) (no_placement_tail stable) (by omega) entry (by omega)
        exact later.2.trans assigned
    | succ observedOffset =>
      cases entryOffset with
      | zero => omega
      | succ entryOffset =>
        apply ih (start := start + 1) (step_good good source operation) checkpoint entry (by omega)
        intro offset tick reached below selected group
        exact stable (offset + 1) tick (by omega) (by omega) selected group

-- §FS-entry.image: The physical admission receipt may be the successful captured-handle close.
theorem recorded_image_observed_scope {mayTrace : ProcessIdentity → Prop}
    {owner child task : ProcessIdentity} {history : List Nat} {start namespaceId : Nat}
    {cgroup : Option Nat} {ticks : List Tick} {last before after : Context}
    {execution : ExecContract} (runtime : ImageContract execution owner child start ticks)
    {position : Nat} {state : State} {request : Request} {image : Image}
    {checkpoint : Tick} {observedOffset group : Nat}
    (journal : Journal mayTrace owner child history (born namespaceId cgroup) ticks last)
    (selected : TickAt ticks observedOffset checkpoint) (assigned : checkpoint.after.cgroup = some group)
    (ordered : start + observedOffset < position)
    (stable : NoPlacementBefore start ticks (start + observedOffset + 1) position)
    (replaced : runtime.replaced position before state request task after image) :
    after.cgroup = some group ∧ after.namespaceId = namespaceId := by
  obtain ⟨offset, tick, ordinal, actual, context⟩ := runtime.occurrence _ _ _ _ _ _ _ replaced
  rw [ordinal] at stable
  have groupScope := journal_after_observed_scope journal (Or.inl rfl) selected assigned actual (by omega) stable
  have namespaceScope := journal_namespace journal (Or.inl rfl) actual
  have inherited := runtime.scope _ _ _ _ _ _ _ replaced
  refine ⟨inherited.2.trans ?_, inherited.1.trans ?_⟩
  · simpa only [context] using groupScope
  · simpa only [context, born] using namespaceScope

theorem recorded_image_scope {mayTrace : ProcessIdentity → Prop}
    {owner child task : ProcessIdentity} {history : List Nat} {start namespaceId : Nat}
    {cgroup : Option Nat} {ticks : List Tick} {last before after : Context}
    {position placementOffset group : Nat} {placed : Tick} {state : State}
    {request : Request} {image : Image} {execution : ExecContract}
    (runtime : ImageContract execution owner child start ticks)
    (journal : Journal mayTrace owner child history (born namespaceId cgroup) ticks last)
    (placement : TickAt ticks placementOffset placed) (assigned : placed.action = .placement group)
    (ordered : start + placementOffset < position)
    (stable : NoPlacementBefore start ticks (start + placementOffset + 1) position)
    (replaced : runtime.replaced position before state request task after image) :
    after.cgroup = some group ∧ after.namespaceId = namespaceId := by
  obtain ⟨offset, tick, ordinal, selected, context⟩ := runtime.occurrence _ _ _ _ _ _ _ replaced
  rw [ordinal] at stable
  have placedScope := journal_after_placement_scope journal (Or.inl rfl) placement assigned selected (by omega) stable
  have namespaceScope := journal_namespace journal (Or.inl rfl) selected
  have inherited := runtime.scope _ _ _ _ _ _ _ replaced
  refine ⟨inherited.2.trans ?_, inherited.1.trans ?_⟩
  · simpa only [context] using placedScope.1
  · simpa only [context, born] using namespaceScope

-- §FS-entry.image: Every write in a successful worker interval belongs to supervision.
def SupervisorAt {mayTrace : ProcessIdentity → Prop} {owner child : ProcessIdentity}
    (supervisor : SupervisorContract mayTrace owner child) (position : Nat) : Prop :=
  ∃ before state action after result, supervisor.returned position before state action after result

def SocketQuietAt (start : Nat) (ticks : List Tick) (position : Nat) : Prop :=
  ∀ offset tick, position = start + offset → TickAt ticks offset tick →
    ∀ actor fd bytes lost, tick.socket ≠ .wrote actor fd bytes lost

private theorem selected_tick_unique {start position left right : Nat} {ticks : List Tick}
    {first second : Tick} (firstPosition : position = start + left)
    (secondPosition : position = start + right) (selectedFirst : TickAt ticks left first)
    (selectedSecond : TickAt ticks right second) : first = second := by
  have equal : left = right := by omega
  subst right
  have firstGet := tickAt_getElem selectedFirst
  have secondGet := tickAt_getElem selectedSecond
  exact Option.some.inj (firstGet.symm.trans secondGet)

-- The proof follows the actual stateful execution, including every parent interleaving.
theorem execution_supervisor_owns_writes {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {native : NativeContract runtime mayTrace owner child} {history : List Nat}
    {start position : Nat} {ticks : List Tick} {before after : Context} {initial final : State}
    {actions : List Action} {trace : List (Request × Reply)} {controls : List TracerControl}
    (recording : NativeRecording native start ticks)
    (run : Execution supervisor native history position before initial actions trace controls after final)
    (commands : List Command) (accepted : Accepted commands trace)
    (guards : ∀ command ∈ commands, GuardSound command) (order : FilterAtEnd commands)
    (clean : commands = [] ∨ initial.filters = []) (good : Good owner history before) :
    ∀ ordinal, position ≤ ordinal → ordinal < position + actions.length →
      SupervisorAt supervisor ordinal ∨ SocketQuietAt start ticks ordinal := by
  induction run generalizing commands with
  | done => intro ordinal lower upper; simp only [List.length_nil, Nat.add_zero] at upper; omega
  | @supervisor position before middle after state changed result actions trace controls
      action source operation rest ih =>
    intro ordinal lower upper
    by_cases first : ordinal = position
    · subst ordinal; exact Or.inl ⟨_, _, _, _, _, operation⟩
    · have frame := supervisor.frame _ _ _ _ _ _ operation (source_frame_allowed source)
      apply ih commands accepted guards order (by simpa only [frame] using clean)
        (step_good good source (supervisor.projection _ _ _ _ _ _ operation)) ordinal (by omega)
      simp only [List.length_cons] at upper; omega
  | @native position before middle after initial changed final actions trace controls
      origin request reply operation rest ih =>
    cases commands with
    | nil => cases accepted
    | cons command commands =>
      cases accepted with
      | cons command reply checked remaining =>
        have initialClean : initial.filters = [] := by
          rcases clean with impossible | clean
          · cases impossible
          · exact clean
        have safe := good_non_substituting (child := child) good
        have actual := native.effect _ _ _ _ _ _ _ _ operation
        have genuine := runtime.unmediated _ _ _ _ _ _ actual safe initialClean
        have returned := runtime.erases _ _ _ _ _ _ actual safe
        subst origin
        have sound := guards command (by simp)
        have nonwrite : command.request.op ≠ .write := by
          have success := sound.2 reply checked
          intro writing
          simp only [successfulReturn, writing] at success
          contradiction
        intro ordinal lower upper
        by_cases first : ordinal = position
        · subst ordinal
          obtain ⟨offset, tick, positionEq, selected, _, _, _, _, socket⟩ :=
            recording.occurrence _ _ _ _ _ _ _ _ operation
          right
          intro actualOffset actualTick actualPosition actualSelected actor fd bytes lost writing
          have same := selected_tick_unique positionEq actualPosition selected actualSelected
          subst actualTick
          exact nonwrite (socket.wrote safe rfl actor fd bytes lost writing).1
        · have nextClean : commands = [] ∨ changed.filters = [] := by
            cases commands with
            | nil => exact Or.inl rfl
            | cons next commands =>
              have nonfilter : command.request.op ≠ .filter := by
                rcases order.1 with impossible | notFilter
                · cases impossible
                · exact notFilter
              have changedState := platform.successful _ _ _ _ returned sound.1 (sound.2 reply checked)
              right
              rw [changedState, advance_filters_nonfilter fs command.request initial _ nonfilter, initialClean]
          apply ih commands remaining (by
            intro selected member; exact guards selected (by simp [member])) order.2 nextClean
            (native_good good operation) ordinal (by omega)
          simp only [List.length_cons] at upper; omega

-- §AR-metadata.frame: Read-only metadata operations keep their original occurrence and origin.
theorem metadata_supervisor_owns_writes {platform : MetadataFrame.PrimitiveContract}
    {runtime : MetadataOriginContract platform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {metadata : MetadataContract runtime mayTrace owner child} {history : List Nat}
    {start namespaceId : Nat} {cgroup : Option Nat} {ticks : List Tick} {context : Context}
    {α : Type} {program : LeanCageM3.Metadata.Program α} {before final : Point}
    {trace : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)} {value : α}
    (journal : Journal mayTrace owner child history (born namespaceId cgroup) ticks context)
    (supervisorRecording : SupervisorRecording supervisor start ticks)
    (recording : MetadataRecording runtime owner child metadata.returned start ticks)
    (run : MetadataExecution supervisor metadata program before trace value final)
    (clean : before.state.filters = [])
    (shapes : ∀ pair ∈ trace, MetadataOrigins.RequestShape pair.1) :
    ∀ ordinal, before.position ≤ ordinal → ordinal < final.position →
      SupervisorAt supervisor ordinal ∨ SocketQuietAt start ticks ordinal := by
  induction run with
  | pure => intro ordinal lower upper; omega
  | @supervised program before final middle changed action trace value operation rest ih =>
    intro ordinal lower upper
    by_cases first : ordinal = before.position
    · subst ordinal; exact Or.inl ⟨_, _, _, _, _, operation⟩
    · have source := supervisor_recorded_source journal supervisorRecording operation
      have frame := supervisor.frame _ _ _ _ _ _ operation (source_frame_allowed source)
      apply ih (by simpa only [Point.advance, frame] using clean) shapes ordinal
        (by simp only [Point.advance]; omega) upper
  | @returned request next reply origin before final middle changed trace value operation rest ih =>
    obtain ⟨offset, tick, positionEq, selected, initial, _, _, _, actual, quiet⟩ :=
      recording.occurrence _ _ _ _ _ _ _ _ operation
    have observed := journal_member_good (Or.inl rfl) journal (tickAt_getElem selected)
    have good : Good owner history before.context := by simpa only [initial] using observed
    have safe := good_non_substituting (child := child) good
    have genuine := runtime.unmediated _ _ _ _ _ _ actual safe clean
    have kernel := runtime.erases _ _ _ _ _ _ actual safe genuine
    have sameFilters := MetadataOrigins.kernel_filters platform (shapes (request, reply) (by simp)) kernel
    intro ordinal lower upper
    by_cases first : ordinal = before.position
    · subst ordinal
      right
      intro actualOffset actualTick actualPosition actualSelected
      have same := selected_tick_unique positionEq actualPosition selected actualSelected
      subst actualTick
      exact quiet genuine safe
    · apply ih (by simpa only [Point.advance] using sameFilters.trans clean)
        (by intro pair member; exact shapes pair (by simp [member])) ordinal
        (by simp only [Point.advance]; omega) upper

private theorem execution_initial_good_actions {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {native : NativeContract runtime mayTrace owner child} {history : List Nat}
    {start namespaceId position : Nat} {cgroup : Option Nat} {ticks : List Tick}
    {context before after : Context} {initial final : State}
    {actions : List Action} {trace : List (Request × Reply)} {controls : List TracerControl}
    (journal : Journal mayTrace owner child history (born namespaceId cgroup) ticks context)
    (supervisorRecording : SupervisorRecording supervisor start ticks)
    (nativeRecording : NativeRecording native start ticks)
    (run : Execution supervisor native history position before initial actions trace controls after final)
    (nonempty : actions ≠ []) : Good owner history before := by
  cases run with
  | done => exact False.elim (nonempty rfl)
  | supervisor source operation rest =>
    obtain ⟨offset, tick, _, selected, first, _, _⟩ :=
      supervisorRecording.occurrence _ _ _ _ _ _ operation
    have good := journal_member_good (Or.inl rfl) journal (tickAt_getElem selected)
    simpa only [first] using good
  | native origin request reply operation rest =>
    obtain ⟨offset, tick, _, selected, first, _, _, _, _⟩ :=
      nativeRecording.occurrence _ _ _ _ _ _ _ _ operation
    have good := journal_member_good (Or.inl rfl) journal (tickAt_getElem selected)
    simpa only [first] using good

private theorem admission_supervisor_owns_writes {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {metadataPlatform : MetadataFrame.PrimitiveContract}
    {metadataRuntime : MetadataOriginContract metadataPlatform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {native : NativeContract runtime mayTrace owner child}
    {metadata : MetadataContract metadataRuntime mayTrace owner child}
    {history : List Nat} {start namespaceId : Nat} {cgroup : Option Nat}
    {ticks : List Tick} {context : Context} {α : Type} {program : Startup α}
    {before final : Point} {trace : List (Request × Reply)} {target : Request}
    (journal : Journal mayTrace owner child history (born namespaceId cgroup) ticks context)
    (supervisorRecording : SupervisorRecording supervisor start ticks)
    (nativeRecording : NativeRecording native start ticks)
    (run : StartupExecution supervisor native metadata program before trace target final)
    (script : Script α) (selected : program = Startup.admission script)
    (commands : List Command) (accepted : Accepted commands trace)
    (guards : ∀ command ∈ commands, GuardSound command) (order : FilterAtEnd commands)
    (clean : before.state.filters = []) :
    ∀ ordinal, before.position ≤ ordinal → ordinal < final.position →
      SupervisorAt supervisor ordinal ∨ SocketQuietAt start ticks ordinal := by
  obtain ⟨actions, controls, execution, duration⟩ :=
    admission_execution journal supervisorRecording run script selected
  intro ordinal lower upper
  have nonempty : actions ≠ [] := by
    intro empty; simp only [empty, List.length_nil, Nat.add_zero] at duration; omega
  have good := execution_initial_good_actions journal supervisorRecording nativeRecording execution nonempty
  exact execution_supervisor_owns_writes nativeRecording execution commands accepted guards order
    (Or.inr clean) good ordinal lower (by omega)

-- §FS-entry.image: This includes actual inspections, native operations and every parent pause.
theorem startup_supervisor_owns_writes {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {metadataPlatform : MetadataFrame.PrimitiveContract}
    {metadataRuntime : MetadataOriginContract metadataPlatform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {native : NativeContract runtime mayTrace owner child}
    {metadata : MetadataContract metadataRuntime mayTrace owner child}
    {history : List Nat} {start namespaceId : Nat} {cgroup : Option Nat}
    {ticks : List Tick} {context : Context} {α : Type} {program : Startup α}
    {before final : Point} {trace : List (Request × Reply)} {target : Request}
    (journal : Journal mayTrace owner child history (born namespaceId cgroup) ticks context)
    (supervisorRecording : SupervisorRecording supervisor start ticks)
    (nativeRecording : NativeRecording native start ticks)
    (metadataRecording : MetadataRecording metadataRuntime owner child metadata.returned start ticks)
    (run : StartupExecution supervisor native metadata program before trace target final)
    (phase : Startup.MetadataPhase program) (source : CallerRequestsAllowed history)
    (commands : List Command) (accepted : Accepted commands trace)
    (guards : ∀ command ∈ commands, GuardSound command) (order : FilterAtEnd commands)
    (clean : before.state.filters = []) :
    ∀ ordinal, before.position ≤ ordinal → ordinal < final.position →
      SupervisorAt supervisor ordinal ∨ SocketQuietAt start ticks ordinal := by
  induction run with
  | ready => intro ordinal lower upper; omega
  | @supervised program before final middle changed action trace target operation rest ih =>
    intro ordinal lower upper
    by_cases first : ordinal = before.position
    · subst ordinal; exact Or.inl ⟨_, _, _, _, _, operation⟩
    · have allowed := supervisor_recorded_source journal supervisorRecording operation
      have frame := supervisor.frame _ _ _ _ _ _ operation (source_frame_allowed allowed)
      apply ih phase accepted (by simpa only [Point.advance, frame] using clean) ordinal
        (by simp only [Point.advance]; omega) upper
  | returned request next reply origin operation rest ih =>
    rcases metadata_phase_view phase with ⟨script, selected⟩ | ⟨_, _, _, impossible, _⟩
    · exact admission_supervisor_owns_writes journal supervisorRecording nativeRecording
        (.returned request next reply origin operation rest) script selected commands accepted guards order clean
    · cases impossible
  | @inspected path limit next result before middle final reads trace target operation rest ih =>
    rcases metadata_phase_view phase with ⟨script, impossible⟩ | ⟨_, _, _, selected, later⟩
    · cases script <;> cases impossible
    · cases selected
      have erased := metadata_execution_erase journal supervisorRecording metadataRecording operation
      have frame := (bounded_metadata_from_caller path limit erased source clean).2
      intro ordinal lower upper
      by_cases first : ordinal < middle.position
      · exact metadata_supervisor_owns_writes journal supervisorRecording metadataRecording operation clean
          (MetadataOrigins.bounded_shapes path limit erased) ordinal lower first
      · exact ih (later (LeanCageM3.Metadata.inspection result)) accepted (frame ▸ clean)
          ordinal (by omega) upper

-- §FS-entry.release: Export only the pure ownership fact about these same worker ticks.
theorem worker_startup_write_origin {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {metadataPlatform : MetadataFrame.PrimitiveContract}
    {metadataRuntime : MetadataOriginContract metadataPlatform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {native : NativeContract runtime mayTrace owner child}
    {metadata : MetadataContract metadataRuntime mayTrace owner child}
    {history : List Nat} {start namespaceId : Nat} {cgroup : Option Nat}
    {ticks : List Tick} {context : Context} {before final : Point}
    {trace : List (Request × Reply)} {target : Request} (args : List String)
    (journal : Journal mayTrace owner child history (born namespaceId cgroup) ticks context)
    (supervisorRecording : SupervisorRecording supervisor start ticks)
    (nativeRecording : NativeRecording native start ticks)
    (metadataRecording : MetadataRecording metadataRuntime owner child metadata.returned start ticks)
    (run : StartupExecution supervisor native metadata (Worker.startup false args) before trace target final)
    (source : CallerRequestsAllowed history) (clean : before.state.filters = []) :
    ∀ offset tick, before.position ≤ start + offset → start + offset < final.position →
      TickAt ticks offset tick → WriteSourceOrExternal owner child tick := by
  have erased := startup_execution_erase journal supervisorRecording nativeRecording metadataRecording run
  obtain ⟨p, _, production, atExec⟩ := startup_at_exec false args (startup_state_control erased)
  have normal := Worker.production_mode p production
  obtain ⟨_, accepted, _, _⟩ := admission_at_exec p atExec
  have writes := startup_supervisor_owns_writes journal supervisorRecording nativeRecording metadataRecording
    run (worker_metadata_phase false args) source (setup p) accepted (setup_guards_sound p normal)
      (setup_filter_at_end p normal) clean
  intro offset tick lower upper selected actor fd bytes lost wrote
  rcases writes (start + offset) lower upper with supervised | quiet
  · obtain ⟨before, state, action, after, result, operation⟩ := supervised
    exact supervisorRecording.writeOrigin _ _ _ _ _ _ operation offset tick rfl selected
      actor fd bytes lost wrote
  · exact False.elim (quiet offset tick rfl selected actor fd bytes lost wrote)

-- §FS-entry.image: Source table proofs and the worker interpreter cover the same interval.
theorem startup_no_cgroup_placement {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {metadataPlatform : MetadataFrame.PrimitiveContract}
    {metadataRuntime : MetadataOriginContract metadataPlatform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {native : NativeContract runtime mayTrace owner child}
    {metadata : MetadataContract metadataRuntime mayTrace owner child}
    {history : List Nat} {start namespaceId cutoff : Nat} {cgroup : Option Nat}
    {ticks : List Tick} {context : Context} {before final : Point}
    {trace : List (Request × Reply)} {target : Request} (args : List String)
    (journal : Journal mayTrace owner child history (born namespaceId cgroup) ticks context)
    (supervisorRecording : SupervisorRecording supervisor start ticks)
    (nativeRecording : NativeRecording native start ticks)
    (metadataRecording : MetadataRecording metadataRuntime owner child metadata.returned start ticks)
    (run : StartupExecution supervisor native metadata (Worker.startup false args) before trace target final)
    (source : CallerRequestsAllowed history) (clean : before.state.filters = [])
    (groups : Nat → Option Nat) (reached : before.position ≤ cutoff)
    (placements : ∀ offset tick, cutoff ≤ start + offset → start + offset < final.position →
      TickAt ticks offset tick → PlacementRecording groups tick)
    (sourceTables : ∀ offset tick, cutoff ≤ start + offset → start + offset < final.position →
      TickAt ticks offset tick → ∀ reference, tick.source = some reference → WriteOutsideCgroup groups tick)
    (otherTables : ∀ offset tick, cutoff ≤ start + offset → start + offset < final.position →
      TickAt ticks offset tick → ∀ actor, actor ≠ owner → actor ≠ child → CgroupAbsent groups tick actor) :
    NoPlacementBefore start ticks cutoff final.position := by
  have writes := worker_startup_write_origin args journal supervisorRecording nativeRecording
    metadataRecording run source clean
  intro offset tick lower upper selected
  apply recorded_write_cannot_place (placements offset tick lower upper selected)
  intro actor fd bytes lost object bounded wrote present
  rcases writes offset tick (by omega) upper selected actor fd bytes lost wrote with
    ⟨reference, actual⟩ | ⟨notOwner, notChild⟩
  · exact sourceTables offset tick lower upper selected reference actual
      actor fd bytes lost object bounded wrote present
  · exact otherTables offset tick lower upper selected actor notOwner notChild fd object bounded present

theorem journal_tick_step {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {history : List Nat} {before after : Context}
    {ticks : List Tick} {offset : Nat} {tick : Tick}
    (journal : Journal mayTrace owner child history before ticks after)
    (selected : TickAt ticks offset tick) : Step mayTrace owner child tick.before tick.action tick.after := by
  induction journal generalizing offset with
  | done => cases offset <;> contradiction
  | next current source operation rest ih =>
    cases offset with
    | zero => cases selected; exact operation
    | succ offset => exact ih selected

private theorem step_request_parent_live {mayTrace : ProcessIdentity → Prop}
    {owner child actor : ProcessIdentity} {history : List Nat} {before after : Context} {request options : Nat}
    (operation : Step mayTrace owner child before (.request actor request options) after)
    (source : SourceUse mayTrace history before (.request actor request options))
    (live : before.parentAlive = true) : after.parentAlive = true := by
  cases operation with
  | other after actor request value permission opcode =>
    exact False.elim (opcode (source permission).2.1)
  | _ => exact live

-- §FS-entry.provenance: Actual CONT linearization retains the live source caller.
theorem journal_request_parent_live {mayTrace : ProcessIdentity → Prop}
    {owner child actor : ProcessIdentity} {history : List Nat} {before after : Context}
    {ticks : List Tick} {offset request options : Nat} {tick : Tick}
    (journal : Journal mayTrace owner child history before ticks after)
    (selected : TickAt ticks offset tick) (action : tick.action = .request actor request options)
    (live : tick.before.parentAlive = true) : tick.after.parentAlive = true := by
  have operation := journal_tick_step journal selected
  have source := journal_tick_source journal selected
  rw [action] at operation source
  exact step_request_parent_live operation source live

private theorem traceMe_changes_tracer {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {before after : Context}
    (operation : Step mayTrace owner child before .traceMe after) :
    before.tracer = none ∧ after.tracer = some owner := by
  cases operation with
  | traceMe untraced parent alive => exact ⟨untraced, rfl⟩

private theorem native_recorded_traceMe {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {native : NativeContract runtime mayTrace owner child}
    {history : List Nat} {start namespaceId position : Nat} {cgroup : Option Nat}
    {ticks : List Tick} {context before after : Context} {state result : State} {reply : Reply}
    (journal : Journal mayTrace owner child history (born namespaceId cgroup) ticks context)
    (recording : NativeRecording native start ticks)
    (operation : native.returned position before .kernel state { op := .traceMe } reply after result)
    (successful : reply.1 = 0) :
    ∃ offset tick, position = start + offset ∧ TickAt ticks offset tick ∧ tick.action = .traceMe := by
  obtain ⟨offset, tick, ordinal, selected, initial, final, action, _, _⟩ :=
    recording.occurrence _ _ _ _ _ _ _ _ operation
  have good := journal_member_good (Or.inl rfl) journal (tickAt_getElem selected)
  have safe : ContextSafe owner before := by simpa only [initial] using good_context_safe good
  have allowed := context_safe_non_substituting (child := child) safe
  have changed : before.tracer = none ∧ after.tracer = some owner := by
    rcases native.projection _ _ _ _ _ _ _ _ operation with ⟨condition, _⟩ | ⟨_, _, _, traced⟩ | ⟨group, condition, _⟩
    · simp only [successful, ne_eq, not_true_eq_false, false_or] at condition
      exact False.elim (condition safe)
    · exact traceMe_changes_tracer traced
    · simp only [reduceCtorEq, false_or] at condition
      exact False.elim (condition allowed)
  refine ⟨offset, tick, ordinal, selected, ?_⟩
  rcases action with frame | ⟨traced, _, _, _⟩ | ⟨group, placed, condition⟩
  · have physical := journal_tick_step journal selected
    rw [frame] at physical
    have identical : tick.after.tracer = tick.before.tracer := by
      cases physical with
      | nativeFrame => assumption
      | nativeUnsafe _ unprotected => exact False.elim (unprotected (good_context_safe good))
    rw [initial, final, changed.1, changed.2] at identical
    contradiction
  · exact traced
  · simp only [reduceCtorEq, false_or] at condition
    exact False.elim (condition (by simpa only [initial] using allowed))

-- §FS-entry.provenance: Extract the genuine TRACEME from the same successful startup.
theorem startup_traceMe_occurrence {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {metadataPlatform : MetadataFrame.PrimitiveContract}
    {metadataRuntime : MetadataOriginContract metadataPlatform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {native : NativeContract runtime mayTrace owner child}
    {metadata : MetadataContract metadataRuntime mayTrace owner child}
    {history : List Nat} {start namespaceId : Nat} {cgroup : Option Nat}
    {ticks : List Tick} {context : Context} {before final : Point}
    {trace : List (Request × Reply)} {target : Request} (args : List String)
    (journal : Journal mayTrace owner child history (born namespaceId cgroup) ticks context)
    (supervisorRecording : SupervisorRecording supervisor start ticks)
    (nativeRecording : NativeRecording native start ticks)
    (metadataRecording : MetadataRecording metadataRuntime owner child metadata.returned start ticks)
    (source : CallerRequestsAllowed history) (clean : before.state.filters = [])
    (run : StartupExecution supervisor native metadata (Worker.startup false args) before trace target final) :
    ∃ offset tick, before.position ≤ start + offset ∧ TickAt ticks offset tick ∧ tick.action = .traceMe := by
  have erased := startup_execution_erase journal supervisorRecording nativeRecording metadataRecording run
  obtain ⟨p, parsed, production, atExec⟩ := startup_at_exec false args (startup_state_control erased)
  have normal := Worker.production_mode p production
  obtain ⟨body, actions, controls, same, actual, position, bodyBound⟩ :=
    startup_execution_body journal supervisorRecording metadataRecording source run
      (worker_metadata_phase false args) clean
  obtain ⟨_, accepted, _, _⟩ := admission_at_exec p atExec
  let command := cmd p 1 { op := .traceMe } (beforeHandles := true)
  have setupCut : setup p = signalSetup p ++ command ::
      cmd p 1 { op := .stop } (beforeHandles := true) :: releaseCommand p :: afterRelease p := by
    rw [setup_release_cut p normal]
    simp only [beforeRelease, command, List.append_assoc, List.cons_append, List.nil_append]
  rw [setupCut] at accepted
  obtain ⟨leading, trailing, traceCut, leadingAccepted, remaining⟩ := accepted_append accepted
  cases remaining with
  | cons selected reply checked tail =>
    obtain ⟨first, rest, firstControls, restControls, ordinal, context, origin, state, next,
      changed, journalCut, controlsCut, ordinalEq, leadingRun, operation, trailingRun⟩ :=
      execution_native_cut actual leading command.request reply _ traceCut
    have nonempty : trace ≠ [] := by
      intro empty
      rw [empty] at traceCut
      simp at traceCut
    have good := execution_initial_good journal supervisorRecording nativeRecording actual nonempty
    have returned := execution_returns good leadingRun
    have guards : ∀ selected ∈ signalSetup p, GuardSound selected := by
      intro selected member
      apply setup_guards_sound p normal selected
      rw [setupCut]
      exact List.mem_append_left _ member
    have operations : ∀ selected ∈ signalSetup p, BeforeReleaseOp selected.request := by
      intro selected member
      apply before_release_operations p selected
      exact List.mem_append_left _ member
    have absent : ∀ selected ∈ signalSetup p, selected.request.op ≠ .filter := by
      intro selected member
      rcases operations selected member with op | op | op | op <;> simp [op]
    have order : FilterAtEnd (signalSetup p) := by
      simpa only [List.append_nil] using filter_at_end_append (signalSetup p) [] absent True.intro
    have kernelPrefix := accepted_kernel_from_clean platform runtime (signalSetup p) leadingAccepted
      guards order (same ▸ clean) (caller_returns_non_substituting source returned.1)
        (caller_returns_erased returned.1)
    have atTraceClean := (accepted_before_release_filters platform leadingAccepted guards operations kernelPrefix).trans
      (by simpa only [same] using clean)
    have genuine := runtime.unmediated _ _ _ _ _ _ (native.effect _ _ _ _ _ _ _ _ operation)
      (caller_control_non_substituting source returned.2) atTraceClean
    subst origin
    have successful : reply.1 = 0 := by
      simpa only [command, cmd, Expected.accepts, beq_iff_eq] using checked
    obtain ⟨offset, tick, ordinalAt, selected, traceMe⟩ :=
      native_recorded_traceMe journal nativeRecording operation successful
    exact ⟨offset, tick, by omega, selected, traceMe⟩

-- §FS-entry.provenance: Tracer detachment after parent death cannot enable another TRACEME.
private def TraceOwnedOrParentDead (owner : ProcessIdentity) (context : Context) : Prop :=
  context.tracer = some owner ∨ context.parentAlive = false

private theorem step_trace_ownership {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {history : List Nat} {before after : Context} {action : Action}
    (good : Good owner history before) (source : SourceUse mayTrace history before action)
    (operation : Step mayTrace owner child before action after)
    (owned : TraceOwnedOrParentDead owner before) : TraceOwnedOrParentDead owner after := by
  cases operation with
  | nativeFrame after tracer options issued parent alive space group =>
    rcases owned with traced | dead
    · exact Or.inl (tracer.trans traced)
    · exact Or.inr (parent.trans dead)
  | nativeUnsafe after unprotected => exact False.elim (unprotected (good_context_safe good))
  | other after actor request value permission opcode =>
    exact False.elim (opcode (source permission).2.1)
  | attach actor request value permission untraced alive opcode =>
    have allowed := (source (Or.inl permission)).2.1
    rcases opcode with rfl | rfl <;> simp [NonSubstitutingRequest] at allowed
  | parentKilled => exact Or.inr rfl
  | parentDetached => exact Or.inr rfl
  | traceMe => exact Or.inl rfl
  | _ => exact owned

private theorem step_owned_has_no_traceMe {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {before after : Context} {action : Action}
    (operation : Step mayTrace owner child before action after)
    (owned : TraceOwnedOrParentDead owner before) : action ≠ .traceMe := by
  cases operation <;> try (intro impossible; cases impossible)
  rcases owned with traced | dead
  · rename_i untraced parent alive
    rw [untraced] at traced; contradiction
  · rename_i untraced parent alive
    rw [dead] at parent; contradiction

private theorem journal_owned_has_no_traceMe {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {history : List Nat} {before after : Context}
    {ticks : List Tick} {offset : Nat} {tick : Tick}
    (journal : Journal mayTrace owner child history before ticks after)
    (good : Good owner history before) (owned : TraceOwnedOrParentDead owner before)
    (selected : TickAt ticks offset tick) (traceMe : tick.action = .traceMe) : False := by
  induction journal generalizing offset tick with
  | done => cases offset <;> contradiction
  | next current source operation rest ih =>
    cases offset with
    | zero =>
      have excluded := step_owned_has_no_traceMe operation owned
      cases selected
      exact excluded traceMe
    | succ offset =>
      exact ih (step_good good source operation) (step_trace_ownership good source operation owned)
        selected traceMe

-- §FS-entry.provenance: The actual worker TRACEME must precede any owned tracer observation.
theorem journal_traceMe_precedes_owned {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {history : List Nat} {before after : Context}
    {ticks : List Tick} {traceOffset ownedOffset : Nat} {traced observed : Tick}
    (journal : Journal mayTrace owner child history before ticks after)
    (good : Good owner history before)
    (traceOccurrence : TickAt ticks traceOffset traced) (traceMe : traced.action = .traceMe)
    (ownedOccurrence : TickAt ticks ownedOffset observed) (owned : observed.before.tracer = some owner) :
    traceOffset < ownedOffset := by
  induction journal generalizing traceOffset ownedOffset traced observed with
  | done => cases traceOffset <;> contradiction
  | next current source operation rest ih =>
    cases ownedOffset with
    | zero =>
      cases ownedOccurrence
      exact False.elim (journal_owned_has_no_traceMe (.next _ source operation rest) good
        (Or.inl owned) traceOccurrence traceMe)
    | succ ownedOffset =>
      cases traceOffset with
      | zero => omega
      | succ traceOffset =>
        exact Nat.succ_lt_succ (ih (step_good good source operation) traceOccurrence traceMe ownedOccurrence owned)

-- §FS-entry.release: A successful parent observation supplies the worker-start ordering.
theorem startup_precedes_owned_observation {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {metadataPlatform : MetadataFrame.PrimitiveContract}
    {metadataRuntime : MetadataOriginContract metadataPlatform} {mayTrace : ProcessIdentity → Prop}
    {owner child : ProcessIdentity} {supervisor : SupervisorContract mayTrace owner child}
    {native : NativeContract runtime mayTrace owner child}
    {metadata : MetadataContract metadataRuntime mayTrace owner child}
    {history : List Nat} {start namespaceId ownedOffset : Nat} {cgroup : Option Nat}
    {ticks : List Tick} {context : Context} {before final : Point} {observed : Tick}
    {trace : List (Request × Reply)} {target : Request} (args : List String)
    (journal : Journal mayTrace owner child history (born namespaceId cgroup) ticks context)
    (supervisorRecording : SupervisorRecording supervisor start ticks)
    (nativeRecording : NativeRecording native start ticks)
    (metadataRecording : MetadataRecording metadataRuntime owner child metadata.returned start ticks)
    (source : CallerRequestsAllowed history) (clean : before.state.filters = [])
    (run : StartupExecution supervisor native metadata (Worker.startup false args) before trace target final)
    (ownedOccurrence : TickAt ticks ownedOffset observed) (owned : observed.before.tracer = some owner) :
    before.position < start + ownedOffset := by
  obtain ⟨offset, tick, bound, selected, traceMe⟩ := startup_traceMe_occurrence args journal
    supervisorRecording nativeRecording metadataRecording source clean run
  have prior := journal_traceMe_precedes_owned journal (Or.inl rfl) selected traceMe ownedOccurrence owned
  omega

end LeanCage.Entry.CallerPhysical
