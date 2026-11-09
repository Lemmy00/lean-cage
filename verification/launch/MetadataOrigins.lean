import MetadataStartup

set_option autoImplicit false

namespace LeanCage.Entry

namespace MetadataOrigins

open LeanCageM3.Metadata

-- §AR-metadata.primitives: These shapes name the exact one-operation adapter arguments.
def RequestShape (request : LeanCageM3.Metadata.Request) : Prop :=
  match request.op with
  | .open => request.fd = 0 ∧ request.amount = 0
  | .read => request.path = ""
  | .close => request.amount = 0 ∧ request.path = "" ∧ request.fd.toNat ≤ 2147483647

theorem read_shape (fd : UInt32) (request : LeanCageM3.Metadata.Request)
    (selected : ReadRequest fd request) : RequestShape request := by
  cases request with
  | mk op actual amount path =>
    rcases selected with ⟨operation, _, pathname, _⟩
    change op = .read at operation
    change path = "" at pathname
    subst op
    exact pathname

theorem bounded_shapes {effect : State → LeanCageM3.Metadata.Request → LeanCageM3.Metadata.Reply → State → Prop}
    (path : String) (limit : Nat) {before after : State}
    {trace : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)} {result : Result}
    (run : Runs effect (bounded path limit) before trace result after) :
    ∀ entry ∈ trace, RequestShape entry.1 := by
  rcases bounded_owned_trace path limit run with empty | ⟨opened, rest, events, disposition⟩
  · subst trace
    simp
  · rw [events]
    intro entry member
    rcases List.mem_cons.mp member with head | member
    · cases head
      exact ⟨rfl, rfl⟩
    · rcases disposition with ⟨_, empty⟩ | ⟨fd, reads, closed, descriptor, remaining, allowed⟩
      · subst rest
        contradiction
      · rw [remaining] at member
        rcases List.mem_append.mp member with reading | closing
        · exact read_shape fd entry.1 (allowed entry reading)
        · obtain rfl := List.mem_singleton.mp closing
          exact ⟨rfl, rfl, openDescriptor_bound opened fd descriptor⟩

theorem kernel_filters (platform : MetadataFrame.PrimitiveContract)
    {before after : State} {request : LeanCageM3.Metadata.Request}
    {reply : LeanCageM3.Metadata.Reply} (shape : RequestShape request)
    (operation : platform.returned before request reply after) : after.filters = before.filters := by
  cases request with
  | mk op fd amount path =>
    cases op with
    | «open» =>
      rcases shape with ⟨rfl, rfl⟩
      have frame := platform.open_return before path reply after operation
      cases descriptor : openDescriptor reply with
      | none =>
        rw [descriptor] at frame
        rw [frame]
      | some fd =>
        rw [descriptor] at frame
        obtain ⟨handle, _, _, _, _, rfl⟩ := frame
        rfl
    | read =>
      change path = "" at shape
      subst path
      rw [platform.read_return before fd amount reply after operation]
    | close =>
      rcases shape with ⟨rfl, rfl, fits⟩
      rw [platform.close_return before fd reply after operation fits]
      rfl

end MetadataOrigins

-- §FS-entry.provenance: Intercepted metadata replies remain possible outside a clean safe context.
structure MetadataOriginContract (platform : MetadataFrame.PrimitiveContract) where
  returns : TracerControl → ReturnOrigin → State → LeanCageM3.Metadata.Request →
    LeanCageM3.Metadata.Reply → State → Prop
  erases : ∀ control origin before request reply after,
    returns control origin before request reply after → control.nonSubstituting →
    origin = .kernel → platform.returned before request reply after
  unmediated : ∀ control origin before request reply after,
    returns control origin before request reply after → control.nonSubstituting →
    before.filters = [] → origin = .kernel

-- §AR-entry.caller.origin: Each metadata effect retains its own actual caller snapshot.
def CallerMetadata {platform : MetadataFrame.PrimitiveContract}
    (runtime : MetadataOriginContract platform) (owner child : ProcessIdentity) (history : List Nat)
    (before : State) (request : LeanCageM3.Metadata.Request) (reply : LeanCageM3.Metadata.Reply)
    (after : State) : Prop :=
  ∃ control origin, runtime.returns control origin before request reply after ∧
    CallerControlUse owner child history control

-- §AR-metadata.frame: Clean filters and the actual caller justify each metadata effect.
theorem metadata_runs_from_caller {platform : MetadataFrame.PrimitiveContract}
    {runtime : MetadataOriginContract platform} {owner child : ProcessIdentity} {history : List Nat}
    {α : Type} {program : LeanCageM3.Metadata.Program α} {before after : State}
    {trace : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)} {result : α}
    (run : LeanCageM3.Metadata.Runs (CallerMetadata runtime owner child history)
      program before trace result after)
    (source : CallerRequestsAllowed history) (clean : before.filters = [])
    (shapes : ∀ entry ∈ trace, MetadataOrigins.RequestShape entry.1) :
    LeanCageM3.Metadata.Runs platform.returned program before trace result after ∧ after.filters = [] := by
  induction run with
  | pure value state => exact ⟨.pure value state, clean⟩
  | call request next reply operation rest ih =>
    obtain ⟨control, origin, actual, snapshot⟩ := operation
    have safe := caller_control_non_substituting source snapshot
    have genuine := runtime.unmediated control origin _ _ _ _ actual safe clean
    have kernel := runtime.erases control origin _ _ _ _ actual safe genuine
    have unchanged := MetadataOrigins.kernel_filters platform (shapes (request, reply) (by simp)) kernel
    obtain ⟨tail, final⟩ := ih (unchanged.trans clean) (by
      intro entry member
      exact shapes entry (by simp [member]))
    exact ⟨.call request next reply kernel tail, final⟩

theorem bounded_metadata_from_caller {platform : MetadataFrame.PrimitiveContract}
    {runtime : MetadataOriginContract platform} {owner child : ProcessIdentity} {history : List Nat}
    (path : String) (limit : Nat) {before after : State}
    {trace : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)}
    {result : LeanCageM3.Metadata.Result}
    (run : LeanCageM3.Metadata.Runs (CallerMetadata runtime owner child history)
      (LeanCageM3.Metadata.bounded path limit) before trace result after)
    (source : CallerRequestsAllowed history) (clean : before.filters = []) :
    LeanCageM3.Metadata.Runs platform.returned (LeanCageM3.Metadata.bounded path limit)
      before trace result after ∧ after = before := by
  have kernel := (metadata_runs_from_caller run source clean
    (MetadataOrigins.bounded_shapes path limit run)).1
  exact ⟨kernel, MetadataFrame.bounded_frame platform path limit kernel⟩

-- §AR-metadata.frame: The executing startup completes inspections before native admission begins.
inductive Startup.MetadataPhase {α : Type} : Startup α → Prop
  | admission (program : Script α) : MetadataPhase (Startup.admission program)
  | inspected (path : String) (limit : Nat) (next : Except IO.Error ByteArray → Startup α)
      (rest : ∀ reply, MetadataPhase (next reply)) : MetadataPhase (.inspect path limit next)

theorem worker_metadata_phase (allowTestModes : Bool) (args : List String) :
    Startup.MetadataPhase (Worker.startup allowTestModes args) := by
  simp only [Worker.startup, Startup.read, bind, Startup.bind, pure]
  constructor
  intro marker
  cases marker with
  | error error => exact .admission (.pure 125)
  | ok marker =>
    by_cases rejected : (marker != "LeanCage-M3-root-VM-v1".toUTF8) = true
    · simp only [rejected, ↓reduceIte]
      exact .admission (.pure 125)
    · simp only [rejected]
      constructor
      intro status
      cases status with
      | error error => exact .admission (.pure 125)
      | ok status =>
        cases decoded : String.fromUTF8? status with
        | none => simp only [decoded]; exact .admission (.pure 125)
        | some status =>
          simp only [decoded]
          by_cases rejected : (!(status.splitOn "\n").contains "Threads:\t1") = true
          · simp only [rejected, ↓reduceIte]
            exact .admission (.pure 125)
          · simp only [rejected]
            cases parsed : Worker.parse args with
            | none => exact .admission (.pure 125)
            | some p =>
              by_cases enabled : Worker.enabled allowTestModes p = true
              · simp only [enabled, ↓reduceIte]
                exact .admission (admission p)
              · simp only [enabled]
                exact .admission (.pure 125)

theorem admission_metadata_irrelevant {α : Type}
    {first second : State → LeanCageM3.Metadata.Request → LeanCageM3.Metadata.Reply → State → Prop}
    {native : State → Request → Reply → State → Prop} (program : Script α)
    {before after : State} {trace : List (Request × Reply)} {request : Request}
    (run : Startup.AtExecState first native (Startup.admission program) before trace request after) :
    Startup.AtExecState second native (Startup.admission program) before trace request after := by
  induction program generalizing before trace with
  | pure value => cases run
  | call current next ih =>
    cases run with
    | ready _ _ _ exec => exact .ready _ _ _ exec
    | returned _ _ reply operation rest => exact .returned _ _ reply operation (ih reply rest)

theorem metadata_phase_from_caller {platform : MetadataFrame.PrimitiveContract}
    {runtime : MetadataOriginContract platform} {owner child : ProcessIdentity} {history : List Nat}
    {native : State → Request → Reply → State → Prop} {α : Type} {program : Startup α}
    (phase : Startup.MetadataPhase program)
    {before after : State} {trace : List (Request × Reply)} {request : Request}
    (run : Startup.AtExecState (CallerMetadata runtime owner child history) native
      program before trace request after)
    (source : CallerRequestsAllowed history) (clean : before.filters = []) :
    Startup.AtExecState platform.returned native program before trace request after := by
  induction phase generalizing before trace with
  | admission program => exact admission_metadata_irrelevant program run
  | inspected path limit next rest ih =>
    cases run with
    | inspected _ _ _ result operation tail =>
      obtain ⟨kernel, restored⟩ := bounded_metadata_from_caller path limit operation source clean
      apply Startup.AtExecState.inspected path limit next result kernel
      exact ih _ tail (by simpa only [restored] using clean)

-- §AR-entry.caller.origin: Provenance is established at each actual inspection and native call.
theorem production_kernel_from_actual_startup {fs : Filesystem} (platform : PrimitiveContract fs)
    (runtime : OriginContract platform) (lineageRuntime : CallerLineageContract)
    (metadata : MetadataFrame.PrimitiveContract) (metadataRuntime : MetadataOriginContract metadata)
    (args : List String) (before after : State) (owner child : ProcessIdentity) (history : List Nat)
    {trace : List (Request × Reply)} {request : Request}
    (run : Startup.AtExecState (CallerMetadata metadataRuntime owner child history)
      (CallerNative runtime owner child history) (Worker.startup false args) before trace request after)
    (source : CallerRequestsAllowed history) (lineage : CallerLineage lineageRuntime child before.filters) :
    KernelTrace platform before trace after := by
  have actual := metadata_phase_from_caller (worker_metadata_phase false args) run source
    (caller_lineage_clean lineage)
  exact production_kernel_from_stateful_startup platform runtime lineageRuntime metadata args before after
    owner child history actual source lineage

end LeanCage.Entry
