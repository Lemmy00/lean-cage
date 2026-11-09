import MetadataFrame
import CallerProvenance

set_option autoImplicit false

namespace LeanCage.Entry

-- §AR-metadata.control: Both maintained callers execute this exact bounded program.
theorem worker_inspect_shared (path : String) (limit : Nat) :
    Worker.inspect path limit = LeanCageM3.Metadata.inspect path limit := rfl

theorem public_readBounded_shared (path : System.FilePath) (limit : Nat) :
    LeanCageM3.readBounded path limit = LeanCageM3.Metadata.readBounded path limit := rfl

-- §AR-metadata.frame: Native effects are interleaved with actual executions of inspect's shared
-- program.
inductive Startup.AtExecState {α : Type}
    (metadata : State → LeanCageM3.Metadata.Request → LeanCageM3.Metadata.Reply → State → Prop)
    (native : State → Request → Reply → State → Prop) :
    Startup α → State → List (Request × Reply) → Request → State → Prop
  | ready (request : Request) (next : Reply → Startup α) (state : State) (exec : request.op = .exec) :
      AtExecState metadata native (.call request next) state [] request state
  | returned (request : Request) (next : Reply → Startup α) (reply : Reply)
      {before middle after : State} {trace : List (Request × Reply)} {target : Request}
      (operation : native before request reply middle)
      (rest : AtExecState metadata native (next reply) middle trace target after) :
      AtExecState metadata native (.call request next) before ((request, reply) :: trace) target after
  | inspected (path : String) (limit : Nat) (next : Except IO.Error ByteArray → Startup α)
      (result : LeanCageM3.Metadata.Result)
      {before middle after : State} {trace : List (Request × Reply)} {target : Request}
      {reads : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)}
      (operation : LeanCageM3.Metadata.Runs metadata
        (LeanCageM3.Metadata.bounded path limit) before reads result middle)
      (rest : AtExecState metadata native (next (LeanCageM3.Metadata.inspection result)) middle trace target after) :
      AtExecState metadata native (.inspect path limit next) before trace target after

-- §FS-entry.runtime: Returning startup errors also retain their actual metadata executions.
inductive Startup.ReturnsState {α : Type}
    (metadata : State → LeanCageM3.Metadata.Request → LeanCageM3.Metadata.Reply → State → Prop)
    (native : State → Request → Reply → State → Prop) :
    Startup α → State → List (Request × Reply) → α → State → Prop
  | pure (value : α) (state : State) : ReturnsState metadata native (.pure value) state [] value state
  | returned (request : Request) (next : Reply → Startup α) (reply : Reply)
      {before middle after : State} {trace : List (Request × Reply)} {value : α}
      (operation : native before request reply middle)
      (rest : ReturnsState metadata native (next reply) middle trace value after) :
      ReturnsState metadata native (.call request next) before ((request, reply) :: trace) value after
  | inspected (path : String) (limit : Nat) (next : Except IO.Error ByteArray → Startup α)
      (result : LeanCageM3.Metadata.Result)
      {before middle after : State} {trace : List (Request × Reply)} {value : α}
      {reads : List (LeanCageM3.Metadata.Request × LeanCageM3.Metadata.Reply)}
      (operation : LeanCageM3.Metadata.Runs metadata
        (LeanCageM3.Metadata.bounded path limit) before reads result middle)
      (rest : ReturnsState metadata native (next (LeanCageM3.Metadata.inspection result)) middle trace value after) :
      ReturnsState metadata native (.inspect path limit next) before trace value after

inductive NativeTrace (native : State → Request → Reply → State → Prop) :
    State → List (Request × Reply) → State → Prop
  | nil (state : State) : NativeTrace native state [] state
  | cons (request : Request) (reply : Reply) {before middle after : State} {trace : List (Request × Reply)}
      (operation : native before request reply middle) (rest : NativeTrace native middle trace after) :
      NativeTrace native before ((request, reply) :: trace) after

-- §AR-entry.caller: The existing control theorem is an erasure of the same stateful startup run.
theorem startup_state_control {α : Type} {metadata : State → LeanCageM3.Metadata.Request → LeanCageM3.Metadata.Reply → State → Prop}
    {native : State → Request → Reply → State → Prop} {program : Startup α}
    {before after : State} {trace : List (Request × Reply)} {request : Request}
    (run : Startup.AtExecState metadata native program before trace request after) :
    Startup.AtExec program trace request := by
  induction run with
  | ready request next state exec => exact .ready request next exec
  | returned request next reply operation rest ih => exact .returned request next reply ih
  | inspected path limit next result operation rest ih =>
    exact .inspected path limit next (LeanCageM3.Metadata.inspection result) ih

-- §AR-metadata.frame: Both inspections restore the actual post-exec state before admission begins.
theorem startup_state_native_effects {α : Type} {metadata : MetadataFrame.PrimitiveContract}
    {native : State → Request → Reply → State → Prop} {program : Startup α}
    {before after : State} {trace : List (Request × Reply)} {request : Request}
    (run : Startup.AtExecState metadata.returned native program before trace request after) :
    NativeTrace native before trace after := by
  induction run with
  | ready request next state exec => exact .nil state
  | returned request next reply operation rest ih => exact .cons request reply operation ih
  | inspected path limit next result operation rest ih =>
    have restored := MetadataFrame.bounded_frame metadata path limit operation
    simpa only [restored] using ih

-- §FS-entry.provenance: Each native call retains its own real caller snapshot and return origin.
def CallerNative {fs : Filesystem} {platform : PrimitiveContract fs}
    (runtime : OriginContract platform) (owner child : ProcessIdentity) (history : List Nat)
    (before : State) (request : Request) (reply : Reply) (after : State) : Prop :=
  ∃ control origin, runtime.returns control origin before request reply after ∧
    CallerControlUse owner child history control

theorem native_trace_caller_returns {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {owner child : ProcessIdentity} {history : List Nat}
    {before after : State} {trace : List (Request × Reply)}
    (execution : NativeTrace (CallerNative runtime owner child history) before trace after) :
    ∃ controls, CallerReturns runtime owner child history before trace controls after := by
  induction execution with
  | nil state => exact ⟨[], .nil state⟩
  | cons request reply operation rest ih =>
    obtain ⟨control, origin, operation, snapshot⟩ := operation
    obtain ⟨controls, last⟩ := ih
    exact ⟨control :: controls, .cons control origin request reply operation snapshot last⟩

theorem startup_state_caller_returns {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {owner child : ProcessIdentity} {history : List Nat}
    {metadata : MetadataFrame.PrimitiveContract} {args : List String}
    {before after : State} {trace : List (Request × Reply)} {request : Request}
    (run : Startup.AtExecState metadata.returned (CallerNative runtime owner child history)
      (Worker.startup false args) before trace request after) :
    ∃ controls, CallerReturns runtime owner child history before trace controls after :=
  native_trace_caller_returns (startup_state_native_effects run)

-- §AR-entry.caller: This consumer starts at the worker exec snapshot, before metadata reads.
theorem production_kernel_from_stateful_startup {fs : Filesystem} (platform : PrimitiveContract fs)
    (runtime : OriginContract platform) (lineageRuntime : CallerLineageContract)
    (metadata : MetadataFrame.PrimitiveContract) (args : List String) (before after : State)
    (owner child : ProcessIdentity) (history : List Nat) {trace : List (Request × Reply)} {request : Request}
    (run : Startup.AtExecState metadata.returned (CallerNative runtime owner child history)
      (Worker.startup false args) before trace request after)
    (source : CallerRequestsAllowed history) (lineage : CallerLineage lineageRuntime child before.filters) :
    KernelTrace platform before trace after := by
  obtain ⟨controls, effects⟩ := startup_state_caller_returns run
  exact production_kernel_from_caller platform runtime lineageRuntime args before after owner child history
    (startup_state_control run) source lineage effects

end LeanCage.Entry
