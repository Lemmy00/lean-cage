import ProcessProvenance

namespace LeanCage.Entry

-- §FS-entry.provenance: The C source proof produces this exact list predicate.
def CallerRequestsAllowed : List Nat → Prop
  | [] => True
  | request :: rest => NonSubstitutingRequest request ∧ CallerRequestsAllowed rest

theorem caller_request_allowed {history : List Nat} (checked : CallerRequestsAllowed history)
    {request : Nat} (member : request ∈ history) : NonSubstitutingRequest request := by
  induction history with
  | nil => contradiction
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst request
      exact checked.1
    · exact ih checked.2 later

-- §AR-entry.caller: A snapshot names the fork-owned identities and the actual issued source log.
inductive CallerControlUse (owner child : ProcessIdentity) (history : List Nat) :
    TracerControl → Prop
  | detached : CallerControlUse owner child history .detached
  | owned (issued : List Nat) (source : ∀ request ∈ issued, request ∈ history)
      (options : UInt64) (configured : TracerOptionsAllowed options.toNat) :
      CallerControlUse owner child history (.exclusive owner child issued options)

theorem caller_control_non_substituting {owner child : ProcessIdentity} {history : List Nat}
    {control : TracerControl} (checked : CallerRequestsAllowed history)
    (snapshot : CallerControlUse owner child history control) : control.nonSubstituting := by
  cases snapshot with
  | detached => trivial
  | owned issued source options configured =>
    refine ⟨?_, configured⟩
    intro request member
    exact caller_request_allowed checked (source request member)

-- §FS-entry.provenance: Every returned operation carries its own same-run caller snapshot.
-- The Linux mapping produces these snapshots from physical ownership and source history.
inductive CallerReturns {fs : Filesystem} {platform : PrimitiveContract fs}
    (runtime : OriginContract platform) (owner child : ProcessIdentity) (history : List Nat) :
    State → List (Request × Reply) → List TracerControl → State → Prop
  | nil (state : State) : CallerReturns runtime owner child history state [] [] state
  | cons (control : TracerControl) (origin : ReturnOrigin) (request : Request) (reply : Reply)
      {before middle after : State} {trace : List (Request × Reply)}
      {controls : List TracerControl}
      (effect : runtime.returns control origin before request reply middle)
      (snapshot : CallerControlUse owner child history control)
      (rest : CallerReturns runtime owner child history middle trace controls after) :
      CallerReturns runtime owner child history before ((request, reply) :: trace)
        (control :: controls) after

theorem caller_returns_erased {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {owner child : ProcessIdentity} {history : List Nat}
    {initial final : State} {trace : List (Request × Reply)} {controls : List TracerControl}
    (run : CallerReturns runtime owner child history initial trace controls final) :
    TracedReturns runtime initial trace controls final := by
  induction run with
  | nil state => exact .nil state
  | cons control origin request reply effect _ _ ih =>
    exact .cons control origin request reply effect ih

theorem caller_returns_non_substituting {fs : Filesystem} {platform : PrimitiveContract fs}
    {runtime : OriginContract platform} {owner child : ProcessIdentity} {history : List Nat}
    {initial final : State} {trace : List (Request × Reply)} {controls : List TracerControl}
    (checked : CallerRequestsAllowed history)
    (run : CallerReturns runtime owner child history initial trace controls final) :
    ∀ control ∈ controls, control.nonSubstituting := by
  induction run with
  | nil state => simp
  | cons control origin request reply effect snapshot rest ih =>
    intro selected member
    rcases List.mem_cons.mp member with same | later
    · subst selected
      exact caller_control_non_substituting checked snapshot
    · exact ih selected later

-- §AR-entry.caller: Operation tags distinguish inheritance, native calls and runtime start.
-- Native prctl/raw-syscall requests retain their actual unsigned words.
def CallerLineageAllowed (kind request : Nat) : Prop :=
  kind = 0 ∨ kind = 1 ∨ kind = 4 ∨ kind = 5 ∨ kind = 7 ∨ kind = 8 ∨
    kind = 9 ∨ kind = 10 ∨ kind = 11 ∨ kind = 12 ∨
    (kind = 2 ∧ request < 4294967296 ∧ request ≠ 22) ∨
    (kind = 3 ∧ request < 1073741824 ∧ request ≠ 101 ∧ request ≠ 157 ∧ request ≠ 317) ∨
    (kind = 6 ∧ (request = 7 ∨ request = 16898)) ∨
    (kind = 13 ∧ TracerOptionsAllowed request)

-- §AR-entry.caller.origin: Keep the exact source operation labels at the strict interface.
structure LineageLabel where
  kind : Nat
  request : Nat

def CallerLabelsAllowed : List LineageLabel → Prop
  | [] => True
  | label :: rest => CallerLineageAllowed label.kind label.request ∧ CallerLabelsAllowed rest

-- §FS-entry.provenance: This contract describes one Linux/runtime operation at a time.
-- The operation relation supplies the actual task identities.
-- These lists track installed programs; State.filters tracks active enforcement.

-- Tags 0–4: fork, exec, prctl, canonical x86-64 syscall, pinned runtime start.
-- Tags 5–9: C step, CONT/GETSIGINFO, I/O, signal, descriptor.
-- Tags 10–13: clock, decimal, bounded memory, SETOPTIONS with its actual options word.
structure CallerLineageContract where
  booted : ProcessIdentity → List ByteArray → Prop
  step : Nat → Nat → ProcessIdentity → ProcessIdentity → List ByteArray → List ByteArray → Prop
  linuxBoot : ∀ task filters, booted task filters → filters = []
  primitiveFrame : ∀ kind request parent child before after,
    step kind request parent child before after → CallerLineageAllowed kind request → after = before
  primitiveIdentity : ∀ kind request parent child before after,
    step kind request parent child before after → kind = 0 ∨ child = parent

inductive CallerLineage (runtime : CallerLineageContract) : ProcessIdentity → List ByteArray → Prop
  | boot {task : ProcessIdentity} {filters : List ByteArray} (started : runtime.booted task filters) :
      CallerLineage runtime task filters
  | step {parent child : ProcessIdentity} {before after : List ByteArray} (kind request : Nat)
      (prior : CallerLineage runtime parent before)
      (operation : runtime.step kind request parent child before after)
      (source : CallerLineageAllowed kind request) : CallerLineage runtime child after

theorem caller_lineage_clean {runtime : CallerLineageContract} {task : ProcessIdentity}
    {filters : List ByteArray} (lineage : CallerLineage runtime task filters) : filters = [] := by
  induction lineage with
  | boot started => exact runtime.linuxBoot _ _ started
  | step kind request prior operation source ih =>
    exact (runtime.primitiveFrame kind request _ _ _ _ operation source).trans ih

-- §FS-entry.provenance: Source history, physical snapshots and lineage establish return origin.
theorem production_kernel_from_caller {fs : Filesystem} (platform : PrimitiveContract fs)
    (runtime : OriginContract platform) (lineageRuntime : CallerLineageContract)
    (args : List String) (initial current : State) (owner child : ProcessIdentity) (history : List Nat)
    {trace : List (Request × Reply)} {request : Request} {controls : List TracerControl}
    (control : Startup.AtExec (Worker.startup false args) trace request)
    (source : CallerRequestsAllowed history)
    (lineage : CallerLineage lineageRuntime child initial.filters)
    (effects : CallerReturns runtime owner child history initial trace controls current) :
    KernelTrace platform initial trace current := by
  exact production_kernel_from_clean platform runtime args initial current control
    (caller_lineage_clean lineage) (caller_returns_non_substituting source effects)
    (caller_returns_erased effects)

end LeanCage.Entry
