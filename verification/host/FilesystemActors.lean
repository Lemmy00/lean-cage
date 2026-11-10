import FilesystemNamespaces
import LeanCageHost.Entrypoint

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.ownership: Actor identities are process-lifetime tokens, not request names.
abbrev ActorId := Nat

inductive Residual {α : Type} : Program α → List Program.Event → Program α → Prop where
  | refl (program : Program α) : Residual program [] program
  | call {β : Type} {effect : Effect β} {next : β → Program α} {reply : β}
      {events : List Program.Event} {after : Program α}
      (tail : Residual (next reply) events after) :
      Residual (.call effect next) (.returned effect reply :: events) after

theorem residual_append {α : Type} {first middle last : Program α}
    {before after : List Program.Event} (initial : Residual first before middle)
    (final : Residual middle after last) : Residual first (before ++ after) last := by
  induction initial with
  | refl => exact final
  | call tail ih => exact .call (ih final)

theorem residual_prefix {α : Type} {first last : Program α} {before after : List Program.Event}
    (initial : Residual first before last) (final : Program.Prefix last after) :
    Program.Prefix first (before ++ after) := by
  induction initial with
  | refl => exact final
  | call tail ih => exact .returned _ _ _ _ (ih final)

structure EngineState where
  references : UInt64 → Option Handle
  closeExec : UInt64 → Bool
  current : Program UInt32
  events : List Program.Event
  running : Bool
  workingDirectory : ObjectId
  directory : Option ObjectId := some workingDirectory

-- §AR-host-boundary.primitives: One actual kernel teardown observation may retire only
-- part of the resources. Completion concerns this engine's resources, not its VM children.
structure EngineRetirement where
  directory : Option ObjectId
  finished : Bool
  status : Option UInt32 := none

-- §AR-host-boundary.primitives: Native teardown keeps every surviving actual reference,
-- including SDK/unowned descriptors. The last CWD identity is history when directory is none.
structure RetirementResources where
  handles : UInt64 → Option Handle
  closeExec : UInt64 → Bool
  directory : Option ObjectId
  lastDirectory : ObjectId

def RetirementResources.project (resources : RetirementResources) (shared : World) : World :=
  { shared with
    handles := resources.handles
    closeOnExec := resources.closeExec
    workingDirectory := resources.lastDirectory }

def EngineState.initialFrom (sourceProgram : Program UInt32) (references : UInt64 → Option Handle) (closeExec : UInt64 → Bool)
    (workingDirectory : ObjectId) : EngineState :=
  ⟨references, closeExec, sourceProgram, [], true, workingDirectory, some workingDirectory⟩

def EngineState.initial (references : UInt64 → Option Handle) (closeExec : UInt64 → Bool)
    (workingDirectory : ObjectId) : EngineState :=
  .initialFrom Entrypoint.run references closeExec workingDirectory

def EngineState.returned {β : Type} (engine : EngineState) (effect : Effect β) (reply : β)
    (next : β → Program UInt32) (after : World) : EngineState :=
  { references := after.handles
    closeExec := after.closeOnExec
    current := next reply
    events := engine.events ++ [.returned effect reply]
    running := true
    workingDirectory := after.workingDirectory
    directory := some after.workingDirectory }

def EngineState.lost {β : Type} (engine : EngineState) (effect : Effect β) (after : World) : EngineState :=
  { engine with
    references := after.handles
    closeExec := after.closeOnExec
    events := engine.events ++ [.lost effect]
    running := false
    workingDirectory := after.workingDirectory
    directory := some after.workingDirectory }

-- §FS-host-boundary.ownership: Retain the old CWD identity only as history after retirement.
-- The optional directory records its actual remaining lifetime at this SAME kernel point.
def EngineState.retired (engine : EngineState) (observation : EngineRetirement) (after : World) : EngineState :=
  { engine with
    references := after.handles
    closeExec := after.closeOnExec
    running := false
    directory := observation.directory }

def EngineSourceFrom (sourceProgram : Program UInt32) (engine : EngineState) : Prop :=
  if engine.running then Residual sourceProgram engine.events engine.current
  else Program.Prefix sourceProgram engine.events

theorem initial_engine_source_for (sourceProgram : Program UInt32) (references : UInt64 → Option Handle) (closeExec : UInt64 → Bool)
    (workingDirectory : ObjectId) :
    EngineSourceFrom sourceProgram (EngineState.initialFrom sourceProgram references closeExec workingDirectory) := Residual.refl _

theorem returned_engine_source_for {β : Type} (engine : EngineState) (effect : Effect β) (reply : β)
    (next : β → Program UInt32) (after : World) (alive : engine.running = true)
    (head : engine.current = .call effect next) (source : EngineSourceFrom sourceProgram engine) :
    EngineSourceFrom sourceProgram (engine.returned effect reply next after) := by
  have reached : Residual sourceProgram engine.events engine.current := by
    simpa only [EngineSourceFrom, alive, Bool.true_eq, ite_true] using source
  apply residual_append reached
  rw [head]
  exact .call (.refl _)

theorem lost_engine_source_for {β : Type} (engine : EngineState) (effect : Effect β)
    (next : β → Program UInt32) (after : World) (alive : engine.running = true)
    (head : engine.current = .call effect next) (source : EngineSourceFrom sourceProgram engine) :
    EngineSourceFrom sourceProgram (engine.lost effect after) := by
  have reached : Residual sourceProgram engine.events engine.current := by
    simpa only [EngineSourceFrom, alive, Bool.true_eq, ite_true] using source
  apply residual_prefix reached
  rw [head]
  exact .lost _ _

theorem engine_source_prefix_for (engine : EngineState) (source : EngineSourceFrom sourceProgram engine) :
    Program.Prefix sourceProgram engine.events := by
  unfold EngineSourceFrom at source
  split at source
  · simpa only [List.append_nil] using residual_prefix source (.empty _)
  · exact source

theorem retired_engine_source_for (engine : EngineState) (observation : EngineRetirement) (after : World)
    (source : EngineSourceFrom sourceProgram engine) : EngineSourceFrom sourceProgram (engine.retired observation after) :=
  engine_source_prefix_for engine source

-- §AR-host-boundary.interfaces: Preserve the original logical-source specialization.
def EngineSource (engine : EngineState) : Prop := EngineSourceFrom Entrypoint.run engine

theorem initial_engine_source (references : UInt64 → Option Handle) (closeExec : UInt64 → Bool)
    (workingDirectory : ObjectId) : EngineSource (EngineState.initial references closeExec workingDirectory) :=
  initial_engine_source_for Entrypoint.run references closeExec workingDirectory

theorem returned_engine_source {β : Type} (engine : EngineState) (effect : Effect β) (reply : β)
    (next : β → Program UInt32) (after : World) (alive : engine.running = true)
    (head : engine.current = .call effect next) (source : EngineSource engine) :
    EngineSource (engine.returned effect reply next after) :=
  returned_engine_source_for engine effect reply next after alive head source

theorem lost_engine_source {β : Type} (engine : EngineState) (effect : Effect β)
    (next : β → Program UInt32) (after : World) (alive : engine.running = true)
    (head : engine.current = .call effect next) (source : EngineSource engine) :
    EngineSource (engine.lost effect after) := lost_engine_source_for engine effect next after alive head source

theorem engine_source_prefix (engine : EngineState) (source : EngineSource engine) :
    Program.Prefix Entrypoint.run engine.events := engine_source_prefix_for engine source

-- §AR-host-boundary.primitives: Shared fields are projected with each actor's own FD references.
structure Population where
  shared : World
  actors : ActorId → Option EngineState
  born : ActorId → Bool

def Population.project (population : Population) (engine : EngineState) : World :=
  { population.shared with
    handles := engine.references, closeOnExec := engine.closeExec, workingDirectory := engine.workingDirectory }

def Population.install (population : Population) (actor : ActorId) (engine : EngineState) : Population :=
  { population with actors := fun query => if query = actor then some engine else population.actors query }

def Population.advance (population : Population) (actor : ActorId) (engine : EngineState)
    (shared : World) : Population := { population.install actor engine with shared }

def Population.launch (population : Population) (actor : ActorId) (engine : EngineState) : Population :=
  { population.install actor engine with born := fun query => if query = actor then true else population.born query }

def Population.SourceFrom (sourceProgram : Program UInt32) (population : Population) : Prop :=
  ∀ actor engine, population.actors actor = some engine → EngineSourceFrom sourceProgram engine

def Population.Source (population : Population) : Prop := population.SourceFrom Entrypoint.run

def Population.Consistent (population : Population) : Prop :=
  ∀ actor engine, population.actors actor = some engine → ValidReferences population.shared engine.references

def Population.empty (shared : World) : Population := ⟨shared, fun _ => none, fun _ => false⟩

theorem empty_population_source_for (sourceProgram : Program UInt32) (shared : World) :
    (Population.empty shared).SourceFrom sourceProgram := by
  intro actor engine present
  cases present

-- §AR-host-boundary.primitives: The non-FS effects retain their individual runtime relation.
structure ActorRuntime (kernel : Contract) (sourceProgram : Program UInt32 := Entrypoint.run) where
  other : {β : Type} → ActorId → Effect β → Option β → World → World → Prop
  foreign : Credentials → World → World → Prop
  initialReferences : ActorId → World → (UInt64 → Option Handle) → (UInt64 → Bool) → ObjectId → Prop
  retire : ActorId → EngineRetirement → Option ObjectId → World → World → Prop
  nativeRetire : ActorId → EngineRetirement → RetirementResources → RetirementResources → World → World → Prop

def ActorOperation {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) {β : Type}
    (actor : ActorId) (effect : Effect β) (reply : Option β) (before after : World) : Prop :=
  match effect with
  | .filesystem request => kernel.step before request reply after
  | other => runtime.other actor other reply before after

inductive ActorAction : Type 1 where
  | launch (actor : ActorId) (references : UInt64 → Option Handle) (closeExec : UInt64 → Bool) (workingDirectory : ObjectId)
  | returned {β : Type} (actor : ActorId) (effect : Effect β) (reply : β)
  | lost {β : Type} (actor : ActorId) (effect : Effect β)
  | foreign (caller : Credentials)
  | retire (actor : ActorId) (observation : EngineRetirement)
  | nativeRetire (token : ActorId) (observation : EngineRetirement) (before after : RetirementResources)

-- §FS-host-boundary.ownership: Every peer step executes the current residual of the real engine.
inductive ActorStep {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) :
    ActorAction → Population → Population → Prop where
  | launch {population : Population} {actor : ActorId}
      {references : UInt64 → Option Handle} {closeExec : UInt64 → Bool}
      {workingDirectory : ObjectId}
      (fresh : population.born actor = false) (absent : population.actors actor = none)
      (inherited : runtime.initialReferences actor population.shared references closeExec workingDirectory) :
      ActorStep runtime (.launch actor references closeExec workingDirectory) population
        (population.launch actor (.initialFrom sourceProgram references closeExec workingDirectory))
  | returned {β : Type} {population : Population} {actor : ActorId} {engine : EngineState}
      {effect : Effect β} {next : β → Program UInt32} {reply : β} {after : World}
      (present : population.actors actor = some engine) (alive : engine.running = true)
      (head : engine.current = .call effect next)
      (actual : ActorOperation runtime actor effect (some reply) (population.project engine) after) :
      ActorStep runtime (.returned actor effect reply) population
        (population.advance actor (engine.returned effect reply next after) after)
  | lost {β : Type} {population : Population} {actor : ActorId} {engine : EngineState}
      {effect : Effect β} {next : β → Program UInt32} {after : World}
      (present : population.actors actor = some engine) (alive : engine.running = true)
      (head : engine.current = .call effect next)
      (actual : ActorOperation runtime actor effect none (population.project engine) after) :
      ActorStep runtime (.lost actor effect) population
        (population.advance actor (engine.lost effect after) after)
  | foreign {population : Population} {caller : Credentials} {after : World}
      (actual : runtime.foreign caller population.shared after) :
      ActorStep runtime (.foreign caller) population { population with shared := after }
  | retire {population : Population} {actor : ActorId} {engine : EngineState}
      {observation : EngineRetirement} {after : World}
      (present : population.actors actor = some engine)
      (actual : runtime.retire actor observation engine.directory (population.project engine) after) :
      ActorStep runtime (.retire actor observation) population
        (population.advance actor (engine.retired observation after) after)
  | nativeRetire {population : Population} {token : ActorId} {observation : EngineRetirement}
      {beforeResources afterResources : RetirementResources} {after : World}
      (actual : runtime.nativeRetire token observation beforeResources afterResources population.shared after) :
      ActorStep runtime (.nativeRetire token observation beforeResources afterResources)
        population { population with shared := after }

theorem actor_step_source_for {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {action : ActorAction} {before after : Population}
    (step : ActorStep runtime action before after) (source : before.SourceFrom sourceProgram) : after.SourceFrom sourceProgram := by
  cases step with
  | @launch population actor references closeExec workingDirectory fresh absent inherited =>
    intro query engine present
    by_cases same : query = actor
    · subst query
      simp only [Population.launch, Population.install] at present
      cases present
      exact initial_engine_source_for sourceProgram references closeExec workingDirectory
    · exact source query engine (by simpa only [Population.launch, Population.install, ite_eq_right same] using present)
  | @returned β population actor engine effect next reply world present alive head actual =>
    intro query result found
    by_cases same : query = actor
    · subst query
      simp only [Population.advance, Population.install] at found
      cases found
      exact returned_engine_source_for engine effect reply next world alive head (source actor engine present)
    · exact source query result (by simpa only [Population.advance, Population.install, ite_eq_right same] using found)
  | @lost β population actor engine effect next world present alive head actual =>
    intro query result found
    by_cases same : query = actor
    · subst query
      simp only [Population.advance, Population.install] at found
      cases found
      exact lost_engine_source_for engine effect next world alive head (source actor engine present)
    · exact source query result (by simpa only [Population.advance, Population.install, ite_eq_right same] using found)
  | foreign actual => exact source
  | @retire population actor engine observation world present actual =>
    intro query result found
    by_cases same : query = actor
    · subst query
      simp only [Population.advance, Population.install] at found
      cases found
      exact retired_engine_source_for engine observation world (source actor engine present)
    · exact source query result (by simpa only [Population.advance, Population.install, ite_eq_right same] using found)
  | nativeRetire actual => exact source

inductive ActorHistory {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) : Population → Population → Prop where
  | refl (population : Population) : ActorHistory runtime population population
  | cons {before middle after : Population} {action : ActorAction} (step : ActorStep runtime action before middle)
      (tail : ActorHistory runtime middle after) : ActorHistory runtime before after

theorem actor_history_source_for {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} {before after : Population}
    (history : ActorHistory runtime before after) (source : before.SourceFrom sourceProgram) : after.SourceFrom sourceProgram := by
  induction history with
  | refl => exact source
  | cons step tail ih => exact ih (actor_step_source_for step source)

-- §FS-host-boundary.acceptance: Source provenance is derived from the same complete actor journal.
theorem actual_actor_entry_prefix_for {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {initial : World} {after : Population} (history : ActorHistory runtime (Population.empty initial) after)
    (actor : ActorId) (engine : EngineState) (present : after.actors actor = some engine) :
    Program.Prefix sourceProgram engine.events :=
  engine_source_prefix_for engine (actor_history_source_for history (empty_population_source_for sourceProgram initial) actor engine present)

structure ActorTick {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) where
  action : ActorAction
  before : Population
  after : Population
  operation : ActorStep runtime action before after

-- §FS-host-boundary.acceptance: Positions refer to this one ordered list of actual kernel actions.
inductive ActorJournal {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) :
    Population → List (ActorTick runtime) → Population → Prop where
  | nil (population : Population) : ActorJournal runtime population [] population
  | cons {tick : ActorTick runtime} {ticks : List (ActorTick runtime)} {after : Population}
      (tail : ActorJournal runtime tick.after ticks after) :
      ActorJournal runtime tick.before (tick :: ticks) after

theorem actor_journal_history {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) : ActorHistory runtime before after := by
  induction journal with
  | nil population => exact .refl population
  | @cons tick ticks after tail ih => exact .cons tick.operation ih

theorem actor_journal_split {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} (leading suffix : List (ActorTick runtime))
    (journal : ActorJournal runtime before (leading ++ suffix) after) :
    ∃ middle, ActorJournal runtime before leading middle ∧ ActorJournal runtime middle suffix after := by
  induction leading generalizing before with
  | nil => exact ⟨before, .nil _, journal⟩
  | cons tick rest ih =>
    cases journal with
    | cons tail =>
      obtain ⟨middle, first, last⟩ := ih tail
      exact ⟨middle, .cons first, last⟩

theorem actor_journal_selected_source_for {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {initial : World} {after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks after)
    (leading suffix : List (ActorTick runtime)) (tick : ActorTick runtime)
    (position : ticks = leading ++ tick :: suffix) : tick.before.SourceFrom sourceProgram := by
  rw [position] at journal
  obtain ⟨middle, first, rest⟩ := actor_journal_split leading _ journal
  cases rest with
  | cons tail => exact actor_history_source_for (actor_journal_history first) (empty_population_source_for sourceProgram initial)

-- §FS-host-boundary.ownership: A selected syscall's actual head is reached by that same actor.
theorem selected_actor_head_for {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {initial : World} {after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks after)
    (leading suffix : List (ActorTick runtime)) (tick : ActorTick runtime)
    (position : ticks = leading ++ tick :: suffix) {actor : ActorId} {engine : EngineState}
    (present : tick.before.actors actor = some engine) (alive : engine.running = true) :
    Residual sourceProgram engine.events engine.current := by
  have source := actor_journal_selected_source_for journal leading suffix tick position actor engine present
  simpa only [EngineSourceFrom, alive, Bool.true_eq, ite_true] using source

-- §AR-host-boundary.interfaces: Existing logical callers retain their exact entry specialization.
theorem empty_population_source (shared : World) : (Population.empty shared).Source :=
  empty_population_source_for Entrypoint.run shared

theorem actor_step_source {kernel : Contract} {runtime : ActorRuntime kernel}
    {action : ActorAction} {before after : Population}
    (step : ActorStep runtime action before after) (source : before.Source) : after.Source :=
  actor_step_source_for step source

theorem actor_history_source {kernel : Contract} {runtime : ActorRuntime kernel} {before after : Population}
    (history : ActorHistory runtime before after) (source : before.Source) : after.Source :=
  actor_history_source_for history source

theorem actual_actor_entry_prefix {kernel : Contract} {runtime : ActorRuntime kernel}
    {initial : World} {after : Population} (history : ActorHistory runtime (Population.empty initial) after)
    (actor : ActorId) (engine : EngineState) (present : after.actors actor = some engine) :
    Program.Prefix Entrypoint.run engine.events := actual_actor_entry_prefix_for history actor engine present

theorem actor_journal_selected_source {kernel : Contract} {runtime : ActorRuntime kernel}
    {initial : World} {after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks after)
    (leading suffix : List (ActorTick runtime)) (tick : ActorTick runtime)
    (position : ticks = leading ++ tick :: suffix) : tick.before.Source :=
  actor_journal_selected_source_for journal leading suffix tick position

theorem selected_actor_head {kernel : Contract} {runtime : ActorRuntime kernel}
    {initial : World} {after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks after)
    (leading suffix : List (ActorTick runtime)) (tick : ActorTick runtime)
    (position : ticks = leading ++ tick :: suffix) {actor : ActorId} {engine : EngineState}
    (present : tick.before.actors actor = some engine) (alive : engine.running = true) :
    Residual Entrypoint.run engine.events engine.current := selected_actor_head_for journal leading suffix tick position present alive

end LeanCage.Host.Kernel
