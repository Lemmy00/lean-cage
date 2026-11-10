import GatewayStreamKernel
import GatewayStreamWriter

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

structure Record where
  position : Nat
  event : ProgressEvent
  actions : List Action

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

-- §AR-host-boundary.primitives: These are individual actual physical samples
-- on the SAME global rows; a pending commit is independent of a later reply.
inductive ObservedStep (primitive : Primitive process child native hostUid before after callers next ticks pair Token) :
    PhysicalState → Record → PhysicalState → Type 1 where
  | engine (state : PhysicalState) (entry : EngineWriteEntry ticks pair) (token : Token)
      (entered : primitive.enteredEngine token entry) (fresh : state.ledger entry.key = none) :
      ObservedStep primitive state ⟨entry.position, .begin entry.key entry.description, []⟩
        { state with ledger := state.ledger.set entry.key ⟨entry.description, 0, Nat.zero_le _, .pending⟩ }
  | native (state : PhysicalState)
      (entry : NativeWriteEntry process child native hostUid before after callers next ticks pair) (token : Token)
      (entered : primitive.enteredNative token entry) (fresh : state.ledger entry.key = none) :
      ObservedStep primitive state ⟨entry.position, .begin entry.key entry.description, []⟩
        { state with ledger := state.ledger.set entry.key ⟨entry.description, 0, Nat.zero_le _, .pending⟩ }
  | commit (position : Nat) (inside : position ≤ ticks.length) (token : Token)
      (current : WriteProgress) (state : PhysicalState) (initial final : State) (extent : Nat)
      (selected : state.ledger (primitive.input token).1 = some current) (live : state.stream = some initial)
      (actual : primitive.progress position token current extent initial final) :
      ObservedStep primitive state
        ⟨position, .commit (primitive.input token).1 extent,
          [.write current.input.sender (segment current.input.bytes current.committed extent)]⟩
        { stream := some final
          ledger := state.ledger.set (primitive.input token).1
            { current with
              committed := extent
              bounded := by
                have result := primitive.progressLaw _ _ _ _ _ _ actual
                exact result.1.symm ▸ result.2.2.2.1 } }
  | observation (position : Nat) (inside : position ≤ ticks.length) (token : Token)
      (current : WriteProgress) (state : PhysicalState) (initial final : State) (reply : Option Reply)
      (selected : state.ledger (primitive.input token).1 = some current) (live : state.stream = some initial)
      (actual : primitive.observation position token current reply initial final) :
      ObservedStep primitive state ⟨position, observationEvent (primitive.input token).1 reply, []⟩
        { stream := some final
          ledger := state.ledger.set (primitive.input token).1 (observed current reply) }
  | read (entry : NativeReadEntry process child native hostUid before after callers next ticks pair)
      (state : PhysicalState) (initial final : State) (live : state.stream = some initial)
      (flags : entry.flags = 0) (actual : primitive.read entry initial final) :
      ObservedStep primitive state ⟨entry.position, .channel (.read entry.receiver entry.bytes.data.toList),
        [.read entry.receiver entry.bytes.data.toList]⟩ { state with stream := some final }
  | birth (entry : PairBirthEntry process child native hostUid before after callers next ticks pair)
      (state : PhysicalState) (final : Option State) (actual : primitive.birth entry state.stream final) :
      ObservedStep primitive state ⟨entry.position, .channel .born, [.born]⟩ { state with stream := final }
  | other (position : Nat) (inside : position ≤ ticks.length) (state : PhysicalState)
      (action : Action) (final : Option State) (actual : primitive.other position action state.stream final) :
      ObservedStep primitive state ⟨position, .channel action, [action]⟩ { state with stream := final }

theorem ObservedStep.erase
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initial final : PhysicalState} {record : Record} (actual : ObservedStep primitive initial record final) :
    ProgressStep initial record.event record.actions final := by
  cases actual with
  | engine => exact .begin _ _ _ (by assumption)
  | native => exact .begin _ _ _ (by assumption)
  | commit position inside token current state initial final extent selected live actual =>
    exact token_progress_step _ _ _ _ _ _ _ _ selected live actual
  | observation position inside token current state initial final reply selected live actual =>
    exact token_observation_step _ _ _ _ _ _ _ _ selected live actual
  | read entry state initial final live flags actual => exact native_read_step _ _ _ _ _ live flags actual
  | birth entry state final actual => exact pair_birth_step _ _ _ _ actual
  | other position inside state action final actual => exact other_step _ _ _ _ _ actual

-- §FS-host-boundary.ownership: Ledger origins are source entries, not a claimed
-- safe-payload predicate. Their actual raw arguments remain available to consumers.
inductive InputAt (primitive : Primitive process child native hostUid before after callers next ticks pair Token)
    (position : Nat) : CallKey → WriteDescription → Prop where
  | engine (entry : EngineWriteEntry ticks pair) (token : Token)
      (entered : primitive.enteredEngine token entry) (order : entry.position ≤ position) :
      InputAt primitive position entry.key entry.description
  | native (entry : NativeWriteEntry process child native hostUid before after callers next ticks pair) (token : Token)
      (entered : primitive.enteredNative token entry) (order : entry.position ≤ position) :
      InputAt primitive position entry.key entry.description

theorem InputAt.monotone
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {first last : Nat} {key : CallKey} {input : WriteDescription}
    (origin : InputAt primitive first key input) (ordered : first ≤ last) : InputAt primitive last key input := by
  cases origin with
  | engine entry token entered order => exact .engine entry token entered (Nat.le_trans order ordered)
  | native entry token entered order => exact .native entry token entered (Nat.le_trans order ordered)

def Registered (primitive : Primitive process child native hostUid before after callers next ticks pair Token)
    (position : Nat) (state : PhysicalState) : Prop :=
  ∀ key current, state.ledger key = some current → InputAt primitive position key current.input

private theorem ledger_set_property (property : CallKey → WriteDescription → Prop) (ledger : Ledger)
    (key : CallKey) (current : WriteProgress)
    (before : ∀ selected value, ledger selected = some value → property selected value.input)
    (inserted : property key current.input) :
    ∀ selected value, (ledger.set key current) selected = some value → property selected value.input := by
  intro selected value found
  by_cases same : selected = key
  · subst selected
    have identity : current = value := Option.some.inj (by simpa [Ledger.set] using found)
    exact identity ▸ inserted
  · exact before selected value (by simpa only [Ledger.set, ite_eq_right same] using found)

theorem progress_ledger_property {initial final : PhysicalState} {event : ProgressEvent} {actions : List Action}
    (actual : ProgressStep initial event actions final) (property : CallKey → WriteDescription → Prop)
    (before : ∀ key current, initial.ledger key = some current → property key current.input)
    (began : ∀ key input, event = .begin key input → property key input) :
    ∀ key current, final.ledger key = some current → property key current.input := by
  cases actual with
  | begin key input fresh => exact ledger_set_property property _ _ _ before (began _ _ rfl)
  | commit key current stream extent selected live unreturned increase bound writable =>
    exact ledger_set_property property _ _ _ before (before key current selected)
  | returned key current reply selected pending count =>
    exact ledger_set_property property _ _ _ before (before key current selected)
  | lost key current selected pending =>
    exact ledger_set_property property _ _ _ before (before key current selected)
  | channel => exact before

theorem ObservedStep.began
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initial final : PhysicalState} {record : Record} (actual : ObservedStep primitive initial record final)
    {key : CallKey} {input : WriteDescription} (selected : record.event = .begin key input) :
    InputAt primitive record.position key input := by
  cases actual with
  | engine state entry token entered fresh => cases selected; exact .engine entry token entered (Nat.le_refl _)
  | native state entry token entered fresh => cases selected; exact .native entry token entered (Nat.le_refl _)
  | commit => cases selected
  | observation position inside token current state initial final reply selected live actual => cases reply <;> cases selected
  | read => cases selected
  | birth => cases selected
  | other => cases selected

theorem ObservedStep.registered
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initial final : PhysicalState} {record : Record} (actual : ObservedStep primitive initial record final)
    {position : Nat} (earlier : position ≤ record.position) (registered : Registered primitive position initial) :
    Registered primitive record.position final := by
  apply progress_ledger_property actual.erase (InputAt primitive record.position)
  · intro key current selected
    exact (registered key current selected).monotone earlier
  · intro key input selected
    exact actual.began selected

theorem ObservedStep.written_origin
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initial final : PhysicalState} {record : Record} (actual : ObservedStep primitive initial record final)
    {position : Nat} (earlier : position ≤ record.position) (registered : Registered primitive position initial)
    (sender : Side) (bytes : Bytes) (member : Action.write sender bytes ∈ record.actions) :
    ∃ key input first last, InputAt primitive record.position key input ∧ input.sender = sender ∧
      bytes = segment input.bytes first last ∧ first < last ∧ last ≤ input.bytes.length := by
  cases actual with
  | engine => cases member
  | native => cases member
  | commit position inside token current state initial final extent selected live actual =>
    have same := Action.write.inj (List.mem_singleton.mp member)
    obtain ⟨rfl, rfl⟩ := same
    have law := primitive.progressLaw _ _ _ _ _ _ actual
    refine ⟨_, current.input, current.committed, extent,
      (registered _ current selected).monotone earlier, rfl, rfl, law.2.2.1, ?_⟩
    exact law.1.symm ▸ law.2.2.2.1
  | observation => cases member
  | read => cases List.mem_singleton.mp member
  | birth => cases List.mem_singleton.mp member
  | other position inside state action final actual =>
    exact False.elim ((primitive.otherLaw _ _ _ _ actual).2.1 sender bytes (List.mem_singleton.mp member).symm)

theorem ObservedStep.absent_or_birth
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initial final : PhysicalState} {record : Record} (actual : ObservedStep primitive initial record final)
    (absent : initial.stream = none) :
    final.stream = none ∨ ∃ entry : PairBirthEntry process child native hostUid before after callers next ticks pair,
      record = ⟨entry.position, .channel .born, [.born]⟩ ∧
      final = { initial with stream := some .empty } ∧ primitive.birth entry none (some .empty) := by
  cases actual with
  | engine => exact .inl absent
  | native => exact .inl absent
  | commit position inside token current state initial final extent selected live actual =>
    rw [absent] at live
    cases live
  | observation position inside token current state initial final reply selected live actual =>
    rw [absent] at live
    cases live
  | read entry state initial final live flags actual =>
    rw [absent] at live
    cases live
  | birth entry state final actual =>
    have law := primitive.birthLaw _ _ _ actual
    have same := law.2
    subst final
    exact .inr ⟨entry, rfl, rfl, by simpa only [absent] using actual⟩
  | other position inside state action final actual =>
    have law := primitive.otherLaw _ _ _ _ actual
    have step := law.1
    rw [absent] at step
    cases step with
    | born => exact False.elim (law.2.2 rfl)
    | quiet => exact .inl rfl

inductive ObservedJournal
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token) :
    Nat → PhysicalState → List Record → PhysicalState → Type 1 where
  | nil (position : Nat) (state : PhysicalState) : ObservedJournal primitive position state [] state
  | cons {position : Nat} {initial middle final : PhysicalState} {record : Record} {records : List Record}
      (ordered : position ≤ record.position) (actual : ObservedStep primitive initial record middle)
      (tail : ObservedJournal primitive record.position middle records final) :
      ObservedJournal primitive position initial (record :: records) final

theorem steps_append {first middle last : Option State} {initial final : List Action}
    (before : Steps first initial middle) (after : Steps middle final last) : Steps first (initial ++ final) last := by
  induction before with
  | nil => exact after
  | cons head tail ih => exact .cons head (ih after)

theorem ObservedJournal.stream
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {initial final : PhysicalState} {records : List Record}
    (actual : ObservedJournal primitive position initial records final) :
    Steps initial.stream (records.flatMap Record.actions) final.stream := by
  induction actual with
  | nil => exact .nil _
  | cons ordered actual tail ih => exact steps_append (progress_stream actual.erase) ih

theorem ObservedJournal.registered
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {initial final : PhysicalState} {records : List Record}
    (actual : ObservedJournal primitive position initial records final) (registered : Registered primitive position initial) :
    ∃ last, position ≤ last ∧ Registered primitive last final := by
  induction actual with
  | nil position state => exact ⟨position, Nat.le_refl _, registered⟩
  | cons ordered actual tail ih =>
    obtain ⟨last, order, final⟩ := ih (actual.registered ordered registered)
    exact ⟨last, Nat.le_trans ordered order, final⟩

def PhysicalState.unborn : PhysicalState := ⟨none, fun _ => none⟩

theorem registered_unborn
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token) :
    Registered primitive 0 .unborn := by
  intro key current impossible
  cases impossible

-- §FS-host-boundary.ownership: Queue initialization is produced by the actual
-- fresh socketpair occurrence in this history, never a free private-state invariant.
theorem ObservedJournal.birth_cut
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {initial final : PhysicalState} {records : List Record}
    (actual : ObservedJournal primitive position initial records final) (absent : initial.stream = none)
    (live : ∃ stream, final.stream = some stream) :
    ∃ (leading rest : List Record) (entry : PairBirthEntry process child native hostUid before after callers next ticks pair)
        (prior : PhysicalState),
      records = leading ++ ⟨entry.position, .channel .born, [.born]⟩ :: rest ∧
      Nonempty (ObservedJournal primitive position initial leading prior) ∧ prior.stream = none ∧
      primitive.birth entry none (some .empty) ∧
      Nonempty (ObservedJournal primitive entry.position { prior with stream := some .empty } rest final) := by
  induction actual with
  | nil position state => obtain ⟨stream, present⟩ := live; rw [absent] at present; cases present
  | @cons position initial middle final record records ordered actual tail ih =>
    rcases actual.absent_or_birth absent with stillAbsent | ⟨entry, sameRecord, sameMiddle, birth⟩
    · obtain ⟨leading, rest, entry, prior, shape, ⟨before⟩, absent, birth, ⟨after⟩⟩ := ih stillAbsent live
      exact ⟨record :: leading, rest, entry, prior, by simp only [shape, List.cons_append],
        ⟨.cons ordered actual before⟩, absent, birth, ⟨after⟩⟩
    · subst record middle
      exact ⟨[], records, entry, initial, rfl, ⟨.nil _ _⟩, absent, birth, ⟨tail⟩⟩

-- §FS-host-boundary.caller: This is a byte-prefix consequence of the actual
-- per-operation queue history. No complete response or successful writer is assumed.
theorem observed_received_prefix
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {initial final : PhysicalState} {records : List Record}
    (actual : ObservedJournal primitive position initial records final) (born : initial.stream = some .empty)
    (receiver : Side) (retained : ∀ action ∈ records.flatMap Record.actions, preservesUnread receiver action) :
    ∃ pending, (records.flatMap Record.actions).flatMap (written receiver) =
      (records.flatMap Record.actions).flatMap (received receiver) ++ pending := by
  have run := actual.stream
  rw [born] at run
  obtain ⟨state, selected, live⟩ := steps_live run
  exact run_received_prefix receiver live retained

theorem absent_steps_no_bytes {initial final : Option State} {actions : List Action}
    (actual : Steps initial actions final) (receiver : Side) (first : initial = none) (last : final = none) :
    actions.flatMap (written receiver) = [] ∧ actions.flatMap (received receiver) = [] := by
  induction actual with
  | nil => cases first; exact ⟨rfl, rfl⟩
  | cons head tail ih =>
    cases first
    cases head with
    | born =>
      obtain ⟨state, impossible, run⟩ := steps_live tail
      rw [last] at impossible
      cases impossible
    | quiet =>
      obtain ⟨emptyWritten, emptyRead⟩ := ih rfl last
      exact ⟨by simpa only [List.flatMap_cons, written, List.nil_append] using emptyWritten,
        by simpa only [List.flatMap_cons, received, List.nil_append] using emptyRead⟩

-- §FS-host-boundary.caller: The actual fresh birth, ordered partial commits and
-- selected read products yield this prefix fact from the global-history adapter.
-- Other-reader/discard authority remains an explicit source/custody obligation.
theorem actual_received_prefix_from_birth
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {final : PhysicalState} {records : List Record}
    (actual : ObservedJournal primitive 0 .unborn records final) (live : ∃ stream, final.stream = some stream)
    (receiver : Side) (retained : ∀ action ∈ records.flatMap Record.actions, preservesUnread receiver action) :
    ∃ (entry : PairBirthEntry process child native hostUid before after callers next ticks pair), ∃ pending,
      primitive.birth entry none (some .empty) ∧
      (records.flatMap Record.actions).flatMap (written receiver) =
        (records.flatMap Record.actions).flatMap (received receiver) ++ pending := by
  obtain ⟨leading, rest, entry, prior, shape, ⟨prefixRun⟩, absent, birth, ⟨suffixRun⟩⟩ := actual.birth_cut rfl live
  have beforeBirth : Steps none (leading.flatMap Record.actions) none := by
    simpa only [PhysicalState.unborn, absent] using prefixRun.stream
  obtain ⟨emptyWritten, emptyRead⟩ := absent_steps_no_bytes beforeBirth receiver rfl rfl
  have tailRetained : ∀ action ∈ rest.flatMap Record.actions, preservesUnread receiver action := by
    intro action member
    apply retained action
    simp only [shape, List.flatMap_append, List.flatMap_cons]
    exact List.mem_append_right _ (List.mem_append_right _ member)
  obtain ⟨pending, finalPrefix⟩ := observed_received_prefix suffixRun rfl receiver tailRetained
  refine ⟨entry, pending, birth, ?_⟩
  simpa only [shape, List.flatMap_append, List.flatMap_cons, written, received, List.flatMap_nil,
    List.nil_append, emptyWritten, emptyRead] using finalPrefix

end LeanCage.Host.PrivateStreams
