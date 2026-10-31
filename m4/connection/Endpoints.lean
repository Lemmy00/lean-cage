import LeanCageM3

namespace LeanCageM4
open LeanCageM3

-- §AR-m4-effects.lean: These use the live M3 definitions; no C/Lean bridge is assumed.
def observations (state : Knowledge) : List Observation → Knowledge
  | [] => state
  | event :: rest => observations (observe state event) rest

theorem observations_append (state : Knowledge) (front suffix : List Observation) :
    observations state (front ++ suffix) = observations (observations state front) suffix := by
  induction front generalizing state with
  | nil => rfl
  | cons e es ih => exact ih (observe state e)

theorem observed_entry_persists (state : Knowledge) (events : List Observation)
    (entered : state.entry = .yes) : (observations state events).entry = .yes := by
  induction events generalizing state with
  | nil => exact entered
  | cons e es ih =>
    apply ih
    cases e <;> simp_all [observe]
    split <;> simp_all

theorem entry_step_origin (state : Knowledge) (event : Observation)
    (after : (observe state event).entry = .yes) :
    state.entry = .yes ∨ event = .execObserved := by
  cases event <;> simp_all [observe]
  case releaseObserved => split at after <;> simp_all

theorem entry_trace_origin (state : Knowledge) (events : List Observation)
    (after : (observations state events).entry = .yes) :
    state.entry = .yes ∨ Observation.execObserved ∈ events := by
  induction events generalizing state with
  | nil => exact Or.inl after
  | cons e es ih =>
    have origin := ih (observe state e) after
    rcases origin with current | later
    · rcases entry_step_origin state e current with before | entered
      · exact Or.inl before
      · exact Or.inr (by simp [entered])
    · exact Or.inr (List.mem_cons_of_mem e later)

theorem initial_entry_needs_exec (events : List Observation)
    (after : (observations {} events).entry = .yes) :
    Observation.execObserved ∈ events := by
  rcases entry_trace_origin {} events after with impossible | present
  · contradiction
  · exact present

theorem release_step_sound (state : Knowledge) (event : Observation)
    (before : state.released = true → state.extinct = true) :
    (observe state event).released = true → (observe state event).extinct = true := by
  cases event <;> simp_all [observe]
  case releaseObserved => split <;> simp_all

theorem trace_release_needs_extinction (events : List Observation) :
    (observations {} events).released = true →
      (observations {} events).extinct = true := by
  have general : ∀ state : Knowledge, (state.released = true → state.extinct = true) →
      (observations state events).released = true →
        (observations state events).extinct = true := by
    induction events with
    | nil => intro state h; exact h
    | cons e es ih =>
      intro state h
      exact ih (observe state e) (release_step_sound state e h)
  exact general {} (by simp)

-- §AR-m4-effects.lean: A final decoder result retains all concrete M3 validity checks.
theorem accepted_final_valid (bytes : ByteArray) (result : Result)
    (accepted : decodeResult bytes = .ok result) : resultValid result = true :=
  decodeResult_valid bytes result accepted

theorem accepted_final_excludes_intermediate (bytes : ByteArray) (result : Result)
    (accepted : decodeResult bytes = .ok result) : result.kind ≠ 5 ∧ result.kind ≠ 6 := by
  have valid := decodeResult_valid bytes result accepted
  constructor <;> intro kind <;> simp [resultValid, kind] at valid

theorem launch_trace_keeps_receipt_order (events : List LaunchEvent)
    (entered : (launchTrace {} events).entered = true) :
    (launchTrace {} events).receipts = required :=
  reachable_entry_ordered events entered

theorem entry_then_reporting_loss_witness :
    (observations {} [.execObserved, .cancel, .reportLost]).entry = .yes ∧
    (observations {} [.execObserved, .cancel, .reportLost]).extinct = false ∧
    (observations {} [.execObserved, .cancel, .reportLost]).released = false := by
  decide

theorem guest_report_cannot_release_witness (bytes : ByteArray) :
    (observations {} [.guestBytes bytes, .cancel, .releaseObserved, .reportLost]).released = false :=
  rfl

end LeanCageM4
