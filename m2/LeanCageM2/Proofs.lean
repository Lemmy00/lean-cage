import LeanCageM2.Model
import LeanCage.Proofs.Launch
import LeanCage.Proofs.FilterDecoder

namespace LeanCageM2

-- §FS-lifecycle.model: No initial resource, entry or descendant is assumed established.
theorem initial_safe : Safe initial := by simp [Safe, initial]

-- §FS-lifecycle.model: Success sets actual modeled receipts; all prior restrictions persist.
theorem establish_safe (s : State) (op : Operation) (safe : Safe s)
    (live : s.extinct = false) (guard : op = .exec → ready s = true) :
    Safe (establish s op) := by
  cases op <;> simp_all [Safe, establish, nextOperation, ready, Member.Secure]

-- §FS-lifecycle.model: All allowed effects, failures and hostile guest steps preserve safety.
theorem step_safe (abi : LeanCage.Linux.Filter.Abi) (bytes : ByteArray)
    (s t : State) (event : Event) (safe : Safe s)
    (transition : step abi bytes s event = some t) : Safe t := by
  cases event with
  | ok op =>
    simp only [step] at transition
    split at transition
    · contradiction
    · rename_i permitted
      split at transition
      · contradiction
      · split at transition
        · contradiction
        · rename_i guarded
          obtain rfl := Option.some.inj transition
          have phase : s.phase = .setup op :=
            by simpa using permitted
          have live : s.extinct = false := by
            cases h : s.extinct
            · rfl
            · have := (safe.2.2 h).1; simp_all
          apply establish_safe s op safe live
          intro exec
          simpa [exec] using guarded
  | fork parent fresh =>
    simp only [step] at transition
    split at transition
    · rename_i admitted
      obtain rfl := Option.some.inj transition
      simp only [Bool.and_eq_true, decide_eq_true_eq] at admitted
      rcases admitted with ⟨⟨phase, member⟩, _⟩
      refine ⟨safe.1, ?_, ?_⟩
      · intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact safe.2.1 parent member
        · exact safe.2.1 p hp
      · intro extinct
        have := (safe.2.2 extinct).1
        simp_all
    · contradiction
  | exit member =>
    simp only [step] at transition
    split at transition
    · obtain rfl := Option.some.inj transition
      refine ⟨safe.1, ?_, ?_⟩
      · intro p hp; exact safe.2.1 p (List.mem_filter.mp hp).1
      · intro extinct
        obtain ⟨phase, members⟩ := safe.2.2 extinct
        simp_all
    · contradiction
  | reexec member | escapeAttempt member | signalOutside member =>
    simp only [step] at transition
    split at transition
    · obtain rfl := Option.some.inj transition; exact safe
    · contradiction
  | namespaceDeath =>
    simp only [step, Option.some.injEq] at transition
    subst t
    exact ⟨safe.1, by simp, by simp⟩
  | reportLost =>
    simp only [step, Option.some.injEq] at transition
    subst t
    exact safe
  | cancelRequest =>
    simp only [step] at transition
    split at transition
    · contradiction
    · obtain rfl := Option.some.inj transition; exact safe
  | release handle =>
    simp only [step] at transition
    split at transition
    · obtain rfl := Option.some.inj transition; exact safe
    · contradiction
  | setupError op _ | interrupted op | contractViolation op =>
    simp only [step] at transition
    split at transition
    · rename_i pending
      obtain rfl := Option.some.inj transition
      refine ⟨safe.1, safe.2.1, ?_⟩
      intro extinct
      have := (safe.2.2 extinct).1
      simp_all
    · contradiction

-- §FS-lifecycle.model: Universal safety is over all reachable states, including hostile steps.
theorem reachable_safe (abi : LeanCage.Linux.Filter.Abi) (bytes : ByteArray) (s : State)
    (reachable : Reaches abi bytes s) : Safe s := by
  induction reachable with
  | initial => exact initial_safe
  | next _ transition ih => exact step_safe _ _ _ _ _ ih transition

-- §FS-lifecycle.supervision: Every live descendant inherits scope, credentials, NNP and filter.
theorem descendant_secure (abi : LeanCage.Linux.Filter.Abi) (bytes : ByteArray)
    (s : State) (reachable : Reaches abi bytes s) (member : Member) (owned : member ∈ s.members) :
    member.Secure := (reachable_safe abi bytes s reachable).2.1 member owned

-- §FS-lifecycle.model: Failed setup has no success continuation, for every operation.
theorem failed_no_setup (abi : LeanCage.Linux.Filter.Abi) (bytes : ByteArray)
    (s : State) (failed : s.phase = .failed) (op : Operation) :
    step abi bytes s (.ok op) = none := by simp [step, failed]

-- §FS-lifecycle.cancellation: Requesting cancellation does not remove any process.
theorem request_preserves_members (abi : LeanCage.Linux.Filter.Abi) (bytes : ByteArray)
    (s t : State) (h : step abi bytes s .cancelRequest = some t) : t.members = s.members := by
  simp only [step] at h
  split at h
  · contradiction
  · obtain rfl := Option.some.inj h; rfl

-- §FS-lifecycle.cancellation: Extinction observation, not request/reporting, empties the scope.
theorem death_empties_scope (abi : LeanCage.Linux.Filter.Abi) (bytes : ByteArray) (s : State) :
    ∃ t, step abi bytes s .namespaceDeath = some t ∧ t.extinct = true ∧ t.members = [] := by
  exact ⟨_, rfl, rfl, rfl⟩

-- §FS-lifecycle.resources: Cleanup cannot release a handle the controller does not own.
theorem release_owned_only (abi : LeanCage.Linux.Filter.Abi) (bytes : ByteArray)
    (s t : State) (handle : UInt64) (h : step abi bytes s (.release handle) = some t) :
    handle ∈ s.owned ∧ t.released = handle :: s.released := by
  simp only [step] at h
  split at h
  · rename_i owned; obtain rfl := Option.some.inj h; exact ⟨owned.1, rfl⟩
  · contradiction

-- §FS-lifecycle.supervision: Losing a report preserves history and weakens knowledge explicitly.
theorem lost_report_unknown (abi : LeanCage.Linux.Filter.Abi) (bytes : ByteArray) (s : State) :
    step abi bytes s .reportLost = some { s with knowledge := .unknown } := rfl

-- §FS-lifecycle.model: Ordered effects cannot be substituted/reordered by a caller's event.
theorem success_was_requested (abi : LeanCage.Linux.Filter.Abi) (bytes : ByteArray)
    (s t : State) (op : Operation) (h : step abi bytes s (.ok op) = some t) :
    request s = some op := by
  simp only [step] at h
  split at h
  · contradiction
  · rename_i allowed
    have phase : s.phase = .setup op := by simpa using allowed
    simp [request, phase]

-- §AR-lifecycle.design: The pure preparation used by Main has the independent M1 specification.
theorem preparePlan_iff (abi : LeanCage.Linux.Filter.Abi) (bytes : ByteArray)
    (operations : List Operation) :
    preparePlan abi bytes = .ok operations ↔
      LeanCage.Linux.Filter.ValidInput abi bytes ∧ operations = plan := by
  cases h : LeanCage.Linux.Filter.decode abi bytes with
  | error error =>
    simp only [preparePlan, h, reduceCtorEq, false_iff]
    intro ⟨valid, _⟩
    have := (LeanCage.Linux.Filter.decode_ok_iff abi bytes .denyGetppid).mpr valid
    simp_all
  | ok program =>
    have valid := (LeanCage.Linux.Filter.decode_ok_iff abi bytes program).mp h
    simp [preparePlan, h, valid, eq_comm]

-- §FS-lifecycle.model: Start before every setup operation.
theorem initial_ordered : Ordered initial := by simp [Ordered, initial, setupPrefix]

-- §FS-lifecycle.model: Each successful effect extends the exact required prefix.
theorem establish_ordered (s : State) (op : Operation) (ordered : Ordered s)
    (phase : s.phase = .setup op) : Ordered (establish s op) := by
  have completed := ordered.1 op phase
  have notEntered : s.entered = false := by
    cases he : s.entered
    · rfl
    · have full := ordered.2 he
      cases op <;> simp_all [setupPrefix, plan]
  cases op <;> simp_all [Ordered, establish, nextOperation, setupPrefix, plan]

-- §FS-lifecycle.model: Full histories remain ordered through errors and arbitrary guest actions.
theorem step_ordered (abi : LeanCage.Linux.Filter.Abi) (bytes : ByteArray)
    (s t : State) (event : Event) (ordered : Ordered s)
    (transition : step abi bytes s event = some t) : Ordered t := by
  cases event with
  | ok op =>
    simp only [step] at transition
    split at transition
    · contradiction
    · rename_i permitted
      have phase : s.phase = .setup op :=
        by simpa using permitted
      split at transition
      · contradiction
      · split at transition
        · contradiction
        · obtain rfl := Option.some.inj transition
          exact establish_ordered s op ordered phase
  | setupError op _ | interrupted op | contractViolation op =>
    simp only [step] at transition
    split at transition
    · obtain rfl := Option.some.inj transition
      exact ⟨by simp, ordered.2⟩
    · contradiction
  | fork parent fresh | exit parent =>
    simp only [step] at transition
    split at transition
    · obtain rfl := Option.some.inj transition; exact ordered
    · contradiction
  | reexec member | escapeAttempt member | signalOutside member =>
    simp only [step] at transition
    split at transition
    · obtain rfl := Option.some.inj transition; exact ordered
    · contradiction
  | namespaceDeath =>
    simp only [step, Option.some.injEq] at transition
    subst t; exact ⟨by simp, ordered.2⟩
  | reportLost =>
    simp only [step, Option.some.injEq] at transition
    subst t; exact ordered
  | cancelRequest | release _ =>
    simp only [step] at transition
    split at transition
    · first | contradiction | obtain rfl := Option.some.inj transition; exact ordered
    · first | contradiction | obtain rfl := Option.some.inj transition; exact ordered

-- §FS-lifecycle.model: All finite reachable setup histories preserve order.
theorem reachable_ordered (abi : LeanCage.Linux.Filter.Abi) (bytes : ByteArray) (s : State)
    (reachable : Reaches abi bytes s) : Ordered s := by
  induction reachable with
  | initial => exact initial_ordered
  | next _ transition ih => exact step_ordered _ _ _ _ _ ih transition

-- §FS-lifecycle.model: Entry requires every exact plan effect, not just an unordered receipt set.
theorem entry_requires_plan (abi : LeanCage.Linux.Filter.Abi) (bytes : ByteArray) (s : State)
    (reachable : Reaches abi bytes s) (entered : s.entered = true) : s.completed = plan :=
  (reachable_ordered abi bytes s reachable).2 entered

-- §FS-lifecycle.model: Decoder acceptance is established by the actual executable decoder.
theorem step_decoded (abi : LeanCage.Linux.Filter.Abi) (bytes : ByteArray)
    (s t : State) (event : Event) (decoded : Decoded abi bytes s)
    (transition : step abi bytes s event = some t) : Decoded abi bytes t := by
  cases event with
  | ok op =>
    simp only [step] at transition
    split at transition
    · contradiction
    · split at transition
      · contradiction
      · rename_i accepted
        split at transition
        · contradiction
        · obtain rfl := Option.some.inj transition
          cases op <;> simp_all [Decoded, establish]
  | setupError _ _ | interrupted _ | contractViolation _ | fork _ _ | exit _ | reexec _ | escapeAttempt _ | signalOutside _ | cancelRequest | release _ =>
    simp only [step] at transition
    split at transition
    · first | contradiction | obtain rfl := Option.some.inj transition; exact decoded
    · first | contradiction | obtain rfl := Option.some.inj transition; exact decoded
  | namespaceDeath | reportLost =>
    simp only [step, Option.some.injEq] at transition
    subst t; exact decoded

-- §FS-lifecycle.model: Every reachable decoder receipt reflects actual decoding.
theorem reachable_decoded (abi : LeanCage.Linux.Filter.Abi) (bytes : ByteArray) (s : State)
    (reachable : Reaches abi bytes s) : Decoded abi bytes s := by
  induction reachable with
  | initial => simp [Decoded, initial]
  | next _ transition ih => exact step_decoded _ _ _ _ _ ih transition

-- §FS-lifecycle.model: Arbitrary invalid inputs cannot enter even after other setup succeeds.
theorem invalid_input_never_enters (abi : LeanCage.Linux.Filter.Abi) (bytes : ByteArray)
    (s : State) (invalid : ¬LeanCage.Linux.Filter.ValidInput abi bytes)
    (reachable : Reaches abi bytes s) : s.entered = false := by
  cases entered : s.entered
  · rfl
  · have ready := (reachable_safe abi bytes s reachable).1 entered
    have decoded : s.decoded = true := by simp_all [LeanCageM2.ready]
    have accepted := reachable_decoded abi bytes s reachable decoded
    cases h : LeanCage.Linux.Filter.decode abi bytes with
    | error error => simp_all [Except.isOk, Except.toBool]
    | ok program => exact False.elim (invalid ((LeanCage.Linux.Filter.decode_ok_iff abi bytes program).mp h))

-- §FS-lifecycle.model: Exact ordered M1 projection; the original M1 theorem remains applicable.
theorem plan_refines_m1 : plan.flatMap m1Events = LeanCage.Launch.successTrace := rfl

-- §FS-lifecycle.model: The projected plan executes under the preserved M1 semantics.
theorem projected_m1_replay :
    LeanCage.Launch.replay true .unvalidated (plan.flatMap m1Events) = some .executed := by
  rw [plan_refines_m1]
  exact LeanCage.Launch.success_witness

-- §FS-lifecycle.model: Compose every reachable entered lifecycle with the unchanged M1 semantics.
theorem reachable_m1_refinement (abi : LeanCage.Linux.Filter.Abi) (bytes : ByteArray) (s : State)
    (reachable : Reaches abi bytes s) (entered : s.entered = true) :
    LeanCage.Launch.replay true .unvalidated (s.completed.flatMap m1Events) = some .executed := by
  rw [entry_requires_plan abi bytes s reachable entered]
  exact projected_m1_replay

-- §FS-lifecycle.model: Executable finite traces satisfy the same inductive invariants.
theorem replay_extends_reaches (abi : LeanCage.Linux.Filter.Abi) (bytes : ByteArray)
    (events : List Event) (s t : State) (reachable : Reaches abi bytes s)
    (h : replay abi bytes s events = some t) : Reaches abi bytes t := by
  induction events generalizing s with
  | nil => simp only [replay, Option.some.injEq] at h; subst t; exact reachable
  | cons event events ih =>
    simp only [replay] at h
    cases next : step abi bytes s event with
    | none => simp_all
    | some u =>
      simp only [next, Option.bind_some] at h
      exact ih u (Reaches.next reachable next) h

-- §FS-lifecycle.model: Kernel reduction supplies actual decoded success, not an invariant premise.
def successEvents : List Event := plan.map Event.ok

def successState : State :=
  { phase := .running, completed := plan, imageSealed := true, privateInputs := true,
    signalsReset := true, namespaced := true, handlesClosed := true,
    credentialsDropped := true, credentials := some restrictedCredentials,
    startupSignals := some cleanStartup, decoded := true, nnp := true, filtered := true,
    entered := true, knowledge := .yes, members := [⟨2,1,restrictedCredentials,true,true⟩], issued := [2], owned := [10,11,12] }

-- §FS-lifecycle.model: A full launch is inhabited with concrete accepted bytes.
theorem success_witness :
    replay LeanCage.Linux.Filter.nativeAbi LeanCage.Linux.Filter.canonicalBytes initial successEvents =
      some successState := by decide

-- §FS-lifecycle.cancellation: The exec race is inhabited; a request alone cannot suppress entry.
theorem cancellation_exec_race :
    replay LeanCage.Linux.Filter.nativeAbi LeanCage.Linux.Filter.canonicalBytes successState
      [.cancelRequest, .reportLost, .namespaceDeath] =
      some { successState with
        phase := .done
        cancelRequested := true
        knowledge := .unknown
        extinct := true
        members := [] } := by decide

-- §FS-lifecycle.model: A cancellation request may race before actual image replacement.
theorem request_can_precede_exec :
    (replay LeanCage.Linux.Filter.nativeAbi LeanCage.Linux.Filter.canonicalBytes initial
      (.cancelRequest :: successEvents)).map State.entered = some true := by decide

-- §FS-lifecycle.supervision: A real fork/exec/daemon-style survivor can be killed and reaped.
theorem descendant_teardown_witness :
    (replay LeanCage.Linux.Filter.nativeAbi LeanCage.Linux.Filter.canonicalBytes successState
      [.fork ⟨2,1,restrictedCredentials,true,true⟩ 3, .escapeAttempt ⟨3,1,restrictedCredentials,true,true⟩,
       .reexec ⟨3,1,restrictedCredentials,true,true⟩, .exit ⟨2,1,restrictedCredentials,true,true⟩,
       .cancelRequest, .namespaceDeath]).map State.members = some [] := by decide

end LeanCageM2
