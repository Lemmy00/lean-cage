import FilesystemLookupSemantics

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.acceptance: Raw lost/returned calls keep their real kernel step and origin.
inductive RawPrefixHistory (step : RawStep) (interference : RawInterference) (origin : RawOrigin) :
    Nat → World → List (Request × Option Reply) → World → Prop where
  | stop (ordinal : Nat) (world : World) : RawPrefixHistory step interference origin ordinal world [] world
  | returned {ordinal : Nat} {before middle after : World} {request : Request} {reply : Reply}
      {events : List (Request × Option Reply)} (actual : step before request (some reply) middle)
      (sampled : origin ordinal request (some reply) before middle)
      (tail : RawPrefixHistory step interference origin (ordinal + 1) middle events after) :
      RawPrefixHistory step interference origin ordinal before ((request, some reply) :: events) after
  | lost {ordinal : Nat} {before after : World} {request : Request}
      (actual : step before request none after) (sampled : origin ordinal request none before after) :
      RawPrefixHistory step interference origin ordinal before [(request, none)] after
  | environment {ordinal : Nat} {before middle after : World} {events : List (Request × Option Reply)}
      (actual : interference before middle)
      (tail : RawPrefixHistory step interference origin ordinal middle events after) :
      RawPrefixHistory step interference origin ordinal before events after

theorem raw_prefix_returned_head {step : RawStep} {interference : RawInterference} {origin : RawOrigin}
    {ordinal : Nat} {before after : World} {request : Request} {reply : Reply}
    {events : List (Request × Option Reply)}
    (history : RawPrefixHistory step interference origin ordinal before ((request, some reply) :: events) after) :
    ∃ actual middle, RawHistory step interference origin ordinal before [] actual ∧
      step actual request (some reply) middle ∧ origin ordinal request (some reply) actual middle ∧
      RawPrefixHistory step interference origin (ordinal + 1) middle events after := by
  generalize shape : (request, some reply) :: events = all at history
  induction history with
  | stop => cases shape
  | returned actual sampled tail ih => cases shape; exact ⟨_, _, .nil _ _, actual, sampled, tail⟩
  | lost => cases shape
  | environment actual tail ih =>
    obtain ⟨before, middle, leading, operation, sampled, rest⟩ := ih shape
    exact ⟨before, middle, .environment actual leading, operation, sampled, rest⟩

theorem raw_prefix_split {step : RawStep} {interference : RawInterference} {origin : RawOrigin}
    {ordinal : Nat} {before after : World} (first : List (Request × Reply)) (last : List (Request × Option Reply))
    (history : RawPrefixHistory step interference origin ordinal before
      (first.map (fun item => (item.1, some item.2)) ++ last) after) :
    ∃ middle, RawHistory step interference origin ordinal before first middle ∧
      RawPrefixHistory step interference origin (ordinal + first.length) middle last after := by
  induction first generalizing ordinal before with
  | nil => exact ⟨before, .nil _ _, history⟩
  | cons event rest ih =>
    obtain ⟨actual, between, leading, operation, sampled, tail⟩ := raw_prefix_returned_head history
    obtain ⟨middle, firstHistory, lastHistory⟩ := ih tail
    refine ⟨middle, raw_history_append leading (.call operation sampled firstHistory), ?_⟩
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lastHistory

theorem raw_prefix_operation_head {step : RawStep} {interference : RawInterference} {origin : RawOrigin}
    {ordinal : Nat} {before after : World} {request : Request} {observed : Option Reply}
    {events : List (Request × Option Reply)}
    (history : RawPrefixHistory step interference origin ordinal before ((request, observed) :: events) after) :
    ∃ actual middle, RawHistory step interference origin ordinal before [] actual ∧
      step actual request observed middle ∧ origin ordinal request observed actual middle := by
  generalize shape : (request, observed) :: events = all at history
  induction history with
  | stop => cases shape
  | returned actual sampled tail ih => cases shape; exact ⟨_, _, .nil _ _, actual, sampled⟩
  | lost actual sampled => cases shape; exact ⟨_, _, .nil _ _, actual, sampled⟩
  | environment actual tail ih =>
    obtain ⟨before, middle, leading, operation, sampled⟩ := ih shape
    exact ⟨before, middle, .environment actual leading, operation, sampled⟩

theorem checked_parents_recorded {step : RawStep} {interference : RawInterference}
    {origin : RawOrigin} {semantics : NameSemanticsView}
    (laws : LookupPrimitiveContract step interference semantics)
    {ordinal : Nat} {before after : World} {fds : List UInt64} {events : List (Request × Reply)}
    (checked : CheckedParents fds events) (history : RawHistory step interference origin ordinal before events after) :
    ∀ fd ∈ fds, ∀ handle, before.handles fd = some handle →
      Nonempty (CheckedDirectory step origin semantics fd handle) ∧ after.handles fd = some handle := by
  induction checked generalizing ordinal before with
  | nil => simp
  | cons fd rest first last accepted following ih =>
    obtain ⟨middle, initial, ending⟩ := raw_history_split first last history
    have firstSource := lookup_check_complete accepted
    have all := CheckedParents.cons fd rest first last accepted following
    have wholeFrame := raw_probe_history_handles laws history (checked_parents_probes all)
    intro query member handle live
    have finalLive : after.handles query = some handle := by rw [wholeFrame]; exact live
    refine ⟨?_, finalLive⟩
    rcases List.mem_cons.mp member with rfl | later
    · exact (lookup_check_raw_sound laws firstSource initial live).1
    · have firstFrame := raw_probe_history_handles laws initial
        (fun event member => checked_parents_probes (CheckedParents.cons fd [] first [] accepted .nil)
          event (by simpa only [List.append_nil] using member))
      exact (ih ending query later handle (by rw [firstFrame]; exact live)).1

-- §FS-host-boundary.lookup: The primary call consumes these actual accepted probe snapshots.
-- Stable trusted-parent flags are a separate per-operation authority producer.
theorem guarded_primary_recorded {step : RawStep} {interference : RawInterference}
    {origin : RawOrigin} {semantics : NameSemanticsView}
    (laws : LookupPrimitiveContract step interference semantics) {ordinal : Nat}
    {before after : World} {primary : Request} {events : List (Request × Option Reply)}
    (source : Prefix (guardedCall primary) events)
    (history : RawPrefixHistory step interference origin ordinal before events after)
    {event : Request × Option Reply} (selected : event ∈ events) (kind : NamespaceRequest event.1) :
    ∃ checks observed actual middle,
      CheckedParents (Lookup.parents primary) checks ∧ event = (primary, observed) ∧
      RawHistory step interference origin ordinal before checks actual ∧
      step actual primary observed middle ∧
      origin (ordinal + checks.length) primary observed actual middle ∧
      (∀ fd ∈ Lookup.parents primary, ∀ handle, before.handles fd = some handle →
        Nonempty (CheckedDirectory step origin semantics fd handle) ∧ actual.handles fd = some handle) := by
  obtain ⟨checks, observed, trailing, checked, shape, same, _, _⟩ := guarded_namespace_cut source selected kind
  rw [shape] at history
  obtain ⟨checkedWorld, checking, continuing⟩ := raw_prefix_split checks _ history
  obtain ⟨actual, middle, leading, operation, sampled⟩ := raw_prefix_operation_head continuing
  have initial : RawHistory step interference origin ordinal before checks actual := by
    simpa only [List.append_nil] using raw_history_append checking leading
  exact ⟨checks, observed, actual, middle, checked, same, initial, operation, sampled,
    checked_parents_recorded laws checked initial⟩

end LeanCage.Host.Kernel
