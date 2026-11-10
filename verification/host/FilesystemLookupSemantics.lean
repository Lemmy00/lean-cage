import FilesystemAccessProofs.Closing
import FilesystemContracts

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.lookup: Filesystem type is a lifetime fact; inode flags are live observations.
structure NameSemantics where
  magic : Nat
  inodeFlags : Nat

def NameSemantics.byteExact (value : NameSemantics) : Prop :=
  value.magic = Lookup.tmpMagic ∨
    value.magic = Lookup.extMagic ∧
      value.inodeFlags &&& (Lookup.casefoldFlag ||| Lookup.encryptionFlag) = 0

structure NameSemanticsView where
  filesystemType : ObjectId → Nat

def NameSemanticsView.at (view : NameSemanticsView) (world : World) (object : ObjectId) : NameSemantics :=
  ⟨view.filesystemType object, world.inodeFlags object⟩

def LookupProbe (request : Request) : Prop :=
  request.op = .filesystemType ∨ request.op = .inodeFlags

abbrev RawStep := World → Request → Option Reply → World → Prop
abbrev RawInterference := World → World → Prop
abbrev RawOrigin := Nat → Request → Option Reply → World → World → Prop

-- §AR-host-boundary.primitives: These laws concern individual raw probes and actual handles.
-- Input-directory flags may change between probes; these laws do not freeze them.
structure LookupPrimitiveContract (step : RawStep) (interference : RawInterference)
    (semantics : NameSemanticsView) : Prop where
  probe_frame : ∀ before after request observed,
    step before request observed after → LookupProbe request → after = before
  interference_handles : ∀ before after, interference before after → after.handles = before.handles
  filesystem_type : ∀ before after fd reply handle value,
    step before { op := .filesystemType, first := fd } (some reply) after →
    before.handles fd = some handle → Lookup.word? 8 reply = some value →
    value = semantics.filesystemType handle.object
  inode_flags : ∀ before after fd reply handle value,
    step before { op := .inodeFlags, first := fd } (some reply) after →
    before.handles fd = some handle → Lookup.word? 4 reply = some value →
    value = before.inodeFlags handle.object

-- §FS-host-boundary.acceptance: Probe transcripts retain individual worlds and interleaving.
inductive RawHistory (step : RawStep) (interference : RawInterference) (origin : RawOrigin) :
    Nat → World → List (Request × Reply) → World → Prop where
  | nil (ordinal : Nat) (world : World) : RawHistory step interference origin ordinal world [] world
  | call {ordinal : Nat} {before middle after : World} {request : Request} {reply : Reply}
      {events : List (Request × Reply)} (actual : step before request (some reply) middle)
      (sampled : origin ordinal request (some reply) before middle)
      (tail : RawHistory step interference origin (ordinal + 1) middle events after) :
      RawHistory step interference origin ordinal before ((request, reply) :: events) after
  | environment {ordinal : Nat} {before middle after : World} {events : List (Request × Reply)}
      (actual : interference before middle)
      (tail : RawHistory step interference origin ordinal middle events after) :
      RawHistory step interference origin ordinal before events after

theorem raw_history_head {step : RawStep} {interference : RawInterference} {origin : RawOrigin}
    {ordinal : Nat} {before after : World} {request : Request} {reply : Reply}
    {events : List (Request × Reply)}
    (history : RawHistory step interference origin ordinal before ((request, reply) :: events) after) :
    ∃ actual middle, RawHistory step interference origin ordinal before [] actual ∧
      step actual request (some reply) middle ∧ origin ordinal request (some reply) actual middle ∧
      RawHistory step interference origin (ordinal + 1) middle events after := by
  generalize shape : (request, reply) :: events = all at history
  induction history with
  | nil => cases shape
  | call actual sampled tail ih => cases shape; exact ⟨_, _, .nil _ _, actual, sampled, tail⟩
  | environment actual tail ih =>
    obtain ⟨before, middle, leading, operation, sampled, rest⟩ := ih shape
    exact ⟨before, middle, .environment actual leading, operation, sampled, rest⟩

theorem raw_history_append {step : RawStep} {interference : RawInterference} {origin : RawOrigin}
    {ordinal : Nat} {before middle after : World} {first last : List (Request × Reply)}
    (initial : RawHistory step interference origin ordinal before first middle)
    (final : RawHistory step interference origin (ordinal + first.length) middle last after) :
    RawHistory step interference origin ordinal before (first ++ last) after := by
  induction initial with
  | nil => exact final
  | call actual sampled tail ih =>
    apply RawHistory.call actual sampled
    apply ih
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using final
  | environment actual tail ih => exact .environment actual (ih final)

theorem raw_history_split {step : RawStep} {interference : RawInterference} {origin : RawOrigin}
    {ordinal : Nat} {before after : World} (first last : List (Request × Reply))
    (history : RawHistory step interference origin ordinal before (first ++ last) after) :
    ∃ middle, RawHistory step interference origin ordinal before first middle ∧
      RawHistory step interference origin (ordinal + first.length) middle last after := by
  induction first generalizing ordinal before with
  | nil => exact ⟨before, .nil _ _, history⟩
  | cons event rest ih =>
    obtain ⟨actual, between, leading, operation, sampled, tail⟩ := raw_history_head history
    obtain ⟨middle, firstHistory, lastHistory⟩ := ih tail
    refine ⟨middle, ?_, ?_⟩
    · exact raw_history_append leading (.call operation sampled firstHistory)
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lastHistory

theorem raw_probe_history_handles {step : RawStep} {interference : RawInterference}
    {origin : RawOrigin} {semantics : NameSemanticsView}
    (laws : LookupPrimitiveContract step interference semantics)
    {ordinal : Nat} {before after : World} {events : List (Request × Reply)}
    (history : RawHistory step interference origin ordinal before events after)
    (probes : ∀ event ∈ events, LookupProbe event.1) : after.handles = before.handles := by
  induction history with
  | nil => rfl
  | @call ordinal before middle after request reply events actual sampled tail ih =>
    have same := laws.probe_frame _ _ _ _ actual (probes (request, reply) (by simp))
    exact (ih (fun event member => probes event (by simp [member]))).trans (congrArg World.handles same)
  | environment actual tail ih => exact (ih probes).trans (laws.interference_handles _ _ actual)

-- §FS-host-boundary.lookup: A successful check exports observations of this same retained object.
structure ProbeSample (step : RawStep) (origin : RawOrigin) (op : Op) (fd : UInt64)
    (handle : Handle) (width value : Nat) where
  ordinal : Nat
  before : World
  after : World
  reply : Reply
  actual : step before { op, first := fd } (some reply) after
  sampled : origin ordinal { op, first := fd } (some reply) before after
  live : before.handles fd = some handle
  parsed : Lookup.word? width reply = some value

-- §FS-host-boundary.lookup: Approval refers to the actual last probe, not a future interval.
inductive CheckedDirectory (step : RawStep) (origin : RawOrigin)
    (semantics : NameSemanticsView) (fd : UInt64) (handle : Handle) where
  | temporary
      (magic : ProbeSample step origin .filesystemType fd handle 8 (semantics.filesystemType handle.object))
      (code : semantics.filesystemType handle.object = Lookup.tmpMagic)
  | ext
      (magic : ProbeSample step origin .filesystemType fd handle 8 (semantics.filesystemType handle.object))
      (value : Nat) (flags : ProbeSample step origin .inodeFlags fd handle 4 value)
      (code : semantics.filesystemType handle.object = Lookup.extMagic)
      (decoded : value = flags.before.inodeFlags handle.object)
      (allowed : value &&& (Lookup.casefoldFlag ||| Lookup.encryptionFlag) = 0)

def CheckedDirectory.observedAt {step : RawStep} {origin : RawOrigin}
    {semantics : NameSemanticsView} {fd : UInt64} {handle : Handle} :
    CheckedDirectory step origin semantics fd handle → World
  | .temporary magic _ => magic.before
  | .ext _ _ flags _ _ _ => flags.before

def CheckedDirectory.ordinal {step : RawStep} {origin : RawOrigin}
    {semantics : NameSemanticsView} {fd : UInt64} {handle : Handle} :
    CheckedDirectory step origin semantics fd handle → Nat
  | .temporary magic _ => magic.ordinal
  | .ext _ _ flags _ _ _ => flags.ordinal

structure BoundedCheckedDirectory (step : RawStep) (origin : RawOrigin) (semantics : NameSemanticsView)
    (fd : UInt64) (handle : Handle) (first limit : Nat) where
  checked : CheckedDirectory step origin semantics fd handle
  lower : first ≤ checked.ordinal
  upper : checked.ordinal < limit

theorem checked_directory_observed_exact {step : RawStep} {origin : RawOrigin}
    {semantics : NameSemanticsView} {fd : UInt64} {handle : Handle}
    (checked : CheckedDirectory step origin semantics fd handle) :
    (semantics.at checked.observedAt handle.object).byteExact := by
  cases checked with
  | temporary magic code => exact .inl code
  | ext magic value flags code decoded allowed =>
    refine .inr ⟨code, ?_⟩
    change flags.before.inodeFlags handle.object &&& (Lookup.casefoldFlag ||| Lookup.encryptionFlag) = 0
    rw [← decoded]
    exact allowed

theorem lookup_check_raw_sound_bounded {step : RawStep} {interference : RawInterference}
    {origin : RawOrigin} {semantics : NameSemanticsView}
    (laws : LookupPrimitiveContract step interference semantics) {ordinal : Nat}
    {before after : World} {events : List (Request × Reply)} {fd : UInt64} {handle : Handle}
    (source : Returns (Lookup.check fd) events true)
    (history : RawHistory step interference origin ordinal before events after)
    (live : before.handles fd = some handle) :
    Nonempty (BoundedCheckedDirectory step origin semantics fd handle ordinal (ordinal + events.length)) ∧
      after.handles fd = some handle := by
  have accepted := lookup_check_source source
  have probes : ∀ event ∈ events, LookupProbe event.1 := by
    rcases accepted with ⟨observed, rfl, _⟩ | ⟨observed, flags, rfl, _⟩
    · intro event member
      have same := List.mem_singleton.mp member
      subst event
      exact .inl rfl
    · intro event member
      rcases List.mem_cons.mp member with rfl | rest
      · exact .inl rfl
      · have same := List.mem_singleton.mp rest
        subst event
        exact .inr rfl
  have finalLive : after.handles fd = some handle := by
    rw [raw_probe_history_handles laws history probes]
    exact live
  refine ⟨?_, finalLive⟩
  rcases accepted with ⟨observed, shape, zero, width, value⟩ |
    ⟨observed, flags, shape, zero, width, value, allowed⟩
  · rw [shape] at history
    obtain ⟨actual, middle, leading, operation, sampled, rest⟩ := raw_history_head history
    have actualLive : actual.handles fd = some handle := by
      rw [raw_probe_history_handles laws leading (by intro event impossible; cases impossible)]
      exact live
    have parsed := (lookup_word_exact 8 observed Lookup.tmpMagic).mpr ⟨zero, width, value⟩
    have magic := laws.filesystem_type _ _ _ _ _ _ operation actualLive parsed
    refine ⟨⟨.temporary ⟨ordinal, actual, middle, observed, operation, sampled, actualLive, ?_⟩ magic.symm,
      Nat.le_refl _, ?_⟩⟩
    · simpa only [magic] using parsed
    · simp only [CheckedDirectory.ordinal, shape, List.length_singleton]
      omega
  · rw [shape] at history
    obtain ⟨actual, middle, leading, operation, sampled, rest⟩ := raw_history_head history
    have actualLive : actual.handles fd = some handle := by
      rw [raw_probe_history_handles laws leading (by intro event impossible; cases impossible)]
      exact live
    have parsed := (lookup_word_exact 8 observed Lookup.extMagic).mpr ⟨zero, width, value⟩
    have magic := laws.filesystem_type _ _ _ _ _ _ operation actualLive parsed
    obtain ⟨flagBefore, flagAfter, between, flagOperation, flagSampled, ending⟩ := raw_history_head rest
    have flagLive : flagBefore.handles fd = some handle := by
      rw [raw_probe_history_handles laws between (by intro event impossible; cases impossible),
        laws.probe_frame _ _ _ _ operation (.inl rfl)]
      exact actualLive
    obtain ⟨flagsValue, flagZero, flagWidth, flagValue, mask⟩ := (lookup_ext_exact flags).mp allowed
    have flagParsed := (lookup_word_exact 4 flags flagsValue).mpr ⟨flagZero, flagWidth, flagValue⟩
    have flagsExact := laws.inode_flags _ _ _ _ _ _ flagOperation flagLive flagParsed
    refine ⟨⟨.ext ⟨ordinal, actual, middle, observed, operation, sampled, actualLive, ?_⟩
      flagsValue ⟨ordinal + 1, flagBefore, flagAfter, flags, flagOperation, flagSampled, flagLive, flagParsed⟩
      magic.symm flagsExact mask, ?_, ?_⟩⟩
    · simpa only [magic] using parsed
    · change ordinal ≤ ordinal + 1
      omega
    · simp only [CheckedDirectory.ordinal, shape, List.length_cons, List.length_nil]
      omega

theorem lookup_check_raw_sound {step : RawStep} {interference : RawInterference}
    {origin : RawOrigin} {semantics : NameSemanticsView}
    (laws : LookupPrimitiveContract step interference semantics) {ordinal : Nat}
    {before after : World} {events : List (Request × Reply)} {fd : UInt64} {handle : Handle}
    (source : Returns (Lookup.check fd) events true)
    (history : RawHistory step interference origin ordinal before events after)
    (live : before.handles fd = some handle) :
    Nonempty (CheckedDirectory step origin semantics fd handle) ∧ after.handles fd = some handle := by
  obtain ⟨⟨bounded⟩, retained⟩ := lookup_check_raw_sound_bounded laws source history live
  exact ⟨⟨bounded.checked⟩, retained⟩

end LeanCage.Host.Kernel
