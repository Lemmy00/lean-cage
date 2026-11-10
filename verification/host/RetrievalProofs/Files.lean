import RetrievalProofs.Effects

namespace LeanCage.Host.Retrieval

open Filesystem

-- §FS-host-boundary.publication: Returned bytes come from this parent's acknowledged copy.
theorem readFile_source (root : UInt64) (name : ByteArray) (limit : Nat)
    {events : List (Request × Reply)} {bytes : ByteArray}
    (run : Returns (readFile root name limit) events (.ok bytes)) :
    bytes.size ≤ limit ∧ ∃ copied,
      Snapshot.OpenedCopy root name events copied ∧ copied.bytes = bytes := by
  unfold readFile at run
  obtain ⟨copies, result, last, copiedRun, final, shape⟩ := Snapshot.returns_bind_split _ _ run
  cases result with
  | error => cases final
  | ok copied =>
    obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
    cases same
    simp only [List.append_nil] at shape
    subst events
    obtain ⟨bounded, source⟩ := Snapshot.copyAt_provenance _ _ _ copiedRun
    exact ⟨bounded, copied, source, rfl⟩

def OptionalCopy (root : UInt64) (name : ByteArray) (limit : Nat) (present : Bool)
    (events : List (Request × Reply)) (bytes : Option ByteArray) : Prop :=
  if present then ∃ raw copied, bytes = some raw ∧ copied.bytes = raw ∧ raw.size ≤ limit ∧
    Snapshot.OpenedCopy root name events copied
  else bytes = none ∧ events = []

theorem optionalFile_source (root : UInt64) (name : ByteArray) (limit : Nat) (present : Bool)
    {events : List (Request × Reply)} {bytes : Option ByteArray}
    (run : Returns (optionalFile root name limit present) events (.ok bytes)) :
    OptionalCopy root name limit present events bytes := by
  unfold optionalFile at run
  split at run
  · rename_i presence
    obtain ⟨copies, result, last, copiedRun, final, shape⟩ := Snapshot.returns_bind_split _ _ run
    cases result with
    | error => cases final
    | ok raw =>
      obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
      cases same
      simp only [List.append_nil] at shape
      subst events
      obtain ⟨bounded, copied, source, equal⟩ := readFile_source _ _ _ copiedRun
      simp only [OptionalCopy, presence, ↓reduceIte]
      exact ⟨raw, copied, rfl, equal, bounded, source⟩
  · obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq run
    cases same
    simp only [OptionalCopy, ‹¬present = true›]
    exact ⟨True.intro, True.intro⟩

theorem readMarker_source (target : UInt64) {events : List (Request × Reply)} {marker : ByteArray}
    (run : Returns (readMarker target) events (.ok marker)) :
    ∃ reply, events = [({
      op := .getAttribute
      first := target
      second := 40
      left := Publication.attributeName }, reply)] ∧ reply.1.toNat = 40 ∧ reply.2 = marker ∧ marker.size = 40 := by
  unfold readMarker at run
  obtain ⟨reply, last, shape, final⟩ := Snapshot.returns_call_split run
  dsimp only [Filesystem.Program.bind] at final
  split at final
  · cases final
  · rename_i checked
    obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
    cases same
    have markerSize : Publication.markerMagic.size + 32 = 40 := by decide
    have fields : reply.1.toNat = 40 ∧ reply.2.size = 40 := by
      simpa only [Bool.or_eq_true, bne_iff_ne, not_or, Classical.not_not, markerSize] using checked
    exact ⟨reply, shape, fields.1, rfl, fields.2⟩

-- §FS-host-boundary.publication: Human JSON is copied and checked against the same typed object.
theorem resultJson_source (root : UInt64) (metadata : GatewayWire.Value)
    {events : List (Request × Reply)}
    (run : Returns (resultJson root metadata) events (.ok ())) :
    ∃ expected copied, WireJson.render GatewayWire.valueDepthMax metadata = .ok expected ∧
      copied.bytes = expected ++ "\n".toUTF8 ∧ copied.bytes.size ≤ Publication.metadataMax ∧
      Snapshot.OpenedCopy root "result.json".toUTF8 events copied := by
  unfold resultJson at run
  split at run
  · cases run
  · rename_i expected rendered
    split at run
    · cases run
    · obtain ⟨copies, result, last, copiedRun, final, shape⟩ := Snapshot.returns_bind_split _ _ run
      cases result with
      | error => cases final
      | ok actual =>
        simp only [Except.bind] at final
        split at final
        · rename_i same
          obtain ⟨rfl, _⟩ := Snapshot.returns_pure_eq final
          simp only [List.append_nil] at shape
          subst events
          obtain ⟨bounded, copied, source, copiedBytes⟩ := readFile_source _ _ _ copiedRun
          have equal : actual = expected ++ "\n".toUTF8 := by simpa only [beq_iff_eq] using same
          exact ⟨expected, copied, rendered, copiedBytes.trans equal,
            by simpa only [copiedBytes] using bounded, source⟩
        · cases final

end LeanCage.Host.Retrieval
